#include "tron.hpp"

#include <algorithm>
#include <array>
#include <cmath>
#include <cstdint>
#include <vector>

namespace {

constexpr int side = tron::MAXW + 2;
constexpr int cells = side * side;
constexpr int inf = 30000;
constexpr int victory = 20000;

struct Board {
    int step[4], size, seats, me, turn;
    bool open[cells]{};
    std::array<int, tron::MAXN> heads{};

    explicit Board(const tron::State& s)
        : size((s.W + 2) * (s.H + 2)), seats(s.N), me(s.me), turn(s.turn) {
        const int stride = s.W + 2;
        step[0] = -stride;
        step[1] = 1;
        step[2] = stride;
        step[3] = -1;
        for (int y = 0; y < s.H; ++y)
            for (int x = 0; x < s.W; ++x)
                open[(y + 1) * stride + x + 1] = s.cell[y][x] == tron::EMPTY;
        for (int k = 0; k < seats; ++k)
            if (s.alive[k]) heads[k] = (s.y[k] + 1) * stride + s.x[k] + 1;
    }

    int degree(int p) const {
        return open[p + step[0]] + open[p + step[1]] + open[p + step[2]] + open[p + step[3]];
    }
    int priority(int k, int time) const {
        return (k + seats - time % seats) % seats;
    }
};

using Distances = std::array<short, cells>;

void distances(const Board& b, const int* sources, int n, Distances& ds) {
    std::fill_n(ds.begin(), b.size, short(inf));
    short queue[cells];
    int tail = 0;
    for (int i = 0; i < n; ++i) {
        int p = sources[i];
        if (p) {
            ds[p] = 0;
            queue[tail++] = short(p);
        }
    }
    for (int front = 0; front < tail; ++front) {
        const int p = queue[front];
        const short next = short(ds[p] + 1);
        for (int d : b.step) {
            const int q = p + d;
            if (b.open[q] && ds[q] == inf) {
                ds[q] = next;
                queue[tail++] = short(q);
            }
        }
    }
}

void rivals(const Board& b, int who, Distances& ds) {
    auto sources = b.heads;
    sources[who] = 0;
    distances(b, sources.data(), b.seats, ds);
}

// Removing a cut vertex makes its branches mutually exclusive for a simple path.
// On the block-cut tree a trail can use one chain of blocks from its starting head.
struct Chambers {
    const Board& b;
    const Distances& us;
    const Distances& them;
    short seen[cells], low[cells], stack[cells];
    int branch[cells];
    int top = 0, number = 0, area = 0, start = 0;
    bool alone;

    Chambers(const Board& board, const Distances& mine, const Distances& others, bool isolated)
        : b(board), us(mine), them(others), alone(isolated) {
        std::fill_n(seen, b.size, short(0));
    }

    int weight(int p) const {
        if (alone || us[p] < them[p]) return 4;
        return 2;
    }

    void visit(int p, int parent) {
        seen[p] = low[p] = short(++number);
        stack[top++] = short(p);
        branch[p] = 0;
        for (int d : b.step) {
            const int q = p + d;
            if (q == parent || (!b.open[q] && q != start) || (!alone && us[q] > them[q])) continue;
            if (seen[q]) {
                low[p] = std::min(low[p], seen[q]);
                continue;
            }
            visit(q, p);
            low[p] = std::min(low[p], low[q]);
            if (low[q] < seen[p]) continue;
            int colors[2]{}, tail = 0, v;
            do {
                v = stack[--top];
                colors[v & 1] += weight(v);
                tail = std::max(tail, branch[v]);
            } while (v != q);
            area += colors[0] + colors[1];
            // Every grid path alternates colors. One extra square can be an endpoint.
            int room = std::min(colors[0] + colors[1], 2 * std::min(colors[0], colors[1]) + 4);
            branch[p] = std::max(branch[p], room + tail);
        }
    }

    int value(int root) {
        start = root;
        visit(root, 0);
        return branch[root];
    }
};

int passage(const Board& b, const Distances& ds, int p) {
    int answer = inf;
    for (int d : b.step)
        if (b.open[p+d]) answer = std::min(answer, int(ds[p+d]) + 1);
    return answer;
}

struct DuelField {
    const Board& board;
    int nextTime, opponent;
    signed char owner[cells]{}, weight[cells]{};
    short distance[cells], queue[cells], order[cells]{}, low[cells], stack[cells];
    short continuation[cells];
    int top = 0, serial = 0;
    int total[2]{}, links[2]{}, oneWay[2]{};
    bool joined = false;

    DuelField(const Board& b, int a, int e, int other, int time)
        : board(b), nextTime(time), opponent(other) {
        std::fill_n(distance, b.size, short(inf));
        queue[0] = short(a);
        queue[1] = short(e);
        distance[a] = distance[e] = 0;
        owner[e] = 1;
        int count = 2, start = 0;
        unsigned char tieWinner[tron::MAXN];
        for (int i = 0; i < b.seats; ++i)
            tieWinner[i] = b.priority(b.me, i) > b.priority(other, i);
        int priorityTurn = time % b.seats;
        while (start < count) {
            const int end = count;
            for (; start < end; ++start) {
                int p = queue[start], k = owner[p], depth = distance[p] + 1;
                for (int d : b.step) {
                    int q = p + d;
                    if (!b.open[q]) continue;
                    if (distance[q] == inf) {
                        distance[q] = short(depth);
                        owner[q] = (signed char)k;
                        weight[q] = 4;
                        queue[count++] = short(q);
                    } else if (owner[q] != k) {
                        joined = true;
                        if (distance[q] == depth) {
                            owner[q] = (signed char)tieWinner[priorityTurn];
                            weight[q] = 3;
                        }
                    }
                }
            }
            priorityTurn = (priorityTurn + 1) % b.seats;
        }
    }

    void cut(int p, int parent, int k, int root) {
        order[p] = low[p] = short(++serial);
        continuation[p] = 0;
        stack[top++] = short(p);
        int degree = 0;
        for (int d : board.step) {
            const int q = p + d;
            if ((!board.open[q] && q != root) || owner[q] != k) continue;
            ++degree;
            if (q == parent) continue;
            if (order[q]) {
                low[p] = std::min(low[p], order[q]);
                continue;
            }
            cut(q, p, k, root);
            low[p] = std::min(low[p], low[q]);
            if (low[q] < order[p]) continue;
            int colors[2]{}, extension = 0, v;
            do {
                v = stack[--top];
                colors[v&1] += weight[v];
                extension = std::max(extension, int(continuation[v]));
            } while (v != q);
            int area = colors[0]+colors[1];
            total[k] += area;
            int cap = std::min(area, 2 * std::min(colors[0],colors[1]) + 4);
            continuation[p] = short(std::max(int(continuation[p]), cap+extension));
        }
        links[k] += degree;
        oneWay[k] += degree == 1;
    }

    int score(int a, int e) {
        cut(a, 0, 0, a);
        cut(e, 0, 1, e);
        int strength[2];
        for (int k = 0; k < 2; ++k) {
            const int root = k == 0 ? a : e;
            strength[k] = 9*continuation[root] + 2*total[k] + links[k] - 4*oneWay[k];
        }
        int edge = strength[0]-strength[1];
        int denominator = 160 + (strength[0]+strength[1])/5;
        int score = 520*edge / denominator;
        if (!joined) {
            score += 25;
            if (score > 35) score += 270;
            if (score < -35) score -= 270;
        }
        return score + 3*(board.degree(a)-board.degree(e));
    }
};

std::uint64_t scramble(std::uint64_t x) {
    x ^= x >> 30; x *= 0xbf58476d1ce4e5b9ULL;
    x ^= x >> 27; x *= 0x94d049bb133111ebULL;
    return x ^ (x >> 31);
}

struct CachedRace {
    std::uint64_t key;
    short value;
    signed char depth, flag, own, enemy;
};

struct CachedField {
    std::uint64_t key;
    short value;
    bool split;
};

struct Race {
    Board& b;
    int other, work = 0, nodes = 0, limit;
    bool stopped = false;
    static constexpr int cacheMask = 65535;
    inline static std::array<CachedRace, cacheMask+1> games{};
    inline static std::array<CachedField, cacheMask+1> fields{};
    inline static std::uint64_t occupy[cells], selfHead[cells], enemyHead[cells];
    inline static bool initialized = false;
    std::uint64_t base = 0;
    int answer = 0;

    Race(Board& board, int opponent) : b(board), other(opponent) {
        if (!initialized) {
            for (int i = 0; i < cells; ++i) {
                occupy[i] = scramble(1+i);
                selfHead[i] = scramble(4096+i);
                enemyHead[i] = scramble(8192+i);
            }
            initialized = true;
        }
        for (int p = 0; p < b.size; ++p) if (!b.open[p]) base ^= occupy[p];
        base ^= scramble(16384 + 512*b.seats + 16*b.me + other);
        limit = b.turn == 0 ? 36000 : 4800;
    }

    int estimated(int a, int e, int time, std::uint64_t key) {
        auto& cached = fields[key & cacheMask];
        if (cached.key == key) return cached.value;
        DuelField board(b, a, e, other, time);
        int value = board.score(a,e);
        cached = {key, short(value), !board.joined};
        if (++work >= limit) stopped = true;
        return value;
    }

    void order(int p, int target, int hint, int result[4]) const {
        int value[4];
        const int stride = b.step[2];
        for (int d=0; d<4; ++d) {
            result[d]=d;
            int q=p+b.step[d];
            if (!b.open[q]) value[d] = -1000;
            else {
                int gap=std::abs(q/stride-target/stride)+std::abs(q%stride-target%stride);
                value[d] = (d==hint ? 200 : 0) - 3*gap + std::min(2,b.degree(q));
            }
        }
        for(int i=1;i<4;++i)
            for(int j=i;j>0 && value[result[j]]>value[result[j-1]];--j)
                std::swap(result[j],result[j-1]);
    }

    int search(int a, int e, int time, int depth, int alpha, int beta, std::uint64_t occupied, bool root) {
        if ((++nodes & 63) == 0 && tron::budget_left() < 12) {
            stopped = true;
            return 0;
        }
        int na=b.degree(a), ne=b.degree(e);
        if (!na || !ne) return na==ne ? 0 : na ? victory-time : time-victory;
        std::uint64_t key=occupied^selfHead[a]^enemyHead[e]^scramble(24000+time);
        if (!depth) return estimated(a,e,time,key);
        auto& previous=games[key&cacheMask];
        int hintA=-1, hintE=-1;
        if(previous.key==key) {
            hintA=previous.own; hintE=previous.enemy;
            if(previous.depth>=depth) {
                int saved=previous.value;
                if(previous.flag==0 || (previous.flag==1 && saved>=beta) || (previous.flag==-1 && saved<=alpha)) {
                    if(root) answer=hintA;
                    return saved;
                }
            }
        }
        auto& leaf=fields[key&cacheMask];
        if(!root && leaf.key==key && leaf.split) return leaf.value;
        int first[4], second[4]; order(a,e,hintA,first); order(e,a,hintE,second);
        int best=-victory-1,bestA=first[0],bestE=second[0];
        const int initialAlpha=alpha;
        for(int da:first) {
            const int x=a+b.step[da];
            if(!b.open[x]) continue;
            int worst=victory+1, reply=second[0];
            for(int de:second) {
                const int y=e+b.step[de];
                if(!b.open[y]) continue;
                int outcome;
                if(x==y) outcome=b.priority(b.me,time)<b.priority(other,time) ? victory-time : time-victory;
                else {
                    b.open[x]=b.open[y]=false;
                    outcome=search(x,y,time+1,depth-1,std::max(alpha,best),std::min(beta,worst),occupied^occupy[x]^occupy[y],false);
                    b.open[x]=b.open[y]=true;
                    if(stopped) return 0;
                }
                if(outcome<worst) { worst=outcome; reply=de; }
                if(worst<=std::max(alpha,best)) break;
            }
            if(worst>best) {
                best=worst; bestA=da; bestE=reply;
                if(best>=beta) break;
            }
        }
        signed char flag = best<=initialAlpha ? -1 : best>=beta ? 1 : 0;
        previous={key,short(best),(signed char)depth,flag,(signed char)bestA,(signed char)bestE};
        if(root) answer=bestA;
        return best;
    }

    int move() {
        int choice=0;
        for(int depth=1; depth<=13; ++depth) {
            int value=search(b.heads[b.me],b.heads[other],b.turn,depth,-victory-1,victory+1,base,true);
            if(stopped) break;
            choice=answer;
            if(std::abs(value)>victory-2000 || tron::budget_left()<17) break;
        }
        return choice;
    }
};

constexpr int forecastSteps = 6;
using Heads = std::array<int, tron::MAXN>;
using Directions = std::array<int, tron::MAXN>;
using Preferences = std::array<std::array<int, 4>, tron::MAXN>;

struct Territory {
    const Board& b;
    short tick[cells], queue[cells], disc[cells], low[cells], stack[cells], downstream[cells];
    signed char owner[cells], mass[cells];
    int length[tron::MAXN]{}, reach[tron::MAXN]{}, fringe[tron::MAXN]{};
    int serial=0, top=0;

    explicit Territory(const Board& board) : b(board) {
        std::fill_n(tick,b.size,short(-1));
        std::fill_n(disc,b.size,short(0));
        int head=0, tail=0;
        for(int k=0;k<b.seats;++k) if(b.heads[k]) {
            int p=b.heads[k];
            queue[tail++]=short(p); tick[p]=0; owner[p]=(signed char)k; mass[p]=0;
        }
        int priority=b.turn%b.seats;
        for(int depth=1;head<tail;++depth) {
            int end=tail;
            for(;head<end;++head) {
                const int p=queue[head], k=owner[p];
                for(int offset:b.step) {
                    const int q=p+offset;
                    if(!b.open[q]) continue;
                    if(tick[q]<0) {
                        queue[tail++]=short(q); tick[q]=short(depth);
                        owner[q]=(signed char)k; mass[q]=4;
                    } else if(tick[q]==depth && k!=owner[q]) {
                        int incumbent=owner[q];
                        int ourPriority=k>=priority?k-priority:k+b.seats-priority;
                        int theirPriority=incumbent>=priority?incumbent-priority:incumbent+b.seats-priority;
                        if(ourPriority<theirPriority) owner[q]=(signed char)k;
                        mass[q]=3;
                    }
                }
            }
            if(++priority==b.seats) priority=0;
        }
        for(int k=0;k<b.seats;++k) if(b.heads[k]) {
            visit(b.heads[k],0,k);
            length[k]=downstream[b.heads[k]];
        }
    }

    void visit(int p,int parent,int k) {
        disc[p]=low[p]=short(++serial);
        stack[top++]=short(p); downstream[p]=0;
        int ownNeighbors=0;
        for(int offset:b.step) {
            int q=p+offset;
            if(!b.open[q] && q!=b.heads[k]) continue;
            if(owner[q]!=k) continue;
            ++ownNeighbors;
            if(q==parent) continue;
            if(disc[q]) { low[p]=std::min(low[p],disc[q]); continue; }
            visit(q,p,k);
            low[p]=std::min(low[p],low[q]);
            if(low[q]<disc[p]) continue;
            int colors[2]{},extension=0,v;
            do {
                v=stack[--top];
                colors[v&1]+=mass[v];
                extension=std::max(extension,int(downstream[v]));
            } while(v!=q);
            const int area=colors[0]+colors[1];
            reach[k]+=area;
            const int space=std::min(area,2*std::min(colors[0],colors[1])+4);
            downstream[p]=short(std::max(int(downstream[p]),space+extension));
        }
        fringe[k]+=ownNeighbors<=1;
    }

    int lifespan(int k) const {
        if(!b.heads[k]) return 0;
        return (8*length[k]+2*reach[k])/40 - fringe[k]/5;
    }

    int score(int rival) const {
        int me=b.me;
        const int ours=lifespan(me);
        int points=0;
        for(int k=0;k<b.seats;++k) if(k!=me) {
            if(!b.heads[k]) {points+=200;continue;}
            int theirs=lifespan(k);
            int gap=ours-theirs;
            points+=100+100*gap/(std::abs(gap)+12+(ours+theirs)/8);
        }
        return 3*std::min(ours,400)+(8*points)/(b.seats-1)
               -std::min(lifespan(rival),250)/2+2*b.degree(b.heads[me]);
    }
};

struct Crowd {
    Board& b;
    int rival=-1, gap=inf, maxDepth=0, work=0, ceiling, answer=0;
    bool stopped=false;
    Preferences prediction[forecastSteps]{};

    explicit Crowd(Board& board) : b(board), ceiling(board.seats>4?400:900) {
        int self=b.heads[b.me];
        Distances walk;
        distances(b,&self,1,walk);
        for(int k=0;k<b.seats;++k) if(k!=b.me && b.heads[k]) {
            int distance=passage(b,walk,b.heads[k]);
            if(distance<gap) {gap=distance;rival=k;}
        }
        if(b.turn==0) ceiling*=4;
    }

    Preferences forecasts() const {
        Preferences order{};
        for(int k=0;k<b.seats;++k) {
            int p=b.heads[k];
            for(int d=0;d<4;++d) order[k][d]=d;
            if(!p) continue;
            Distances enemy, ours; rivals(b,k,enemy);
            int value[4];
            for(int d=0;d<4;++d) {
                int q=p+b.step[d];
                if(!b.open[q]) {value[d]=-100000; continue;}
                distances(b,&q,1,ours);
                int score=0;
                for(int j=0;j<b.size;++j) if(ours[j]<inf) {
                    if(ours[j]+1<enemy[j]) score+=4;
                    else if(ours[j]<=enemy[j]) score+=2;
                }
                score+=3*b.degree(q);
                if(!b.degree(q)) score-=120;
                if(enemy[q]==1)
                    for(int i=0;i<b.seats;++i)
                        if(i!=k && b.heads[i] && b.priority(i,b.turn)<b.priority(k,b.turn))
                            for(int off:b.step) if(b.heads[i]+off==q) score-=350;
                value[d]=score;
            }
            for(int i=1;i<4;++i)
                for(int j=i;j>0 && value[order[k][j]]>value[order[k][j-1]];--j)
                    std::swap(order[k][j],order[k][j-1]);
        }
        return order;
    }

    Directions probable(const Preferences& order) const {
        Directions result{};
        for(int k=0;k<b.seats;++k) if(b.heads[k])
            for(int d:order[k]) if(b.open[b.heads[k]+b.step[d]]) {result[k]=d;break;}
        return result;
    }

    Heads advance(const Directions& plan) {
        Heads next{};
        int i=b.turn%b.seats;
        for(int n=0;n<b.seats;++n) {
            if(b.heads[i]) {
                int q=b.heads[i]+b.step[plan[i]];
                if(b.open[q]) {b.open[q]=false;next[i]=q;}
            }
            if(++i==b.seats) i=0;
        }
        return next;
    }

    void undo(const Heads& next) {
        for(int p:next) if(p) b.open[p]=true;
    }

    int estimate() {
        ++work;
        if(work>=ceiling || ((work&7)==0 && tron::budget_left()<12)) stopped=true;
        return Territory(b).score(rival);
    }

    int search(int ply,int alpha,int beta) {
        int me=b.me,p=b.heads[me];
        if(!p || !b.degree(p)) return -8000+100*ply;
        if(ply==maxDepth) return estimate();
        const Heads before=b.heads;
        const Preferences& order=prediction[ply];
        Directions directions=probable(order);
        const int enemy=b.heads[rival], enemyDegree=enemy?b.degree(enemy):0;
        int best=-20000;
        for(int da:order[me]) {
            int q=p+b.step[da];
            if(!b.open[q]) continue;
            int danger=0;
            for(int k=0;k<b.seats;++k) if(k!=me && k!=rival && before[k]
                        && b.priority(k,b.turn)<b.priority(me,b.turn)) {
                for(int off:b.step) if(before[k]+off==q) danger=ply==0?5000:(ply==1?550:70);
            }
            directions[me]=da;
            int worst=10000;
            for(int de:order[rival]) {
                if(enemyDegree && !b.open[enemy+b.step[de]]) continue;
                directions[rival]=de;
                Heads after=advance(directions);
                b.heads=after; ++b.turn;
                int score;
                if(!after[me]) score=-8500+100*ply;
                else {
                    int alive=0;
                    for(int z:after) alive+=z!=0;
                    score=alive==1?8000-ply:search(ply+1,std::max(alpha,best)+danger,std::min(beta,worst)+danger);
                }
                --b.turn; b.heads=before; undo(after);
                if(stopped) return 0;
                score-=danger;
                worst=std::min(worst,score);
                if(!enemyDegree || worst<=std::max(alpha,best)) break;
                if(gap>12 && ply>0) break;
            }
            if(worst>best) {best=worst;if(!ply) answer=da;}
            if(best>=beta) break;
        }
        return best;
    }

    int move() {
        Heads saved[forecastSteps+1]; saved[0]=b.heads;
        for(int i=0;i<forecastSteps;++i) {
            prediction[i]=forecasts();
            saved[i+1]=advance(probable(prediction[i]));b.heads=saved[i+1];++b.turn;
        }
        for(int i=forecastSteps;i>0;--i) {undo(saved[i]);--b.turn;}
        b.heads=saved[0];
        int chosen=prediction[0][b.me][0];
        if(rival<0) return chosen;
        for(maxDepth=1;maxDepth<=forecastSteps;++maxDepth) {
            search(0,-20000,20000);
            if(stopped) break;
            chosen=answer;
            if(tron::budget_left()<16) break;
        }
        return chosen;
    }
};

struct PathPlanner {
    Board& b;
    const int start;
    std::uint32_t rng;
    std::vector<int> path, best;
    short index[cells];
    int bound = 0;

    PathPlanner(Board& board, const std::vector<int>& previous, int upper)
        : b(board), start(b.heads[b.me]), rng(0x7a8541b3u + 1031u * start + 29023u * b.turn), bound(upper) {
        auto it = std::find(previous.begin(), previous.end(), start);
        if (it != previous.end()) {
            best.push_back(start);
            for (++it; it != previous.end() && b.open[*it]; ++it) best.push_back(*it);
        } else best.push_back(start);
        path.reserve(b.size);
        best.reserve(b.size);
    }

    unsigned random() {
        rng ^= rng << 13;
        rng ^= rng >> 17;
        rng ^= rng << 5;
        return rng;
    }

    void reset(bool reuse) {
        std::fill_n(index, b.size, short(-1));
        path.assign(1, start);
        if (reuse && best.size() > 5) {
            int keep = 1 + random() % best.size();
            path.assign(best.begin(), best.begin() + keep);
        }
        for (int i = 0; i < int(path.size()); ++i) index[path[i]] = short(i);
    }

    bool unused(int p) const { return b.open[p] && index[p] < 0; }

    bool extend() {
        int choice = 0, maxScore = -100000;
        for (int d : b.step) {
            const int q = path.back() + d;
            if (!unused(q)) continue;
            int degree = 0, exits = 0;
            for (int off : b.step) {
                if (unused(q + off)) ++degree;
                else if (index[q+off] >= 0) ++exits;
            }
            // Low-degree cells along the boundary are easier to strand on a later pass.
            int score = (degree ? -degree * 13 : -70 + exits * 3) + int(random() % 20);
            if (score > maxScore) maxScore = score, choice = q;
        }
        if (!choice) return false;
        index[choice] = short(path.size());
        path.push_back(choice);
        return true;
    }

    bool rotateEnd() {
        int pivot = -1, high = -1, last = int(path.size())-1;
        for (int off : b.step) {
            int pos = index[path.back() + off];
            if (pos < 0 || pos >= last - 1) continue;
            int q = path[pos + 1], free = 0;
            for (int d : b.step) free += unused(q + d);
            int merit = int(random() % 10) + (free ? 30 : 0);
            if (merit > high) high = merit, pivot = pos;
        }
        if (pivot < 0) return false;
        std::reverse(path.begin()+pivot+1, path.end());
        for (int i = pivot+1; i <= last; ++i) index[path[i]] = short(i);
        return true;
    }

    bool insertPair() {
        for (int i = 1; i < int(path.size()); ++i) {
            int a = path[i-1], c = path[i];
            int dir = std::abs(a-c) == 1 ? b.step[2] : 1;
            for (int off : {dir, -dir}) {
                if (!unused(a+off) || !unused(c+off)) continue;
                path.insert(path.begin()+i, {a+off,c+off});
                for (int j = i; j < int(path.size()); ++j) index[path[j]] = short(j);
                return true;
            }
        }
        return false;
    }

    int move(std::vector<int>& previous) {
        for (int attempt = 0; attempt < 45 && int(best.size()) <= bound; ++attempt) {
            if (attempt && tron::budget_left() < 12) break;
            reset(attempt % 4 != 0);
            int stale = 0, steps = 0;
            while (stale < 35 && steps++ < 1300) {
                if ((steps & 63) == 0 && tron::budget_left() < 12) break;
                while (extend()) {}
                if (path.size() > best.size()) {
                    best = path;
                    if (int(best.size()) > bound) break;
                }
                if (stale % 5 == 0 && insertPair()) { stale = 0; continue; }
                if (!rotateEnd()) break;
                ++stale;
            }
        }
        previous = best;
        if (best.size() >= 2)
            for (int d = 0; d < 4; ++d) if (start + b.step[d] == best[1]) return d;
        for (int d = 0; d < 4; ++d) if (b.open[start+b.step[d]]) return d;
        return 0;
    }
};

}  // namespace

int decide(const tron::State& s) {
    static std::vector<int> route;
    if (s.turn == 0) route.clear();
    Board board(s);
    const int head = board.heads[s.me];
    if (board.degree(head) <= 1) {
        for (int d = 0; d < 4; ++d) if (board.open[head + board.step[d]]) return d;
        return s.last_dir[s.me];
    }
    Distances reachable, empty;
    distances(board, &head, 1, reachable);
    int opponent = -1, count = 0;
    for (int k = 0; k < s.N; ++k) {
        if (k == s.me || !board.heads[k]) continue;
        if (passage(board, reachable, board.heads[k]) < inf) {
            ++count;
            opponent = k;
        }
    }
    if (!count) {
        Chambers room(board, reachable, empty, true);
        int upper = room.value(head) / 4;
        return PathPlanner(board, route, upper).move(route);
    }
    route.clear();
    if (count == 1 && tron::alive_count(s) == 2) return Race(board, opponent).move();
    return Crowd(board).move();
}
