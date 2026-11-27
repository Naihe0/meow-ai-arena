// Cutline / 折线. Adapted from the MIT-licensed tournament programs
// tron/sparring/sparring_hard.cpp and tron/bots/reference/gpt-6-astra-ultra-fast.cpp.
// Copyright (c) 2026 Naihe0 and meow-ai-arena contributors.
/*
MIT License

Copyright (c) 2026 meow-ai-arena contributors

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
*/
#include "tron.hpp"
#include <algorithm>
#include <array>
#include <bit>
#include <cmath>
#include <cstdint>
#include <cstring>
#include <vector>

namespace tactics {
constexpr int MAXP = 43 * 43;
constexpr int INF = 1 << 30;
constexpr int WIN = 1 << 26;

long long work = 0;
long long check_at = 0;
double margin = 8;
int W, H, PW, N, ME;
int DV[4];
uint8_t blk[MAXP];      // 1 = 不能走：界外、障碍、任何轨迹（含头部）
uint8_t col[MAXP];      // 棋盘格颜色 (x + y) & 1
int head[tron::MAXN];
bool alv[tron::MAXN];

inline int prio(int k, int turn) { return ((k - turn) % N + N) % N; }

// ---------------------------------------------------------------- Voronoi
uint32_t vstamp = 0;
uint32_t seen[MAXP];
int lay[MAXP];
int8_t own[MAXP];
uint16_t msk[MAXP];
int qa[MAXP], qb[MAXP];
int vid[tron::MAXN], vturn;    // 各源的玩家编号、BFS 第 0 层对应的回合（同时到达时按优先级判给谁）

struct Vor {
    int cnt[tron::MAXN];
    int edges[tron::MAXN];
    int par[tron::MAXN][2];     // 各人地盘里两种颜色的格数
    uint16_t conn;              // 与我（src 0）相遇过的人（位）
    int meet[tron::MAXN];       // 与我第一次相遇的层数
};

// srcs[0] 是"我"，vid[] 是各源的编号。同时出发的 BFS：严格先到的格子归他；
// 同时到的格子按到达那一回合的抢格优先级记给优先者，但不再向外扩。
void voronoi(const int* srcs, int ns, Vor& v) {
    if (++vstamp == 0) {
        std::memset(seen, 0, sizeof seen);
        vstamp = 1;
    }
    for (int i = 0; i < ns; ++i) {
        v.cnt[i] = v.edges[i] = v.par[i][0] = v.par[i][1] = 0;
        v.meet[i] = INF;
    }
    v.conn = 0;
    int* cur = qa;
    int* nxt = qb;
    int nc = 0;
    for (int i = 0; i < ns; ++i) {
        const int p = srcs[i];
        cur[nc++] = p;
        own[p] = int8_t(i);
        seen[p] = vstamp;
        lay[p] = -1;
        msk[p] = uint16_t(1u << i);
    }
    for (int L = 0; nc; ++L) {
        int nn = 0;
        for (int i = 0; i < nc; ++i) {
            const int p = cur[i];
            const int o = own[p];
            const uint16_t ob = uint16_t(1u << o);
            for (int d = 0; d < 4; ++d) {
                const int t = p + DV[d];
                if (blk[t]) continue;
                if (seen[t] != vstamp) {
                    seen[t] = vstamp;
                    lay[t] = L;
                    own[t] = int8_t(o);
                    msk[t] = ob;
                    nxt[nn++] = t;
                } else if (!(msk[t] & ob)) {
                    const uint16_t m = msk[t];
                    if (o == 0) {
                        v.conn |= m;
                        for (int j = 1; j < ns; ++j)
                            if ((m >> j & 1) && v.meet[j] == INF) v.meet[j] = L;
                    } else if (m & 1) {
                        v.conn |= ob;
                        if (v.meet[o] == INF) v.meet[o] = L;
                    }
                    if (lay[t] == L) {
                        msk[t] |= ob;
                        own[t] = -1;
                    }
                }
            }
        }
        int k = 0;
        for (int i = 0; i < nn; ++i) {
            const int t = nxt[i];
            const int o = own[t];
            if (o < 0) {
                int w = -1;
                for (int j = 0; j < ns; ++j)
                    if ((msk[t] >> j & 1) && (w < 0 || prio(vid[j], vturn + L) < prio(vid[w], vturn + L))) w = j;
                ++v.cnt[w];
                ++v.par[w][col[t]];
                continue;
            }
            ++v.cnt[o];
            ++v.par[o][col[t]];
            int e = 0;
            for (int d = 0; d < 4; ++d) e += !blk[t + DV[d]];
            v.edges[o] += e;
            nxt[k++] = t;
        }
        nc = k;
        work += nn;
        int* tmp = cur;
        cur = nxt;
        nxt = tmp;
    }
}

// 地盘里"真正走得到"的格数（关节点估计）：在 voronoi 之后调用，只走 own == i 的格子。
// 从头部出发做 Tarjan：子树被关节点隔开时，走进去就回不来，只能选一个这样的死胡同走到底；
// 其余的（能绕回来的）都能走到。返回 可回来的格数 + 最好的一条死胡同。
uint32_t cst[MAXP], cstamp = 0;
int dfn[MAXP], lowv[MAXP], ctimer;
int cown;
struct AB {
    int a, b;
};
AB chamber_dfs(int v) {
    int A = 1, B = 0;
    for (int d = 0; d < 4; ++d) {
        const int t = v + DV[d];
        if (blk[t] || seen[t] != vstamp || own[t] != cown) continue;
        if (cst[t] != cstamp) {
            cst[t] = cstamp;
            dfn[t] = lowv[t] = ++ctimer;
            const AB r = chamber_dfs(t);
            if (lowv[t] < lowv[v]) lowv[v] = lowv[t];
            if (lowv[t] >= dfn[v]) {
                if (r.a + r.b > B) B = r.a + r.b;
            } else {
                A += r.a;
                if (r.b > B) B = r.b;
            }
        } else if (dfn[t] < lowv[v]) lowv[v] = dfn[t];
    }
    return {A, B};
}
int chamber(int h, int i) {
    if (++cstamp == 0) {
        std::memset(cst, 0, sizeof cst);
        cstamp = 1;
    }
    cown = i;
    cst[h] = cstamp;
    dfn[h] = lowv[h] = ctimer = 0;
    const AB r = chamber_dfs(h);
    return r.a - 1 + r.b;
}

// 奇偶上界：从 h 出发能走的最多步数（区域里两种颜色的格数为 par）
inline int parity_bound(int h, const int par[2]) {
    const int first = par[col[h] ^ 1], second = par[col[h]];
    return first > second ? 2 * second + 1 : 2 * first;
}

int RIV;                    // 对手编号

long long limit;
bool aborted;


int srcbuf[tron::MAXN];

int evaluate_position(int a, int b, int turn, bool riv_alive) {
    work += 40;
    int ns = 0;
    vid[ns] = ME;
    srcbuf[ns++] = a;
    if (riv_alive) vid[ns] = RIV, srcbuf[ns++] = b;
    vturn = turn;
    Vor v;
    voronoi(srcbuf, ns, v);
    const int ca = chamber(a, 0), cb = chamber(b, 1);
    const int pa = parity_bound(a, v.par[0]), pb = parity_bound(b, v.par[1]);
    work += v.cnt[0] + v.cnt[1];
    if (!(v.conn & 2)) {
        const int left = std::min(ca, pa), right = std::min(cb, pb);
        const int quality = (v.edges[0] - 2 * v.cnt[0]) - (v.edges[1] - 2 * v.cnt[1]);
        const int advantage = 100 * (left - right) + std::clamp(quality, -95, 95);
        // A narrow parity lead is uncertain. A large lead in two closed chambers is decisive.
        return 8 * advantage / (12 + (left + right) / 12) + std::clamp(advantage * 5, -4600, 4600);
    }
    return 9 * (ca - cb) + 2 * (std::min(ca, pa) - std::min(cb, pb)) + (v.edges[0] - v.edges[1]);
}

// 置换表
struct TT {
    uint64_t key;
    int val;
    int8_t depth, flag, ma, mb;
};
constexpr int TTSIZE = 1 << 18;
TT tt[TTSIZE];
uint64_t ZC[MAXP], ZA[MAXP], ZB[MAXP], ZT[tron::MAXN], ZR[tron::MAXN];
uint64_t root_hash;    // 根局面所有轨迹格的 ZC 异或（置换表跨回合保留）
bool zinit = false;

uint64_t sm(uint64_t& s) {
    uint64_t z = (s += 0x9E3779B97F4A7C15ULL);
    z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ULL;
    z = (z ^ (z >> 27)) * 0x94D049BB133111EBULL;
    return z ^ (z >> 31);
}

struct Leaf { uint64_t key; int value; };
Leaf leaves[1 << 16];
int evaluate(int a, int b, int turn, uint64_t trails) {
    const auto key = trails ^ ZA[a] ^ ZB[b] ^ ZT[turn % N];
    auto& entry = leaves[key & ((1 << 16) - 1)];
    if (entry.key == key) { work += 15; return entry.value; }
    const int value = evaluate_position(a, b, turn, true);
    entry = {key, value};
    return value;
}
int root_turn;

// 置换表里的胜负分按"离本节点几步"存，取出时换回"离根几步"
constexpr int MATE = WIN - 10000;
inline int to_tt(int v, int ply) { return v >= MATE ? v + ply : v <= -MATE ? v - ply : v; }
inline int from_tt(int v, int ply) { return v >= MATE ? v - ply : v <= -MATE ? v + ply : v; }

// 我走 da、对手走 db 之后的结果。返回 0 = 都活；否则 1 我死、2 对手死、3 都死
inline int outcome(int a, int b, int da, int db, int turn) {
    const int ta = a + DV[da], tb = b + DV[db];
    bool dA = blk[ta], dB = blk[tb];
    if (!dA && !dB && ta == tb) {
        if (prio(ME, turn) < prio(RIV, turn)) dB = true;
        else dA = true;
    }
    return (dA ? 1 : 0) | (dB ? 2 : 0);
}

int search(int a, int b, int depth, int alpha, int beta, int ply, uint64_t hash) {
    const int turn = root_turn + ply;
    if (work >= check_at) {
        check_at = work + 18000;
        if (tron::budget_left() < margin) { aborted = true; return 0; }
    }
    if (depth <= 0) return evaluate(a, b, turn, hash);
    if (work >= limit) {
        aborted = true;
        return 0;
    }
    work += 10;
    int ma[4], nma = 0, mb[4], nmb = 0;
    for (int d = 0; d < 4; ++d) {
        if (!blk[a + DV[d]]) ma[nma++] = d;
        if (!blk[b + DV[d]]) mb[nmb++] = d;
    }
    if (nma == 0) return nmb == 0 ? (N == 2 ? 0 : -WIN + ply) : -WIN + ply;
    if (nmb == 0) return WIN - ply;
    const uint64_t key = hash ^ ZA[a] ^ ZB[b] ^ ZT[turn % N] ^ ZR[RIV];
    TT& e = tt[key & (TTSIZE - 1)];
    int hint_a = -1, hint_b = -1;
    if (e.key == key) {
        if (e.depth >= depth) {
            const int ev = from_tt(e.val, ply);
            if (e.flag == 0) return ev;
            if (e.flag == 1 && ev >= beta) return ev;
            if (e.flag == 2 && ev <= alpha) return ev;
        }
        hint_a = e.ma;
        hint_b = e.mb;
    }
    if (hint_a >= 0)
        for (int i = 0; i < nma; ++i)
            if (ma[i] == hint_a) {
                ma[i] = ma[0];
                ma[0] = hint_a;
                break;
            }
    const int a0 = alpha;
    int best = -INF, bma = ma[0], bmb = -1;
    for (int i = 0; i < nma; ++i) {
        const int da = ma[i], ta = a + DV[da];
        int order[4], no = 0;
        if (hint_b >= 0)
            for (int j = 0; j < nmb; ++j)
                if (mb[j] == hint_b) order[no++] = hint_b;
        for (int j = 0; j < nmb; ++j)
            if (mb[j] != hint_b) order[no++] = mb[j];
        int worst = INF, wr = order[0];
        for (int j = 0; j < no; ++j) {
            const int db = order[j], tb = b + DV[db];
            const int oc = outcome(a, b, da, db, turn);
            int v;
            if (oc == 1) v = -WIN + ply;
            else if (oc == 3) v = N == 2 ? 0 : -WIN + ply;
            else if (oc == 2) v = WIN - ply;
            else {
                blk[ta] = blk[tb] = 1;
                v = search(ta, tb, depth - 1, alpha, worst < beta ? worst : beta, ply + 1, hash ^ ZC[ta] ^ ZC[tb]);
                blk[ta] = blk[tb] = 0;
            }
            if (aborted) return 0;
            if (v < worst) worst = v, wr = db;
            if (worst <= alpha) break;
        }
        if (worst > best) best = worst, bma = da, bmb = wr;
        if (best > alpha) alpha = best;
        if (alpha >= beta) break;
    }
    e.key = key;
    e.val = to_tt(best, ply);
    e.depth = int8_t(depth);
    e.flag = best <= a0 ? 2 : best >= beta ? 1 : 0;
    e.ma = int8_t(bma);
    e.mb = int8_t(bmb);
    return best;
}

int duel(int last, int turn) {
    const int a = head[ME], b = head[RIV];
    int ma[4], nma = 0;
    ma[nma++] = last;
    for (int d = 0; d < 4; ++d)
        if (d != last) ma[nma++] = d;
    int k = 0;
    for (int i = 0; i < nma; ++i)
        if (!blk[a + DV[ma[i]]]) ma[k++] = ma[i];
    nma = k;
    if (nma < 2) return nma ? ma[0] : last;
    int mb[4], nmb = 0;
    for (int d = 0; d < 4; ++d)
        if (!blk[b + DV[d]]) mb[nmb++] = d;
    work = 0; check_at = 0; limit = turn ? 23000000 : 100000000; margin = turn ? 8.0 : 1650.0;
    root_turn = turn;
    root_hash = 0;
    for (int p = 0; p < (H + 2) * PW; ++p)
        if (blk[p]) root_hash ^= ZC[p];
    int best_move = ma[0];
    for (int depth = 1; depth <= 60; ++depth) {
        aborted = false;
        int best = -INF, bm = ma[0];
        for (int i = 0; i < nma; ++i) {
            const int da = ma[i], ta = a + DV[da];
            int worst = INF;
            if (nmb == 0) return da;
            for (int j = 0; j < nmb; ++j) {
                const int db = mb[j], tb = b + DV[db];
                const int oc = outcome(a, b, da, db, turn);
                int v;
                if (oc == 1) v = -WIN;
                else if (oc == 3) v = N == 2 ? 0 : -WIN;
                else if (oc == 2) v = WIN;
                else {
                    blk[ta] = blk[tb] = 1;
                    v = search(ta, tb, depth - 1, best, worst, 1, root_hash ^ ZC[ta] ^ ZC[tb]);
                    blk[ta] = blk[tb] = 0;
                }
                if (aborted) break;
                if (v < worst) worst = v;
                if (worst <= best) break;
            }
            if (aborted) break;
            if (worst > best) best = worst, bm = da;
        }
        if (aborted) break;    // 本层没搜完：用上一层的结果
        best_move = bm;
        // 上一层的最好走法排到最前
        for (int i = 0; i < nma; ++i)
            if (ma[i] == bm) {
                for (int j = i; j > 0; --j) ma[j] = ma[j - 1];
                ma[0] = bm;
                break;
            }
        if (best >= WIN / 2 || best <= -WIN / 2) {
            if (best >= WIN - 100 || best <= -WIN + 100) break;
        }
    }
    return best_move;
}


int pursue(const tron::State& s) {
    if (!zinit) {
        uint64_t seed = 12345;
        for (int i = 0; i < MAXP; ++i) ZC[i] = sm(seed), ZA[i] = sm(seed), ZB[i] = sm(seed);
        for (int k = 0; k < tron::MAXN; ++k) ZT[k] = sm(seed), ZR[k] = sm(seed);
        zinit = true;
    }
    W = s.W;
    H = s.H;
    N = s.N;
    ME = s.me;
    PW = W + 2;
    DV[tron::U] = -PW;
    DV[tron::R] = 1;
    DV[tron::D] = PW;
    DV[tron::L] = -1;
    std::memset(blk, 1, sizeof blk);
    for (int y = 0; y < H; ++y)
        for (int x = 0; x < W; ++x) {
            const int p = (y + 1) * PW + x + 1;
            blk[p] = s.cell[y][x] != tron::EMPTY;
            col[p] = uint8_t((x + y) & 1);
        }
    for (int k = 0; k < N; ++k) {
        head[k] = (s.y[k] + 1) * PW + s.x[k] + 1;
        alv[k] = s.alive[k];
    }
    const int last = s.last_dir[ME];
    RIV = 1 - ME;
    return duel(last, s.turn);
}

} // namespace tactics
namespace {
constexpr int SZ=43*43, STR=43, INF=30000;
constexpr int delta[4]={-STR,1,STR,-1};
// Simultaneous adversarial search, with a separate persistent path planner
// once no other live player can enter our connected component.
struct Bot {
 unsigned char wall[SZ]{};
 int pos[12],live[12],N,me,turn,W,H;
 short dist[12][SZ], closest[SZ];
 unsigned short masks[SZ];
 int owner[SZ],tin[SZ],low[SZ],timer,queue[SZ],nodes=0,evals=0,rival=-1;
 bool abort=false;
 double stop=8;
 unsigned long long rng=0x9e3779b97f4a7c15ULL;
 std::vector<int> saved; int savedTurn=-1;
 struct EvalEntry{uint64_t key=0;double value=0;unsigned generation=0;bool sep=false;};
 struct TTEntry{uint64_t key=0;double value=0;unsigned generation=0;short depth=0;char bound=0;};
 std::array<EvalEntry,32768> ec;
 std::array<TTEntry,32768> tt;
 uint64_t zcell[SZ],zhead[12][SZ],zt[12],hash=0;
 unsigned generation=0;bool hashReady=false,separated=false;
 int forecast[16][12]{},rootTurn=0;
 uint64_t mix(uint64_t x){x+=0x9e3779b97f4a7c15ULL;x=(x^(x>>30))*0xbf58476d1ce4e5b9ULL;x=(x^(x>>27))*0x94d049bb133111ebULL;return x^(x>>31);}
 void hashInit(){
  if(!hashReady){for(int p=0;p<SZ;p++){zcell[p]=mix(p+1);for(int k=0;k<12;k++)zhead[k][p]=mix(4096+SZ*k+p);}for(int k=0;k<12;k++)zt[k]=mix(50000+k);hashReady=true;}
  hash=0;for(int p=0;p<SZ;p++)if(wall[p])hash^=zcell[p];for(int k=0;k<N;k++)if(live[k])hash^=zhead[k][pos[k]];generation++;
 }
 int random(int n){rng^=rng<<7;rng^=rng>>9;return int(rng%unsigned(n));}
 bool timeout(){return (++nodes%16==0 && tron::budget_left()<stop)?abort=true:abort;}
 int degree(int p)const{return !wall[p-STR]+!wall[p+1]+!wall[p+STR]+!wall[p-1];}
 int priority(int k,int t)const{return (k-t%N+N)%N;}
 void distances(int k){
  std::fill(dist[k],dist[k]+SZ,short(INF));int b=0,e=0;queue[e++]=pos[k];dist[k][pos[k]]=0;
  while(b<e){int p=queue[b++],nd=dist[k][p]+1;for(int d:delta){int q=p+d;if(!wall[q]&&dist[k][q]==INF){dist[k][q]=short(nd);queue[e++]=q;}}}
 }
 struct Chamber{double a,b,exit;};
 Chamber dfs(int p,int par,int who){
  tin[p]=low[p]=++timer;double weight=1.0;
  Chamber out{(p%STR+p/STR)%2==0?weight:0,(p%STR+p/STR)%2!=0?weight:0,0};
  for(int d:delta){int q=p+d;if(owner[q]!=who||q==par)continue;
   if(tin[q])low[p]=std::min(low[p],tin[q]);
   else{auto c=dfs(q,p,who);low[p]=std::min(low[p],low[q]);
    if(low[q]>=tin[p])out.exit=std::max(out.exit,std::min(c.a+c.b,2*std::min(c.a,c.b)+1)+c.exit);
    else{out.a+=c.a;out.b+=c.b;out.exit=std::max(out.exit,c.exit);}
   }
  }return out;
 }
 // Multi-source geodesic Voronoi, then a rooted block-cut-tree capacity bound.
 // Checkerboard counts account for the parity constraint on simple grid paths.
 void areas(double value[12],bool chambers=true){
  std::fill(closest,closest+SZ,short(INF));
  std::fill(masks,masks+SZ,0);
  int qb=0,qe=0;
  for(int k=0;k<N;k++)if(live[k]){queue[qe++]=pos[k];closest[pos[k]]=0;masks[pos[k]]=1u<<k;}
  bool contact=false;
  while(qb<qe){int p=queue[qb++],nd=closest[p]+1;for(int d:delta){int q=p+d;if(wall[q])continue;
   if(closest[q]<INF && masks[q]!=masks[p])contact=true;
   if(closest[q]==INF){closest[q]=short(nd);masks[q]=masks[p];queue[qe++]=q;}
   else if(closest[q]==nd)masks[q]|=masks[p];
  }}
  separated=N==2&&!contact;
  std::fill(owner,owner+SZ,-1);std::fill(value,value+12,0.0);
  for(int y=1;y<=H;y++)for(int x=1;x<=W;x++){
   int p=y*STR+x;if(wall[p])continue;int kbest=-1;
   unsigned mask=masks[p];
   while(mask){int k=std::countr_zero(mask);mask&=mask-1;int phase=N==2?rootTurn:turn+closest[p]-1;if(kbest<0||priority(k,phase)<priority(kbest,phase))kbest=k;}
   owner[p]=kbest;
   if(kbest>=0)value[kbest]++;
  }
  if(chambers){std::fill(tin,tin+SZ,0);timer=0;
   for(int k=0;k<N;k++)if(live[k])owner[pos[k]]=k;
   for(int k=0;k<N;k++)if(live[k]){auto c=dfs(pos[k],-1,k);double usable=std::min(c.a+c.b,2*std::min(c.a,c.b)+1)+c.exit-1;value[k]=usable*.9+value[k]*.1;}
  }
 }
 double evaluate(){
  if((++evals&3)==0 && tron::budget_left()<stop){abort=true;return 0;}
  uint64_t key=hash^zt[turn%N];auto &ce=ec[key&32767];
  if(ce.generation==generation&&ce.key==key){separated=ce.sep;return ce.value;}
  separated=false;
  int alive=0;for(int k=0;k<N;k++)alive+=live[k];
  if(!live[me])return alive?(N==2?-100000.0:-100000.0-10000*alive)+10*(turn-rootTurn):0;
  if(alive==1)return 100000-10*(turn-rootTurn);
  double a[12];areas(a);double score=0;
  if(N==2)score=10*(a[me]-a[rival]);
  else{score=3*a[me];for(int k=0;k<N;k++)if(k!=me&&live[k])score+=100.0*(a[me]-a[k])/(30+a[me]+a[k]);score+=100*(N-alive);}
  int deg=degree(pos[me]);score+=deg==1?-3:deg==2?0:1;
  if(N==2){int od=degree(pos[rival]);score-=od==1?-3:od==2?0:1;}
  // A secured lead is worth more than the same amount of contested territory.
  if(N==2)score=90000.0*std::tanh(score/(separated?(60+.3*(a[me]+a[rival])):350.0));
  ce={key,score,generation,separated};return score;
 }
 struct Change{int old[12],dest[12],l[12];uint64_t oldHash;};
 Change stepMoves(const int dirs[],bool cautious=false){
  Change c;c.oldHash=hash;
  for(int k=0;k<N;k++){c.old[k]=pos[k];c.l[k]=live[k];c.dest[k]=dirs[k]>=0?pos[k]+delta[dirs[k]]:pos[k];if(live[k]&&(dirs[k]<0||wall[c.dest[k]]))live[k]=0;}
  int valid[12];std::copy(live,live+N,valid);
  for(int k=0;k<N;k++)if(valid[k])for(int j=0;j<N;j++)if(j!=k&&valid[j]&&c.dest[k]==c.dest[j]&&priority(j,turn)<priority(k,turn))live[k]=0;
  if(cautious && turn==rootTurn && live[me])for(int k=0;k<N;k++)if(k!=me&&k!=rival&&c.l[k]&&priority(k,turn)<priority(me,turn)){
   int dif=std::abs(c.old[k]-c.dest[me]);if(dif==1||dif==STR){live[me]=0;break;}
  }
  for(int k=0;k<N;k++){if(c.l[k])hash^=zhead[k][c.old[k]];if(live[k]){pos[k]=c.dest[k];wall[pos[k]]=1;hash^=zhead[k][pos[k]]^zcell[pos[k]];}}
  turn++;return c;
 }
 Change move(int d,int e){
  int dirs[12];for(int k=0;k<N;k++){
   int z=forecast[std::min(15,turn-rootTurn)][k];
   if(live[k]&&(z<0||wall[pos[k]+delta[z]])){z=-1;int best=-1;for(int a=0;a<4;a++)if(!wall[pos[k]+delta[a]]){int v=degree(pos[k]+delta[a]);if(v>best){z=a;best=v;}}}
   dirs[k]=z;
  }
  dirs[me]=d;if(rival>=0)dirs[rival]=e;
  return stepMoves(dirs,true);
 }
 void undo(const Change& c){turn--;hash=c.oldHash;for(int k=0;k<N;k++){if(live[k])wall[pos[k]]=0;pos[k]=c.old[k];live[k]=c.l[k];}}
 void predict(const tron::State& s){
  for(int t=0;t<16;t++)for(int k=0;k<N;k++)forecast[t][k]=s.last_dir[k];
  if(N==2)return;
  Change history[6];int count=0;
  for(int t=0;t<(N==4?3:4);t++){
   if(tron::budget_left()<stop+29)break;
   int dirs[12];
   for(int k=0;k<N;k++){
    dirs[k]=-1;if(!live[k])continue;double best=-1e20;
    for(int d=0;d<4;d++){int q=pos[k]+delta[d];if(wall[q])continue;int old=pos[k];pos[k]=q;wall[q]=1;
     double a[12];areas(a,false);
     double value=a[k]+.35*degree(q)+(d==forecast[t][k]?.04:0);
     for(int j=0;j<N;j++)if(j!=k&&live[j]&&priority(j,turn)<priority(k,turn)){
      int gap=std::abs(pos[j]-q);
      if(gap==1||gap==STR)value-=2000;
     }
     pos[k]=old;wall[q]=0;
     if(value>best){best=value;dirs[k]=d;}
    }
    forecast[t][k]=dirs[k];for(int f=t+1;f<16;f++)forecast[f][k]=dirs[k];
   }
   history[count++]=stepMoves(dirs);
  }
  while(count)undo(history[--count]);
 }
 int moves(int k,int a[4]){int n=0;if(k>=0&&live[k])for(int d=0;d<4;d++)if(!wall[pos[k]+delta[d]])a[n++]=d;if(!n)a[n++]=-1;return n;}
 double search(int depth,double alpha,double beta){
  struct RestoreRival{int &value,old;~RestoreRival(){value=old;}} restoreRival{rival,rival};
  if(N>2&&depth>1){distances(me);int nearest=INF,next=-1;for(int k=0;k<N;k++)if(k!=me&&live[k]){int d=INF;for(int dd:delta)d=std::min(d,int(dist[me][pos[k]+dd])+1);if(d<nearest){nearest=d;next=k;}}
   int oldDist=INF;if(rival>=0&&live[rival])for(int dd:delta)oldDist=std::min(oldDist,int(dist[me][pos[rival]+dd])+1);
   if(N==4||nearest+2<oldDist||rival<0||!live[rival])rival=next;
  }
  if(timeout())return 0;if(!depth||!live[me]||(rival>=0&&!live[rival]))return evaluate();
  uint64_t key=hash^zt[turn%N]^mix(60000+rival);auto &te=tt[key&32767];
  double originalAlpha=alpha,originalBeta=beta;
  if(te.generation==generation&&te.key==key&&te.depth>=depth){if(te.bound==0)return te.value;if(te.bound==1)alpha=std::max(alpha,te.value);else beta=std::min(beta,te.value);if(alpha>=beta)return te.value;}
  double stand=evaluate();if(abort)return 0;if(separated)return stand;
  int ma[4],oa[4],nm=moves(me,ma),no=moves(rival,oa);double order[4][4],mv[4];int oi[4][4];
  for(int i=0;i<nm;i++){mv[i]=1e20;for(int j=0;j<no;j++){auto c=move(ma[i],oa[j]);order[i][j]=evaluate();undo(c);if(abort)return 0;oi[i][j]=j;mv[i]=std::min(mv[i],order[i][j]);}std::sort(oi[i],oi[i]+no,[&](int a,int b){return order[i][a]<order[i][b];});}
  int mi[4]={0,1,2,3};std::sort(mi,mi+nm,[&](int a,int b){return mv[a]>mv[b];});
  if(depth==1){
   return mv[mi[0]];
  }
  double best=-1e20;
  for(int ii=0;ii<nm;ii++){int i=mi[ii];double worst=1e20;
   for(int jj=0;jj<no;jj++){int j=oi[i][jj];auto c=move(ma[i],oa[j]);double v=search(depth-1,std::max(alpha,best),std::min(beta,worst));undo(c);if(abort)return 0;worst=std::min(worst,v);if(worst<=std::max(alpha,best))break;}
   best=std::max(best,worst);if(best>=beta)break;
  }te={key,best,generation,short(depth),char(best<=originalAlpha?2:best>=originalBeta?1:0)};return best;
 }
 int duel(int last){
  int ma[4],oa[4],nm=moves(me,ma),no=moves(rival,oa);if(nm==1)return std::max(0,ma[0]);
  int answer=ma[0];double scores[4],reply[4][4];int order[4]={0,1,2,3},oporder[4][4];
  for(int i=0;i<nm;i++){scores[i]=1e20;for(int j=0;j<no;j++){auto c=move(ma[i],oa[j]);reply[i][j]=evaluate();scores[i]=std::min(scores[i],reply[i][j]);undo(c);oporder[i][j]=j;}if(ma[i]==last)scores[i]+=.001;
   std::sort(oporder[i],oporder[i]+no,[&](int a,int b){return reply[i][a]<reply[i][b];});
  }
  std::sort(order,order+nm,[&](int a,int b){return scores[a]>scores[b];});answer=ma[order[0]];
  int maxdepth=N==2?12:N==4?4:6;
  for(int depth=2;depth<=maxdepth;depth++){
   if(tron::budget_left()<stop+2)break;double best=-1e20;int bestmove=answer;double next[4];
   for(int ii=0;ii<nm;ii++){int i=order[ii];double worst=1e20;
    for(int jj=0;jj<no;jj++){int j=oporder[i][jj];auto c=move(ma[i],oa[j]);double v=search(depth-1,best,worst);undo(c);if(abort)break;reply[i][j]=v;worst=std::min(worst,v);if(worst<best)break;}
    if(abort)break;next[i]=worst;if(worst>best){best=worst;bestmove=ma[i];}
   }
   if(abort)break;answer=bestmove;std::copy(next,next+nm,scores);std::sort(order,order+nm,[&](int a,int b){return scores[a]>scores[b];});for(int i=0;i<nm;i++)std::sort(oporder[i],oporder[i]+no,[&](int a,int b){return reply[i][a]<reply[i][b];});if(std::abs(best)>90000)break;
  }return answer;
 }
 // Rooted longest-path improvement: endpoint rotations, square insertions,
 // randomized restarts, and preservation of the best valid path across turns.
 int isolated(int last){
  const int root=pos[me];std::vector<int> best;
  if(savedTurn==turn-1&&saved.size()>1&&saved[1]==root){best.assign(saved.begin()+1,saved.end());for(size_t i=1;i<best.size();i++)if(wall[best[i]]){best.resize(i);break;}}
  if(best.empty())best.push_back(root);
  int maxpossible=0,parity[2]={0,0};distances(me);
  for(int p=0;p<SZ;p++)if(dist[me][p]<INF){maxpossible++;parity[(p%STR+p/STR)&1]++;}
  int color=(root%STR+root/STR)&1;maxpossible=std::min(maxpossible,2*std::min(parity[color]-1,parity[1-color])+1+(parity[1-color]>parity[color]-1));
  // A simple path can use only one child block beyond an articulation point.
  // The chamber bound often proves that the saved path already attains the maximum.
  std::fill(owner,owner+SZ,-1);for(int p=0;p<SZ;p++)if(dist[me][p]<INF)owner[p]=me;
  std::fill(tin,tin+SZ,0);timer=0;auto block=dfs(root,-1,me);
  maxpossible=std::min(maxpossible,int(std::min(block.a+block.b,2*std::min(block.a,block.b)+1)+block.exit));
  std::vector<int> path=best;int index[SZ];
  auto rebuild=[&](){std::fill(index,index+SZ,-1);for(int i=0;i<(int)path.size();i++)index[path[i]]=i;};rebuild();
  for(int iter=0;iter<140000 && int(best.size())<maxpossible;iter++){
   if((iter&255)==0&&tron::budget_left()<stop)break;
   int p=path.back(),choice=-1,bestdeg=100;
   bool explore=random(5)==0;
   for(int z=0,off=random(4);z<4;z++){int q=p+delta[(z+off)&3];if(wall[q]||index[q]>=0)continue;int deg=0;for(int dd:delta)deg+=!wall[q+dd]&&index[q+dd]<0;int score=explore?random(12):(deg?deg*3+random(4):30);if(score<bestdeg){bestdeg=score;choice=q;}}
   if(choice>=0){index[choice]=int(path.size());path.push_back(choice);}
   else{int ro[4],nr=0;for(int d:delta){int q=p+d,j=index[q];if(j>=0&&j+2<(int)path.size())ro[nr++]=j;}
    if(nr){int j=ro[random(nr)];std::reverse(path.begin()+j+1,path.end());for(int i=j+1;i<(int)path.size();i++)index[path[i]]=i;}
    else if(path.size()>1){int cut=std::max(1,int(path.size())-1-random(std::min(12,int(path.size())-1)));while(int(path.size())>cut){index[path.back()]=-1;path.pop_back();}}
   }
   if(path.size()>best.size())best=path;if(int(best.size())>=maxpossible)break;
   if(iter%256==255){
    for(int i=0;i+1<(int)path.size();i++){int a=path[i],b=path[i+1],diff=b-a,dirs[2];if(std::abs(diff)==1){dirs[0]=-STR;dirs[1]=STR;}else{dirs[0]=-1;dirs[1]=1;}
     for(int d:dirs){int u=a+d,v=b+d;if(!wall[u]&&!wall[v]&&index[u]<0&&index[v]<0){path.insert(path.begin()+i+1,{u,v});rebuild();i+=2;break;}}
    }
    if(path.size()>best.size())best=path;
    if(iter%2048==2047){path.assign(1,root);rebuild();}
    else if(random(4)==0){path=best;int cut=std::max(1,int(path.size())-1-random(std::max(1,int(path.size())/2)));path.resize(cut);rebuild();}
   }
  }
  saved=best;savedTurn=turn;if(best.size()>1)for(int d=0;d<4;d++)if(root+delta[d]==best[1])return d;
  for(int d=0;d<4;d++)if(!wall[root+delta[d]])return d;return last;
 }
 // Before accepting a partition, try to certify it with an actual survival
 // path longer than every cell the opponent could possibly still consume.
 int securePartition(){
  if(N!=2)return -1;
  int root=pos[me],enemy=1-me;
  for(int d=0;d<4;d++){
   int q=root+delta[d];if(wall[q])continue;
   int gap=std::abs(q-pos[enemy]);if((gap==1||gap==STR)&&priority(enemy,turn)<priority(me,turn))continue;
   pos[me]=q;wall[q]=1;turn++;distances(me);
   bool separate=true;for(int dd:delta)if(dist[me][pos[enemy]+dd]<INF)separate=false;
   if(separate){
    int mine=0,theirs=0;for(int p=0;p<SZ;p++)mine+=dist[me][p]<INF;
    distances(enemy);for(int p=0;p<SZ;p++)theirs+=dist[enemy][p]<INF;
    if(mine>theirs*1.12+4 && tron::budget_left()>stop+16){
     double oldstop=stop;stop=std::max(stop,tron::budget_left()-6.0);
     saved.clear();savedTurn=-1;isolated(d);stop=oldstop;
     if(int(saved.size())>theirs+1){
      saved.insert(saved.begin(),root);turn--;savedTurn=turn;pos[me]=root;wall[q]=0;return d;
     }
     saved.clear();savedTurn=-1;
    }
   }
   turn--;pos[me]=root;wall[q]=0;
  }
  return -1;
 }
 int decide(const tron::State& s){
  W=s.W;H=s.H;N=s.N;me=s.me;turn=s.turn;rootTurn=turn;stop=turn==0?1650:8;nodes=evals=0;abort=false;std::fill(wall,wall+SZ,1);
  for(int y=0;y<H;y++)for(int x=0;x<W;x++)wall[(y+1)*STR+x+1]=s.cell[y][x]!=tron::EMPTY;
  for(int k=0;k<N;k++){pos[k]=(s.y[k]+1)*STR+s.x[k]+1;live[k]=s.alive[k];}
  hashInit();
  if(!turn){saved.clear();savedTurn=-1;rng^=pos[me]*1234567ULL+N*37;}
  distances(me);rival=-1;int nearest=INF;
  for(int k=0;k<N;k++)if(k!=me&&live[k]){int d=INF;for(int dd:delta)d=std::min(d,int(dist[me][pos[k]+dd])+1);if(d<nearest){nearest=d;rival=k;}}
  if(rival<0)return isolated(s.last_dir[me]);
  if (N == 2) {
   int secure=securePartition();if(secure>=0)return secure;
   return tactics::pursue(s);
  }
  predict(s);saved.clear();savedTurn=-1;
  return duel(s.last_dir[me]);
 }
};
}
int decide(const tron::State& s) { static Bot bot; return bot.decide(s); }
