"""Compare both submissions on the same runner using maps outside the community quick set."""
import hashlib
import json
import os
import random
import sys
from concurrent.futures import ProcessPoolExecutor
from pathlib import Path


LAND = Path("official/land").resolve()
sys.path.insert(0, str(LAND / "tournament"))
import round_robin as rr


ENTRY = Path("community/land/naihe0__frontier-loop/bot.cpp")
PLAYER = "your-bot@you#1"
MAP_SAMPLE_SEED = 202611261433791
STRONG_PAIRS = [
    ("sonnet-5", "anchor-sparring"), ("opus-5.5", "gpt-6-astra"),
    ("anchor-sparring", "opus-5.5"), ("gpt-6-astra", "sonnet-5"),
    ("sonnet-5", "opus-5.5"), ("gpt-6-astra", "anchor-sparring"),
]
MELEE_TABLES = [
    ("opus-5.5", "sonnet-5", "gpt-6-astra"), ("mimo-2.6-pro", "anchor-sparring", "gpt-6-sol"),
    ("gpt-6-astra", "kimi-k3", "anchor-greedy"), ("opus-5.5", "glm-5.3", "anchor-sparring"),
    ("sonnet-5", "gpt-6-sol", "mystery-model"), ("mimo-2.6-pro", "sonnet-5", "gpt-6-astra"),
]


def faces_centre(seed):
    config = rr.referee.config_for(4)
    starts, headings = rr.referee.make_start(seed, config)
    x, y = starts[0]
    dx, dy = {"R": (1, 0), "L": (-1, 0), "D": (0, 1), "U": (0, -1)}[headings[0]]
    return dx * (config["width"] - 1 - 2 * x) + dy * (config["height"] - 1 - 2 * y) > 0


def fixtures():
    rng = random.Random(MAP_SAMPLE_SEED)
    pool = range(1_000_000, 2_000_000)
    maps = rng.sample(pool, len(STRONG_PAIRS))
    taken = set(maps)
    headings = [True, False] * (len(MELEE_TABLES) // 2)
    rng.shuffle(headings)
    melee_maps = []
    for inward in headings:
        seed = rng.choice(pool)
        while seed in taken or faces_centre(seed) != inward:
            seed = rng.choice(pool)
        taken.add(seed)
        melee_maps.append(seed)
    duels, melee = [], []
    for seed, opponents in zip(maps, STRONG_PAIRS):
        for other in opponents:
            duels.extend([(seed, [PLAYER, other]), (seed, [other, PLAYER])])
    for seed, opponents in zip(melee_maps, MELEE_TABLES):
        table = [PLAYER, *opponents]
        melee.extend((seed, table[i:] + table[:i]) for i in range(4))
    return duels, melee


def play_pair(task):
    index, seed, seats, contenders, opponents = task
    order = ("baseline", "candidate") if index % 2 == 0 else ("candidate", "baseline")
    results = {}
    for version in order:
        exes = [contenders[version] if player == PLAYER else opponents[player] for player in seats]
        results[version] = rr.referee.run_match(exes, seats, seed)
    return {"seed": seed, "seats": seats, "results": results}


def tally(rows, version):
    total = points = timeouts = forfeits = 0
    for row in rows:
        result = row["results"][version]
        index = result["names"].index(PLAYER)
        rank = result["ranks"][index]
        for i, other in enumerate(result["ranks"]):
            if i != index:
                total += 1
                points += int(rank < other) + 0.5 * int(rank == other)
        timeouts += result["timeouts"][index]
        forfeits += bool(result["forfeit"][index])
    return {"points": points, "possible": total, "games": len(rows), "timeouts": timeouts, "forfeits": forfeits}


def main():
    out = Path("holdout-results")
    out.mkdir(exist_ok=True)
    cache = str((out / "build").resolve())
    official = {name: Path(src) for name, src in rr.ANCHORS.items()}
    official.update({src.parent.name.split("@")[0]: src for src in (LAND / "bots").glob("*/bot.cpp")})
    scripts = {version: Path(version) / ENTRY for version in ("baseline", "candidate")}
    hashes = {key: hashlib.sha256(source.read_bytes()).hexdigest() for key, source in scripts.items()}
    assert hashes["baseline"] == "e9b35497668f1a53f64024774364215eab1714961ed3d89773a3cb0f6e300c84"
    plans = dict(zip(("duel", "melee"), fixtures()))
    required = {player for rows in plans.values() for _, seats in rows for player in seats if player != PLAYER}
    opponents = {name: rr.build.compile_bot(str(official[name]), cache) for name in sorted(required)}
    contenders = {name: rr.build.compile_bot(str(path), cache) for name, path in scripts.items()}
    records, stats = {}, {}
    for mode, rows in plans.items():
        assert len(rows) == 24
        count = len(rows[0][1])
        workers = max(1, min(8, (os.cpu_count() or 2) // count))
        tasks = [(i, seed, seats, contenders, opponents) for i, (seed, seats) in enumerate(rows)]
        with ProcessPoolExecutor(workers) as pool:
            records[mode] = list(pool.map(play_pair, tasks))
        stats[mode] = {version: tally(records[mode], version) for version in scripts}
    result = {"map_sample_seed": MAP_SAMPLE_SEED, "source_sha256": hashes, "stats": stats, "games": records}
    (out / "holdout.json").write_text(json.dumps(result, sort_keys=True) + "\n", encoding="utf-8")
    report = ["## Previously unseen maps", "", "| Version | Duel on 6 maps | Four-player on 6 maps |",
              "|---|---:|---:|"]
    for version in scripts:
        duel = stats["duel"][version]
        melee = stats["melee"][version]
        report.append(f"| {version} | {duel['points']:g}/{duel['possible']} | {melee['points']:g}/{melee['possible']} |")
    summary = "\n".join(report) + "\n"
    print(summary)
    with open(os.environ["GITHUB_STEP_SUMMARY"], "a", encoding="utf-8") as f:
        f.write(summary)


if __name__ == "__main__":
    main()
