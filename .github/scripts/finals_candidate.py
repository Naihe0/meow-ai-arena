from pathlib import Path
import argparse
import hashlib
import importlib.util
import json
import os
import random
import secrets
import sys

def direct_schedule(episode, challenge, seed):
    rng = random.Random(seed)
    games = []
    def rotate(mode, game_map, game_seed, opponents, offsets):
        seats = ["me", *rng.sample(list(opponents), len(opponents))]
        for offset in offsets:
            games.append((mode, game_map, game_seed, seats[offset:] + seats[:offset]))
    if episode == "tron":
        focus = ["AstraUF", "sparring_hard", "Mistral", "DSNew"]
        for i in range(32):
            for opponent in focus:
                rotate("1v1", 2, seed+i, [opponent], range(2))
        for i in range(40):
            rivals = [name for index, name in enumerate(focus) if index != i % 4]
            rotate("3-4", 4, seed+100+i, rivals, range(4))
        others = [name for name in challenge.OPPONENTS if name not in focus]
        for i in range(24):
            rivals = focus + rng.sample(others, 7)
            rotate("12", 12, seed+300+i, rivals, [i%3+3*k for k in range(4)])
    else:
        focus = ["astra", "fable", "opus"]
        others = [name for name in challenge.OPPONENTS if name != "astra"]
        for mid, game_map in enumerate(challenge.MAPS):
            for i in range(12):
                for opponent in focus:
                    rotate("duel", game_map, seed+15*mid+i, [opponent], range(2))
                rivals = focus if i % 2 == 0 else ["astra", *rng.sample(others, 2)]
                rotate("ffa", game_map, seed+500+15*mid+i, rivals, range(4))
    return focus, games

def per_game_evidence(challenge, games, records, official, episode, destination):
    expected = {row["name"]: row["tally"] for row in official["opponents"]}
    observed = {name: {mode: [0, 0, 0] for mode in by_mode} for name, by_mode in expected.items()}
    matches = []
    for fixture, record in zip(games, records):
        mode, game_map, seed, seats = fixture
        if episode == "boomerang":
            tallies, _ = challenge.tally_games([fixture], [record])
            outcomes = {name: tallies[mode][name].index(1) for name in seats if name != "me"}
        else:
            turns = [10**9 if value < 0 else value for value in record["death_turn"]]
            ours = turns[seats.index("me")]
            outcomes = {name: (0 if ours > turns[i] else 1 if ours == turns[i] else 2)
                        for i, name in enumerate(seats) if name != "me"}
        for name, index in outcomes.items():
            observed[name][mode][index] += 1
        matches.append([mode, game_map, seed, outcomes])
    if observed != expected:
        raise ValueError("Per-game records disagree with the official opponent totals")
    (destination / "matchups.json").write_text(json.dumps(matches, separators=(",", ":")), encoding="utf-8")

parser = argparse.ArgumentParser()
parser.add_argument("episode", choices=["tron", "boomerang"])
parser.add_argument("kind", choices=["official-quick", "official-full", "independent-full", "direct-panel"])
parser.add_argument("expected_sha")
options = parser.parse_args()
root = Path.cwd()
episode = options.episode
slug = {"tron": "naihe0__cutline", "boomerang": "naihe0__return-arc"}[episode]
source = root / "community" / episode / slug / "bot.cpp"
if hashlib.sha256(source.read_bytes()).hexdigest() != options.expected_sha:
    raise SystemExit("Source hash mismatch")
destination = root / "validation-output"
if destination.exists():
    raise SystemExit("Expected a fresh result directory")
full = options.kind != "official-quick"
if options.kind.startswith("official-"):
    import subprocess
    flags = ["--full"] if full else []
    subprocess.run([sys.executable, "community/check.py", str(source.parent), *flags, "--out", str(destination), "--timeout", "75"], check=True)
    doc = json.loads((destination / "result.json").read_bytes())
    if doc["status"] != "pass" or doc["mode"] != ("full" if full else "quick"):
        raise SystemExit("Official evaluation did not pass in the requested mode")
    detail = doc["detail"]
    score = doc["score"]
else:
    sys.path.insert(0, str(root / episode))
    spec = importlib.util.spec_from_file_location("validation_challenge", root / episode / "challenge.py")
    challenge = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(challenge)
    # Keep the official game engine, budget, map pool, seat rotation, and rating fit.
    # This separate schedule is only a reproducibility check and is never submitted for ranking.
    panel = options.kind == "direct-panel"
    challenge.SEED = 1000000+secrets.randbelow(800000000) if panel else {"tron": 694391, "boomerang": 371527}[episode]
    raw_dir = destination
    if panel:
        focus, fixtures = direct_schedule(episode, challenge, challenge.SEED)
        challenge.schedule = lambda *args: fixtures
        destination.mkdir()
        raw_dir = destination / "native-panel"
    original_result = challenge.make_result
    def record_result(games, records, *args, **kwargs):
        measured = original_result(games, records, *args, **kwargs)
        per_game_evidence(challenge, games, records, measured, episode, destination)
        return measured
    challenge.make_result = record_result
    sys.argv = ["challenge.py", str(source), "--full", "--out", str(raw_dir)]
    if episode == "tron":
        sys.argv += ["--require-cpu"]
    challenge.main()
    detail = json.loads((raw_dir / "result.json").read_bytes())
    if panel:
        expected = {"tron":512, "boomerang":720}[episode]
        if detail["source_sha256"]!=options.expected_sha or not detail["complete"] or detail["games"]!=expected or detail["budget"]["budget_kind"]!="cpu":
            raise SystemExit("Incomplete head-to-head panel")
        rows = {p["name"]:p["tally"] for p in detail["opponents"] if p["name"] in focus}
        panel_doc = {"episode":episode, "kind":"direct-panel", "source_sha256":options.expected_sha,
                     "seed":detail["seed"], "games":expected, "stats":detail["stats"], "opponents":rows}
        (destination/"comparison.json").write_text(json.dumps(panel_doc,indent=2)+"\n",encoding="utf-8")
        print(json.dumps(panel_doc))
        sys.exit(0)
    score = detail["rating"]
if not detail["complete"] or detail["full"] != full or detail["source_sha256"] != options.expected_sha:
    raise SystemExit("Incomplete result or source identity mismatch")
expected_games = {"tron": 82, "boomerang": 416}[episode] * (4 if full else 1)
if detail["games"] != expected_games or detail["budget"]["budget_kind"] != "cpu":
    raise SystemExit("Game count or budget mismatch")
report = {"episode": episode, "kind": options.kind, "source_sha256": options.expected_sha, "games": expected_games, "seed": detail["seed"],
          "score": score, "reference_rank": detail["rank"], "ratings": detail["ratings"],
          "opponents": {p["name"]: p["tally"] for p in detail["opponents"]}}
data = json.dumps(report, ensure_ascii=False, indent=2)
(destination / "comparison.json").write_text(data + "\n", encoding="utf-8")
steps = os.environ.get("GITHUB_STEP_SUMMARY")
if steps:
    with open(steps, "a", encoding="utf-8") as stream:
        print(f"## {episode} · {options.kind}\n\n{expected_games} games, fixed-reference rating {score:.1f}\n\n", file=stream)

