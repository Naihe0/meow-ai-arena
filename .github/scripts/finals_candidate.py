from pathlib import Path
import argparse
import hashlib
import importlib.util
import json
import os
import sys

parser = argparse.ArgumentParser()
parser.add_argument("episode", choices=["tron", "boomerang"])
parser.add_argument("kind", choices=["official-full", "independent-full"])
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
if options.kind == "official-full":
    import subprocess
    subprocess.run([sys.executable, "community/check.py", str(source.parent), "--full", "--out", str(destination), "--timeout", "75"], check=True)
    doc = json.loads((destination / "result.json").read_bytes())
    if doc["status"] != "pass" or doc["mode"] != "full":
        raise SystemExit("Official full evaluation did not pass")
    detail = doc["detail"]
    score = doc["score"]
else:
    sys.path.insert(0, str(root / episode))
    spec = importlib.util.spec_from_file_location("validation_challenge", root / episode / "challenge.py")
    challenge = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(challenge)
    # Keep the official game engine, budget, map pool, seat rotation, and rating fit.
    # This separate schedule is only a reproducibility check and is never submitted for ranking.
    challenge.SEED = {"tron": 694391, "boomerang": 371527}[episode]
    sys.argv = ["challenge.py", str(source), "--full", "--out", str(destination)]
    if episode == "tron":
        sys.argv += ["--require-cpu"]
    challenge.main()
    detail = json.loads((destination / "result.json").read_bytes())
    score = detail["rating"]
if not detail["complete"] or not detail["full"] or detail["source_sha256"] != options.expected_sha:
    raise SystemExit("Incomplete result or source identity mismatch")
expected_games = {"tron": 328, "boomerang": 1664}[episode]
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

