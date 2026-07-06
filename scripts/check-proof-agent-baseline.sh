#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "${BASH_SOURCE[0]}")/.."

echo "[1/1] Proof-agent PUA-M00 baseline validation"
python3 - <<'PY'
import csv
import json
import re
import subprocess
from pathlib import Path


ROOT = Path(".")
PUA_ROOT = ROOT / "develop" / "proof-using-agents"
DATA_DIR = PUA_ROOT / "data"
SCHEMA_DIR = PUA_ROOT / "schemas"
CHECK_FAST = ROOT / "scripts" / "check-fast.sh"
EXECUTION_BASELINE_JSON = DATA_DIR / "execution_plane_baseline.json"
EXECUTION_BASELINE_CSV = DATA_DIR / "execution_plane_baseline.csv"
BENCHMARK_TAXONOMY_JSON = DATA_DIR / "benchmark_taxonomy.json"
BENCHMARK_TAXONOMY_CSV = DATA_DIR / "benchmark_taxonomy.csv"
GOLDEN_CORPUS_JSON = DATA_DIR / "golden_corpus_manifest.json"
GOLDEN_CORPUS_CSV = DATA_DIR / "golden_corpus_manifest.csv"
EXECUTION_SCHEMA = SCHEMA_DIR / "execution_plane.schema.json"
KPI_CATALOG = DATA_DIR / "kpi_catalog.json"


def fail(message: str) -> None:
    raise SystemExit(f"error: {message}")


def load_json(path: Path):
    try:
        return json.loads(path.read_text())
    except json.JSONDecodeError as exc:
        fail(f"{path}: invalid JSON: {exc}")


def is_git_tracked(path: Path) -> bool:
    result = subprocess.run(
        ["git", "ls-files", "--error-unmatch", "--", str(path)],
        check=False,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    return result.returncode == 0


def checked_relative_path(raw_path: str, owner: str, field: str) -> Path:
    path = Path(raw_path)
    if path.is_absolute() or ".." in path.parts:
        fail(f"{owner}: {field} must be a repository-relative path")
    if not path.exists():
        fail(f"{owner}: manifest path does not exist: {raw_path}")
    return path


json_paths = sorted(DATA_DIR.rglob("*.json")) + sorted(SCHEMA_DIR.rglob("*.json"))
if not json_paths:
    fail("no proof-agent JSON files found under data/ or schemas/")

parsed_json = {path: load_json(path) for path in json_paths}
print(f"parsed_json_files={len(parsed_json)}")

metadata_result = subprocess.run(
    ["cargo", "metadata", "--format-version", "1", "--no-deps"],
    check=False,
    text=True,
    stdout=subprocess.PIPE,
    stderr=subprocess.PIPE,
)
if metadata_result.returncode != 0:
    fail(
        "cargo metadata --format-version 1 --no-deps failed:\n"
        + metadata_result.stderr.strip()
    )

try:
    metadata = json.loads(metadata_result.stdout)
except json.JSONDecodeError as exc:
    fail(f"cargo metadata returned invalid JSON: {exc}")

package_names = sorted(package["name"] for package in metadata.get("packages", []))
if not package_names:
    fail("cargo metadata reported no workspace packages")

for name in package_names:
    normalized = name.lower().replace("_", "-")
    if normalized == "npa-agents" or normalized.startswith("agent-"):
        fail(f"agent package member is present in root workspace: {name}")
    forbidden_tokens = [
        "axum",
        "postgres",
        "postgresql",
        "sqlx",
        "model",
        "scheduler",
        "sandbox",
        "telemetry",
    ]
    for token in forbidden_tokens:
        if token in normalized:
            fail(f"forbidden proof-agent platform package member is present: {name}")

print(f"workspace_packages={','.join(package_names)}")

check_fast_text = CHECK_FAST.read_text()
if "npa-proof-corpus" in check_fast_text:
    fail("scripts/check-fast.sh should not reference split npa-proof-corpus workspace")
if "cargo clippy --workspace --all-targets" not in check_fast_text:
    fail("scripts/check-fast.sh must run clippy over the core workspace")
if "cargo test --workspace --" not in check_fast_text:
    fail("scripts/check-fast.sh must run tests over the core workspace")
print("check_fast_core_workspace_only=true")

baseline = parsed_json.get(EXECUTION_BASELINE_JSON) or load_json(EXECUTION_BASELINE_JSON)
execution_schema = parsed_json.get(EXECUTION_SCHEMA) or load_json(EXECUTION_SCHEMA)
kpi_catalog = parsed_json.get(KPI_CATALOG) or load_json(KPI_CATALOG)

rows = baseline.get("features")
if not isinstance(rows, list) or not rows:
    fail("execution_plane_baseline.json must contain a non-empty features array")

required_fields = set(execution_schema.get("required", []))
planes = set(execution_schema["properties"]["primary_plane"]["enum"])
disabled_cost_policies = set(
    execution_schema["properties"]["disabled_cost_policy"]["enum"]
)
feature_pattern = re.compile(execution_schema["properties"]["feature_id"]["pattern"])
kpi_pattern = re.compile(
    execution_schema["properties"]["regression_kpis"]["items"]["pattern"]
)
kpi_ids = {row["id"] for row in kpi_catalog.get("kpis", [])}
if not kpi_ids:
    fail("kpi_catalog.json must contain KPI IDs")

feature_ids = []
for row in rows:
    feature_id = row.get("feature_id", "<missing feature_id>")
    missing = sorted(required_fields - set(row))
    if missing:
        fail(f"{feature_id}: missing required execution-plane fields: {missing}")
    if row["api_version"] != execution_schema["properties"]["api_version"]["const"]:
        fail(f"{feature_id}: unexpected api_version {row['api_version']!r}")
    if not feature_pattern.fullmatch(row["feature_id"]):
        fail(f"{feature_id}: feature_id does not match schema pattern")
    if row["primary_plane"] not in planes:
        fail(f"{feature_id}: invalid primary_plane {row['primary_plane']!r}")
    if not isinstance(row["optional"], bool):
        fail(f"{feature_id}: optional must be a boolean")
    if row["normal_verify_dependency"] is not False:
        fail(f"{feature_id}: normal_verify_dependency must be false")
    if row["disabled_cost_policy"] not in disabled_cost_policies:
        fail(
            f"{feature_id}: invalid disabled_cost_policy "
            f"{row['disabled_cost_policy']!r}"
        )

    allowed_consuming_planes = row.get("allowed_consuming_planes", [])
    if len(allowed_consuming_planes) != len(set(allowed_consuming_planes)):
        fail(f"{feature_id}: duplicate allowed_consuming_planes")
    unknown_planes = sorted(set(allowed_consuming_planes) - planes)
    if unknown_planes:
        fail(f"{feature_id}: unknown allowed_consuming_planes: {unknown_planes}")
    if row["primary_plane"] in {"external_service", "research_only"}:
        if "kernel" in allowed_consuming_planes or "checker" in allowed_consuming_planes:
            fail(f"{feature_id}: external/research feature may not feed kernel/checker")

    artifact_outputs = row.get("allowed_artifact_outputs", [])
    if len(artifact_outputs) != len(set(artifact_outputs)):
        fail(f"{feature_id}: duplicate allowed_artifact_outputs")

    regression_kpis = row.get("regression_kpis", [])
    for kpi in regression_kpis:
        if not kpi_pattern.fullmatch(kpi):
            fail(f"{feature_id}: invalid KPI format {kpi!r}")
    missing_kpis = sorted(set(regression_kpis) - kpi_ids)
    if missing_kpis:
        fail(f"{feature_id}: regression KPI IDs missing from catalog: {missing_kpis}")

    budgets = row.get("budgets", {})
    if not isinstance(budgets, dict):
        fail(f"{feature_id}: budgets must be an object")
    for key, value in budgets.items():
        if not isinstance(value, int) or value < 0:
            fail(f"{feature_id}: budget {key!r} must be a non-negative integer")

    feature_ids.append(row["feature_id"])

if len(feature_ids) != len(set(feature_ids)):
    fail("execution_plane_baseline.json contains duplicate feature_id values")

if EXECUTION_BASELINE_CSV.exists():
    with EXECUTION_BASELINE_CSV.open(newline="") as csv_file:
        csv_ids = [row["feature_id"] for row in csv.DictReader(csv_file)]
    if csv_ids != feature_ids:
        fail("execution_plane_baseline.csv feature IDs differ from JSON feature IDs")

print(f"execution_plane_features={len(feature_ids)}")

if BENCHMARK_TAXONOMY_JSON.exists() != BENCHMARK_TAXONOMY_CSV.exists():
    fail("benchmark taxonomy JSON and CSV must be added together")

if BENCHMARK_TAXONOMY_JSON.exists():
    benchmark_taxonomy = parsed_json.get(BENCHMARK_TAXONOMY_JSON) or load_json(
        BENCHMARK_TAXONOMY_JSON
    )
    benchmark_rows = benchmark_taxonomy.get("benchmarks")
    if not isinstance(benchmark_rows, list) or not benchmark_rows:
        fail("benchmark_taxonomy.json must contain a non-empty benchmarks array")

    required_benchmark_fields = {
        "benchmark_id",
        "suite",
        "inputs",
        "commands",
        "measured_kpis",
        "primary_execution_plane",
        "optional_feature_state",
        "expected_gate",
        "lifecycle",
        "normal_authoring_hot_path",
    }
    required_suites = {
        "micro",
        "induction",
        "algebra/library",
        "solver",
        "multi-file",
        "authoring-loop",
        "research",
        "core-performance",
    }
    required_core_kpis = {f"KPI-{i:03d}" for i in range(31, 39)}
    allowed_lifecycles = {
        "PUA-M00 baseline-only",
        "later PUA-M13 harness work",
        "release/high-trust work",
    }
    benchmark_ids = []
    benchmark_suites = set()
    for row in benchmark_rows:
        benchmark_id = row.get("benchmark_id", "<missing benchmark_id>")
        missing = sorted(required_benchmark_fields - set(row))
        if missing:
            fail(f"{benchmark_id}: missing benchmark taxonomy fields: {missing}")
        if row["primary_execution_plane"] not in planes:
            fail(
                f"{benchmark_id}: invalid primary_execution_plane "
                f"{row['primary_execution_plane']!r}"
            )
        if row["lifecycle"] not in allowed_lifecycles:
            fail(f"{benchmark_id}: invalid lifecycle {row['lifecycle']!r}")
        if not isinstance(row["normal_authoring_hot_path"], bool):
            fail(f"{benchmark_id}: normal_authoring_hot_path must be a boolean")
        for list_key in ["inputs", "commands", "measured_kpis"]:
            if not isinstance(row[list_key], list) or not row[list_key]:
                fail(f"{benchmark_id}: {list_key} must be a non-empty array")
        missing_kpis = sorted(set(row["measured_kpis"]) - kpi_ids)
        if missing_kpis:
            fail(f"{benchmark_id}: measured KPI IDs missing from catalog: {missing_kpis}")

        command_text = "\n".join(row["commands"])
        if row["normal_authoring_hot_path"] and (
            "check-corpus-package.sh" in command_text
            or "check-corpus-full.sh" in command_text
        ):
            fail(
                f"{benchmark_id}: package/full corpus gates cannot be normal "
                "authoring hot-path checks"
            )
        benchmark_ids.append(row["benchmark_id"])
        benchmark_suites.add(row["suite"])

    if len(benchmark_ids) != len(set(benchmark_ids)):
        fail("benchmark_taxonomy.json contains duplicate benchmark_id values")

    missing_suites = sorted(required_suites - benchmark_suites)
    if missing_suites:
        fail(f"benchmark_taxonomy.json missing required suites: {missing_suites}")

    core_rows = [
        row
        for row in benchmark_rows
        if row["suite"] == "core-performance"
        or row["benchmark_id"] == "bench.core_performance"
    ]
    core_kpis = {kpi for row in core_rows for kpi in row["measured_kpis"]}
    missing_core_kpis = sorted(required_core_kpis - core_kpis)
    if missing_core_kpis:
        fail(
            "benchmark_taxonomy.json core-performance rows missing KPI coverage: "
            f"{missing_core_kpis}"
        )

    if BENCHMARK_TAXONOMY_CSV.exists():
        with BENCHMARK_TAXONOMY_CSV.open(newline="") as csv_file:
            csv_ids = [row["benchmark_id"] for row in csv.DictReader(csv_file)]
        if csv_ids != benchmark_ids:
            fail("benchmark_taxonomy.csv benchmark IDs differ from JSON benchmark IDs")

    print(f"benchmark_taxonomy_entries={len(benchmark_ids)}")

if GOLDEN_CORPUS_JSON.exists() != GOLDEN_CORPUS_CSV.exists():
    fail("golden corpus manifest JSON and CSV must be added together")

if GOLDEN_CORPUS_JSON.exists():
    golden_manifest = parsed_json.get(GOLDEN_CORPUS_JSON) or load_json(
        GOLDEN_CORPUS_JSON
    )
    golden_cases = golden_manifest.get("cases")
    if not isinstance(golden_cases, list) or not golden_cases:
        fail("golden_corpus_manifest.json must contain a non-empty cases array")

    required_case_fields = {
        "case_id",
        "kind",
        "paths",
        "gate",
        "stable_reason",
    }
    required_case_kinds = {
        "positive_certificate",
        "rejected_artifact",
        "deterministic_hash",
        "source_free_replay",
    }
    case_ids = []
    case_kinds = set()
    for row in golden_cases:
        case_id = row.get("case_id", "<missing case_id>")
        missing = sorted(required_case_fields - set(row))
        if missing:
            fail(f"{case_id}: missing golden corpus fields: {missing}")
        if row["kind"] not in required_case_kinds:
            fail(f"{case_id}: invalid golden corpus kind {row['kind']!r}")
        if not isinstance(row["paths"], list) or not row["paths"]:
            fail(f"{case_id}: paths must be a non-empty array")
        if not isinstance(row["gate"], str) or not row["gate"].strip():
            fail(f"{case_id}: gate must be a non-empty string")
        if not isinstance(row["stable_reason"], str) or not row["stable_reason"].strip():
            fail(f"{case_id}: stable_reason must be a non-empty string")

        declared_paths = {
            str(checked_relative_path(path, case_id, "paths")) for path in row["paths"]
        }

        kind = row["kind"]
        if kind == "positive_certificate":
            certificate_path = checked_relative_path(
                row.get("certificate_path", ""), case_id, "certificate_path"
            )
            if certificate_path.suffix != ".npcert":
                fail(f"{case_id}: positive certificate must point at a .npcert")
            if str(certificate_path) not in declared_paths:
                fail(f"{case_id}: certificate_path must also appear in paths")
            if not is_git_tracked(certificate_path):
                fail(f"{case_id}: positive certificate must be checked in")

        if kind == "source_free_replay":
            module = row.get("module")
            certificate_path = checked_relative_path(
                row.get("certificate_path", ""), case_id, "certificate_path"
            )
            replay_path = checked_relative_path(
                row.get("replay_path", ""), case_id, "replay_path"
            )
            if certificate_path.suffix != ".npcert":
                fail(f"{case_id}: source-free certificate must point at a .npcert")
            if replay_path.name != "replay.json":
                fail(f"{case_id}: source-free replay must point at replay.json")
            if str(certificate_path) not in declared_paths:
                fail(f"{case_id}: certificate_path must also appear in paths")
            if str(replay_path) not in declared_paths:
                fail(f"{case_id}: replay_path must also appear in paths")
            for path in [certificate_path, replay_path]:
                if not is_git_tracked(path):
                    fail(f"{case_id}: source-free replay pair must be checked in")

            replay = load_json(replay_path)
            if replay.get("module") != module:
                fail(f"{case_id}: replay module does not match manifest module")
            accepted_artifact = replay.get("acceptance", {}).get("accepted_artifact")
            expected_artifact = row.get("accepted_artifact")
            if not isinstance(accepted_artifact, str) or not isinstance(
                expected_artifact, str
            ):
                fail(f"{case_id}: replay accepted_artifact must be a string")
            if accepted_artifact != expected_artifact:
                fail(f"{case_id}: replay accepted_artifact does not match manifest")
            if Path("proofs") / accepted_artifact != certificate_path:
                fail(f"{case_id}: replay accepted_artifact does not match certificate")

        if kind == "deterministic_hash":
            hash_fixture_path = checked_relative_path(
                row.get("hash_fixture_path", ""), case_id, "hash_fixture_path"
            )
            if str(hash_fixture_path) not in declared_paths:
                fail(f"{case_id}: hash_fixture_path must also appear in paths")
            if hash_fixture_path != Path(
                "crates/npa-cert/tests/fixtures/golden_hashes.tsv"
            ):
                fail(f"{case_id}: deterministic hash case must reference golden_hashes.tsv")
            if not is_git_tracked(hash_fixture_path):
                fail(f"{case_id}: deterministic hash fixture must be checked in")

        if kind == "rejected_artifact":
            artifact_path = checked_relative_path(
                row.get("artifact_path", ""), case_id, "artifact_path"
            )
            if str(artifact_path) not in declared_paths:
                fail(f"{case_id}: artifact_path must also appear in paths")
            if artifact_path.parts[:1] == ("proofs",):
                fail(f"{case_id}: rejected artifact fixture must not live under proofs/**")
            golden_fixture_root = PUA_ROOT / "fixtures" / "golden"
            try:
                artifact_path.relative_to(golden_fixture_root)
            except ValueError:
                fail(
                    f"{case_id}: rejected artifact fixture must live under "
                    "develop/proof-using-agents/fixtures/golden/"
                )
            expected_rejection = row.get("expected_rejection")
            if not isinstance(expected_rejection, str) or not expected_rejection.strip():
                fail(f"{case_id}: rejected artifact must state expected_rejection")

        case_ids.append(row["case_id"])
        case_kinds.add(kind)

    if len(case_ids) != len(set(case_ids)):
        fail("golden_corpus_manifest.json contains duplicate case_id values")

    missing_kinds = sorted(required_case_kinds - case_kinds)
    if missing_kinds:
        fail(f"golden_corpus_manifest.json missing required kinds: {missing_kinds}")

    if GOLDEN_CORPUS_CSV.exists():
        with GOLDEN_CORPUS_CSV.open(newline="") as csv_file:
            csv_rows = list(csv.DictReader(csv_file))
        csv_ids = [row["case_id"] for row in csv_rows]
        if csv_ids != case_ids:
            fail("golden_corpus_manifest.csv case IDs differ from JSON case IDs")
        json_kinds = {row["case_id"]: row["kind"] for row in golden_cases}
        for csv_row in csv_rows:
            case_id = csv_row["case_id"]
            if csv_row.get("kind") != json_kinds[case_id]:
                fail(f"{case_id}: CSV kind differs from JSON kind")
            csv_paths = [path for path in csv_row.get("paths", "").split(";") if path]
            if not csv_paths:
                fail(f"{case_id}: CSV paths must be non-empty")
            for path in csv_paths:
                checked_relative_path(path, case_id, "csv.paths")

    print(f"golden_corpus_cases={len(case_ids)}")

print("proof-agent baseline validation passed")
PY
