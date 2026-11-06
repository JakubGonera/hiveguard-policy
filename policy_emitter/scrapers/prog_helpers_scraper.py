"""Scrape https://github.com/isovalent/ebpf-docs's helpers-functions.yaml and
emit a JSON file mapping each helper function to the BPF program types that
can call it. Group references in the YAML are resolved recursively and
`exclude` directives are applied.
"""

import json
import sys
import urllib.request

import yaml

SOURCE_URL = (
    "https://raw.githubusercontent.com/isovalent/ebpf-docs/master/"
    "data/helpers-functions.yaml"
)
OUTPUT_PATH = "docs_helper_callers.json"


def fetch_yaml(url: str) -> dict:
    with urllib.request.urlopen(url) as resp:
        return yaml.safe_load(resp.read())


def resolve_group(name: str, groups: dict, seen: set[str]) -> list[dict]:
    if name in seen:
        raise ValueError(f"Cyclic group reference involving {name}")
    if name not in groups:
        print(f"warning: group '{name}' referenced but not defined", file=sys.stderr)
        return []
    seen = seen | {name}
    return expand_entries(groups[name], groups, seen)


def expand_entries(entries: list[dict], groups: dict, seen: set[str]) -> list[dict]:
    """Expand a list of YAML entries into a flat list of helper dicts.

    Each entry is one of:
      - {'name': <helper>, ...metadata}   -> kept as-is
      - {'group': <group>, ...metadata}   -> recursively inlined; per-reference
                                             metadata (e.g. attach_type) is
                                             merged onto every helper of the
                                             expanded group
      - {'exclude': <helper>}             -> handled by the caller
    """
    out = []
    for entry in entries:
        if "group" in entry:
            ref_meta = {k: v for k, v in entry.items() if k != "group"}
            expanded = resolve_group(entry["group"], groups, seen)
            for helper in expanded:
                merged = dict(helper)
                for k, v in ref_meta.items():
                    merged.setdefault(k, v)
                out.append(merged)
        else:
            out.append(entry)
    return out


def build_program_map(doc: dict) -> dict[str, list[dict]]:
    groups = doc.get("groups", {}) or {}
    programs = doc.get("programs", {}) or {}

    result: dict[str, list[dict]] = {}
    for prog_type, entries in programs.items():
        entries = entries or []
        helpers = []
        excludes = set()
        for entry in entries:
            if "exclude" in entry:
                excludes.add(entry["exclude"])
            elif "group" in entry:
                helpers.extend(expand_entries([entry], groups, set()))
            elif "name" in entry:
                helpers.append(entry)
            else:
                print(f"warning: skipping unknown entry {entry!r} in {prog_type}", file=sys.stderr)

        # Apply excludes and de-duplicate by name (first occurrence wins so
        # the program-specific metadata takes precedence over the group's).
        seen_names: set[str] = set()
        filtered: list[dict] = []
        for helper in helpers:
            name = helper.get("name")
            if name is None or name in excludes or name in seen_names:
                continue
            seen_names.add(name)
            filtered.append(helper)
        result[prog_type] = filtered
    return result


def invert(prog_map: dict[str, list[dict]]) -> dict[str, list[dict]]:
    """Invert program->helpers into helper->programs, preserving per-(helper,
    program) metadata (kconfig, cap, since, ...) on the program entries.
    """
    helper_map: dict[str, list[dict]] = {}
    for prog_type, helpers in prog_map.items():
        for helper in helpers:
            name = helper["name"]
            entry = {"program": prog_type}
            for k, v in helper.items():
                if k != "name":
                    entry[k] = v
            helper_map.setdefault(name, []).append(entry)
    return dict(sorted(helper_map.items()))


def main() -> None:
    doc = fetch_yaml(SOURCE_URL)
    prog_map = build_program_map(doc)
    helper_map = invert(prog_map)
    with open(OUTPUT_PATH, "w") as f:
        json.dump(helper_map, f, indent=2, sort_keys=False)
        f.write("\n")
    total = sum(len(v) for v in helper_map.values())
    print(f"wrote {OUTPUT_PATH}: {len(helper_map)} helpers, {total} (helper, program) pairs")


if __name__ == "__main__":
    main()
