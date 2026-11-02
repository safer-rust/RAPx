#!/usr/bin/env python3
"""Summarize RAPx verify verdicts and UNKNOWN reasons from captured logs."""

import argparse
import json
import re
from collections import Counter
from pathlib import Path


ANSI = re.compile(r"\x1b\[[0-9;]*m")
TARGET = re.compile(r"\[rapx::verify\] (?:function|sequence|unsafe impl): (.+)$")
VERDICT = re.compile(r"\bresult: (SOUND|UNSOUND|UNKNOWN)\b")
CATEGORY = re.compile(r"\s+- ([a-z_]+): (\d+)\s*$")
DETAIL = re.compile(r"\s+- (.+)$")


def parse_log(path):
    targets = []
    current = None
    section = None
    for raw in path.read_text(errors="replace").splitlines():
        line = ANSI.sub("", raw)
        if match := TARGET.search(line):
            if current is not None:
                targets.append(current)
            current = {
                "name": match.group(1),
                "verdict": None,
                "categories": {},
                "details": [],
            }
            section = None
            continue
        if current is None:
            continue
        if match := VERDICT.search(line):
            current["verdict"] = match.group(1)
        if "unknown categories:" in line:
            section = "categories"
            continue
        if "unsupported operations:" in line:
            section = "details"
            continue
        if section == "categories":
            if match := CATEGORY.search(line):
                current["categories"][match.group(1)] = int(match.group(2))
            elif line.strip():
                section = None
        elif section == "details":
            if match := DETAIL.search(line):
                current["details"].append(match.group(1))
            elif line.strip():
                section = None
    if current is not None:
        targets.append(current)
    return targets


def summarize(path):
    targets = parse_log(path)
    verdicts = Counter(target["verdict"] or "NOT_RUN" for target in targets)
    categories = Counter()
    category_properties = Counter()
    details = Counter()
    for target in targets:
        for category, count in target["categories"].items():
            categories[category] += 1
            category_properties[category] += count
        if target["verdict"] == "UNKNOWN" and not target["categories"]:
            categories["unclassified"] += 1
        details.update(set(target["details"]))
    return {
        "log": str(path),
        "targets": len(targets),
        "verdicts": dict(sorted(verdicts.items())),
        "unknown_target_categories": dict(sorted(categories.items())),
        "unknown_property_categories": dict(sorted(category_properties.items())),
        "unsupported_details": dict(sorted(details.items())),
        "unknown_targets": [
            target for target in targets if target["verdict"] == "UNKNOWN"
        ],
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("logs", nargs="+", type=Path)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    result = [summarize(path) for path in args.logs]
    rendered = json.dumps(result, indent=2, ensure_ascii=False) + "\n"
    if args.output:
        args.output.write_text(rendered)
    else:
        print(rendered, end="")


if __name__ == "__main__":
    main()
