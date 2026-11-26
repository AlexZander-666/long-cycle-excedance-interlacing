#!/usr/bin/env python3
"""Calculate additional swap for a serial Lean job while reserving build space."""

import argparse
from pathlib import Path
import shutil

KIB_PER_GIB = 1024**2
ADDITIONAL_SWAP_LIMIT = 14
PROFILES = {
    "FixedCutoffCubeAudit": (10, 15),
    "FixedThreeAllAudit": (20, 20),
    "FixedFourAllAudit": (20, 20),
    "CutoffFiveFinalAudit": (12, 12),
}


def additional_swap(audit, ram_kib, swap_kib, free_kib):
    memory_target, disk_reserve = PROFILES[audit]
    missing = max(0, memory_target * KIB_PER_GIB - ram_kib - swap_kib)
    extra = (missing + KIB_PER_GIB - 1) // KIB_PER_GIB
    if extra > ADDITIONAL_SWAP_LIMIT:
        raise ValueError(f"{audit} requires more than {ADDITIONAL_SWAP_LIMIT} GiB of additional swap")
    if free_kib < (extra + disk_reserve) * KIB_PER_GIB:
        raise ValueError(f"{audit} needs {disk_reserve} GiB for Lean and dependencies, "
                         f"plus {extra} GiB of additional swap")
    return extra


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("audit", choices=PROFILES)
    parser.add_argument("build_disk", type=Path)
    args = parser.parse_args()
    meminfo = dict((key, int(value.split()[0]))
                   for key, value in (line.split(":", 1)
                                      for line in Path("/proc/meminfo").read_text().splitlines()))
    try:
        print(additional_swap(args.audit, meminfo["MemTotal"], meminfo["SwapTotal"],
                              shutil.disk_usage(args.build_disk).free // 1024))
    except ValueError as exc:
        parser.exit(1, f"{exc}\nUse a larger runner or free space on the build disk.\n")


if __name__ == "__main__":
    main()
