#!/usr/bin/env python3
"""Stream a general coordinate Matrix Market matrix into chunks with identical dimensions."""
import argparse
from pathlib import Path


def split_matrix(source, target, limit):
    if limit < 1:
        raise ValueError("limit must be positive")
    target.mkdir()  # A fresh directory prevents accidental mixing with old chunks.
    with source.open() as stream:
        header = stream.readline().strip()
        fields = header.lower().split()
        if len(fields) != 5 or fields[:3] != ["%%matrixmarket", "matrix", "coordinate"] or fields[4] != "general":
            raise ValueError("Expected a general coordinate Matrix Market matrix")
        line = stream.readline()
        while line.startswith("%") or not line.strip():
            if not line:
                raise ValueError("Missing dimensions")
            line = stream.readline()
        m, n, expected = map(int, line.split())
        if min(m,n,expected) < 0:
            raise ValueError("Negative dimension or record count")
        count = 0
        while count < expected or count == expected == 0:
            amount = min(limit, expected-count)
            path = target/f"part{count//limit+1:06d}.mtx"
            with path.open("w") as out:
                out.write(f"{header}\n{m} {n} {amount}\n")
                written = 0
                while written < amount:
                    line = stream.readline()
                    if not line:
                        raise ValueError("Fewer entries than declared in the header")
                    if line.startswith("%") or not line.strip():
                        continue
                    out.write(line if line.endswith("\n") else line+"\n")
                    written += 1
            count += amount
            if expected == 0:
                break
        if any(line.strip() and not line.startswith("%") for line in stream):
            raise ValueError("More entries than declared in the header")
    return count


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source",type=Path); parser.add_argument("target",type=Path)
    parser.add_argument("limit",type=int)
    args = parser.parse_args()
    print(f"Split {split_matrix(args.source,args.target,args.limit)} entries")
