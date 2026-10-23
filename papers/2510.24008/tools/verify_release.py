#!/usr/bin/env python3
"""Verify all files listed in the release manifest using Python's standard library."""
from pathlib import Path
import hashlib
import json

ROOT=Path(__file__).resolve().parents[1]

if __name__=="__main__":
    data=json.loads((ROOT/"release_manifest.json").read_text())
    for entry in data["files"]:
        path=(ROOT/entry["path"]).resolve()
        assert ROOT in path.parents, "Invalid manifest path"
        content=path.read_bytes()
        assert len(content)==entry["bytes"],entry["path"]
        assert hashlib.sha256(content).hexdigest()==entry["sha256"],entry["path"]
    print(f"Verified {len(data['files'])} release files.")
