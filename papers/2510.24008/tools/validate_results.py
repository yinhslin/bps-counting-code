#!/usr/bin/env python3
"""Audit the supplied scan and exact rank of the stored Cartan-image matrices.

This checks existing artifacts. It does not regenerate the full Q complex.
Only the Python standard library is required.
"""
import argparse
import csv
from fractions import Fraction
import hashlib
import json
import os
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
FIELDS = ["level","nz1","nz2","nt1","nt2","nt3","degree","N","cohomology","monotone"]
FILE_PATTERN = re.compile(r"\d+(?:_\d+){7}\.csv")


def read_rows(path):
    with path.open(newline="") as f:
        return [list(map(int,row)) for row in csv.reader(f)]


def expected_sectors(max_level=18):
    expected = set()
    for a in range(max_level//3+1):
        for b in range(a,max_level//3+1):
            for c in range(max_level//2+1):
                for d in range(c,max_level//2+1):
                    for e in range(d,max_level//2+1):
                        level = 3*(a+b)+2*(c+d+e)
                        if 1 <= level <= max_level:
                            for n in range(2,a+b+c+d+e+1):
                                expected.add((level,a,b,c,d,e,n))
    return expected


def exact_sparse_rank(path, nrows, ncols):
    rows = [{} for _ in range(nrows)]
    with path.open(newline="") as f:
        for x in csv.DictReader(f):
            i,j = int(x["row"])-1,int(x["column"])-1
            assert 0 <= i < nrows and 0 <= j < ncols
            assert j not in rows[i], "Duplicate coordinate"
            v = Fraction(int(x["numerator"]),int(x["denominator"]))
            if v:
                rows[i][j] = v
    pivots = {}
    for row in rows:
        while row:
            p = min(row)
            if p not in pivots:
                factor = row[p]
                pivots[p] = {j:v/factor for j,v in row.items()}
                break
            factor = row[p]
            for j,v in pivots[p].items():
                value = row.get(j,Fraction(0))-factor*v
                if value:
                    row[j] = value
                else:
                    row.pop(j,None)
    return len(pivots)


def audit(root=ROOT, write=False, data_root=None):
    data_root = Path(data_root or os.environ.get("BPS_DATA_ROOT", root/"data")).expanduser().resolve()
    raw = data_root/"raw"
    derived = data_root/"derived"
    if not (raw/"manifest.json").is_file():
        raise FileNotFoundError(
            f"No result manifest under {data_root}. Pass --data-root pointing to "
            "bps-counting/2510.24008/data, or set BPS_DATA_ROOT.")
    manifest = json.loads((raw/"manifest.json").read_text())
    for entry in manifest["files"]:
        b=(raw/entry["path"]).read_bytes()
        assert len(b)==entry["bytes"] and hashlib.sha256(b).hexdigest()==entry["sha256"], entry["path"]
    expected=expected_sectors()
    scans={}; summaries={}; recovery=[]; all_rows=[]
    for group,nn in [("so",7),("sp",6)]:
        base=raw/f"bps_{group}/all"
        total=read_rows(base/"cohomology"/f"total-{group}.csv")
        assert all(len(row)==10 for row in total)
        scan={tuple(row[:7]):row for row in total}
        assert len(scan)==len(total), "Duplicate aggregate rows"
        assert set(scan)==expected, "Missing or unexpected scan sectors"
        assert all(r[7]==nn and 0<=r[9]<=r[8] for r in total)
        singles={}
        for file in (base/"cohomology").glob("*.csv"):
            if not FILE_PATTERN.fullmatch(file.name):
                continue
            row,=read_rows(file)
            assert row[:8]==list(map(int,file.stem.split("_"))),file
            assert row==scan[tuple(row[:7])],file
            singles[tuple(row[:7])]=row
        counts={}
        for file in (base/"count").glob("*.csv"):
            if not FILE_PATTERN.fullmatch(file.name):
                continue
            row,=read_rows(file)
            assert len(row)==3 and min(row)>=0,file
            key=tuple(map(int,file.stem.split("_")))
            assert key[-1]==nn
            counts[key[:7]]=row
        compared=0
        for key,row in scan.items():
            previous=(*key[:6],key[6]-1)
            if key in counts and previous in counts:
                assert row[8:]==[counts[key][0]-counts[previous][1],counts[previous][2]],key
                compared+=1
        for key in sorted(expected-set(singles)):
            previous=(*key[:6],key[6]-1)
            assert key in counts and previous in counts, "Missing record without count evidence"
            backup=base/"cohomology"/("_".join(map(str,(*key,nn)))+"-bk.csv")
            assert read_rows(backup)==[scan[key]],"Backup does not agree"
            recovery.append({"group":group,"sector":list(key),"cohomology":scan[key][8],
                             "monotone":scan[key][9],"evidence":[str(backup.relative_to(raw)),
                             f"bps_{group}/all/cohomology/total-{group}.csv"],
                             "method":"Aggregate row agrees with backup and consecutive-degree count formula"})
        for key in sorted(scan):
            all_rows.append([group,*scan[key]])
        scans[group]=scan
        summaries[group]={"aggregate_sectors":len(scan),"individual_sector_files":len(singles),
                          "rows_cross_checked_with_counts":compared,
                          "fortuitous_sectors":[r for r in total if r[8]!=r[9]]}
    differences=[]
    for key in sorted(expected):
        a,b=scans["so"][key],scans["sp"][key]
        if a[8:]!=b[8:]:
            differences.append({"sector":list(key),"so":a[8:],"sp":b[8:]})
    assert differences==[
        {"sector":[18,0,0,3,3,3,8],"so":[124,123],"sp":[123,123]},
        {"sector":[18,1,1,2,2,2,8],"so":[85,85],"sp":[84,84]}]
    cartan=[]
    for entry in json.loads((derived/"cartan_exports.json").read_text()):
        assert hashlib.sha256((raw/entry["source"]).read_bytes()).hexdigest()==entry["source_sha256"]
        rank=exact_sparse_rank(derived/f"cartan_{entry['group']}_matrix.csv",entry["rows"],entry["columns"])
        assert rank==entry["exact_stored_matrix_rank"]==84
        cartan.append({"group":entry["group"],"exact_stored_matrix_rank":rank})
    table=[]
    expected_table=[(903,559,220,123,1),(903,559,221,123,0),
                    (826,741,0,85,0),(825,741,0,84,0)]
    for source,expected_row in zip(json.loads((data_root/"table_I_sources.json").read_text()),expected_table,strict=True):
        text=(raw/source["raw_log"]).read_text()
        values={k:int(v) for k,v in re.findall(r"^(all|exact|nonclosed|grav|cohomology|graviton cohomology): (\d+)$",text,re.M)}
        assert values==source["values"]
        assert f"{{{', '.join(map(str,source['charges']))}}}" in text and "degree 8/" in text
        mono=values["grav"]-values["exact"]
        coho=values["all"]-values["exact"]-values["nonclosed"]
        assert coho==values["cohomology"] and mono==values["graviton cohomology"]
        assert (values["all"],values["exact"],values["nonclosed"],mono,coho-mono)==expected_row
        key=(18,*source["charges"],8)
        assert scans[source["group"]][key][8:]==[coho,mono]
        table.append([source["group"],18,*source["charges"],8,values["all"],
                      values["nonclosed"],values["exact"],mono,coho-mono,coho,source["raw_log"]])
    report={"status":"passed","raw_files_sha256_verified":len(manifest["files"]),
            "expected_sectors_per_group":len(expected),"scan":summaries,"differences":differences,
            "recovered_aggregate_record":recovery,"cartan":cartan,
            "full_q_complex_recomputed":False,"table_I_all_exact_nonclosed_basis_dimensions_reloaded":False,
            "table_I_counts_cross_checked_with_cluster_logs":True,
            "scope":"Checks supplied CSVs and exact rank of stored Cartan-image bases; not an independent reproduction of the large calculation"}
    if write:
        with (derived/"cohomology_scan.csv").open("w",newline="") as f:
            w=csv.writer(f);w.writerow(["group",*FIELDS]);w.writerows(all_rows)
        (derived/"validation.json").write_text(json.dumps(report,indent=2)+"\n")
        with (derived/"table_I.csv").open("w",newline="") as f:
            w=csv.writer(f);w.writerow(["group","level","nz1","nz2","nt1","nt2","nt3","degree",
                "all","nonclosed","exact","monotone","fortuitous","cohomology","source_log"]);w.writerows(table)
    return report


if __name__=="__main__":
    p=argparse.ArgumentParser(description=__doc__);p.add_argument("--write",action="store_true")
    p.add_argument("--data-root",type=Path,help="Directory containing raw/ and derived/; defaults to BPS_DATA_ROOT or the bundled data/")
    args=p.parse_args()
    print(json.dumps(audit(write=args.write,data_root=args.data_root),indent=2))
