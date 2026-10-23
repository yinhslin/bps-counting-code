import csv
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0,str(Path(__file__).resolve().parents[1]/"tools"))
from split_mtx import split_matrix
from validate_results import exact_sparse_rank, audit


class ReleaseChecks(unittest.TestCase):
    def test_supplied_results(self):
        self.assertEqual(audit()["status"],"passed")

    def test_split_preserves_comments_dimensions_and_entries(self):
        with tempfile.TemporaryDirectory() as t:
            base=Path(t);f=base/"matrix.mtx"
            data=["1 1 2","2 2 -3","2 3 4"]
            f.write_text("%%MatrixMarket matrix coordinate integer general\n% a comment\n2 3 3\n"+"\n".join(data))
            self.assertEqual(split_matrix(f,base/"parts",2),3)
            parts=sorted((base/"parts").iterdir());collected=[]
            for p in parts:
                lines=p.read_text().splitlines()
                self.assertEqual(lines[0],"%%MatrixMarket matrix coordinate integer general")
                m,n,nnz=map(int,lines[1].split());self.assertEqual((m,n),(2,3))
                self.assertEqual(nnz,len(lines)-2);collected+=lines[2:]
            self.assertEqual(collected,data)

    def test_split_rejects_incomplete_matrix(self):
        with tempfile.TemporaryDirectory() as t:
            base=Path(t);f=base/"bad.mtx"
            f.write_text("%%MatrixMarket matrix coordinate real general\n2 2 2\n1 1 1\n")
            with self.assertRaises(ValueError):split_matrix(f,base/"parts",2)

    def test_rank_uses_exact_rationals(self):
        with tempfile.TemporaryDirectory() as t:
            p=Path(t)/"matrix.csv"
            p.write_text("row,column,numerator,denominator\n1,1,1,3\n1,2,1,7\n2,1,2,3\n2,2,2,7\n3,3,1,100000000000000000000\n")
            self.assertEqual(exact_sparse_rank(p,3,3),2)


if __name__=="__main__":unittest.main()
