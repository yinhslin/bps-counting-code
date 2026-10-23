(* Export the two stored Cartan-image bases; this does not recompute the restriction map. *)
$HistoryLength=0;
releaseRoot=DirectoryName[DirectoryName[$InputFileName]];
dataRoot=Environment["BPS_DATA_ROOT"];
If[!StringQ[dataRoot] || dataRoot=="",dataRoot=FileNameJoin[{releaseRoot,"data"}]];
dataRoot=ExpandFileName[dataRoot];
If[!FileExistsQ[FileNameJoin[{dataRoot,"raw","manifest.json"}]],
 Print["Missing result data. Set BPS_DATA_ROOT to the directory containing raw/ and derived/."];Exit[2]];
out=FileNameJoin[{dataRoot,"derived"}];
If[!DirectoryQ[out],CreateDirectory[out,CreateIntermediateDirectories->True]];
records={};
Do[
 ClearAll[reducedGraviton];
 nn=If[group=="so",7,6];
 relative=StringRiffle[{"bps_"<>group,"all","reducedgraviton","18_1_1_2_2_2_8_"<>ToString[nn]<>".mx"},"/"];
 input=FileNameJoin[{dataRoot,"raw",relative}];
 Check[Get[input],Exit[1]];
 value=reducedGraviton[{1,1,2,2,2},8,nn];
 If[Length[value]!=2 || Dimensions[value[[1]]]!={84,492},Print["Unexpected basis shape"];Exit[1]];
 (* Rationalize[...,0] exactly represents stored numbers, with no fitted tolerance. *)
 matrix=Rationalize[SparseArray[value[[1]]],0];
 rules=Most[ArrayRules[matrix]];
 rows=({#[[1,1]],#[[1,2]],Numerator[#[[2]]],Denominator[#[[2]]]}&/@rules);
 Export[FileNameJoin[{out,"cartan_"<>group<>"_matrix.csv"}],
  Prepend[rows,{"row","column","numerator","denominator"}],"CSV"];
 Put[value[[2]],FileNameJoin[{out,"cartan_"<>group<>"_monomials.wl"}]];
 exactRank=MatrixRank[matrix];
 AppendTo[records,<|"group"->group,"N"->nn,"charges"->{1,1,2,2,2},"degree"->8,
  "source"->relative,"source_sha256"->FileHash[input,"SHA256","HexString"],
  "rows"->84,"columns"->492,"nonzero_entries"->Length[rows],"exact_stored_matrix_rank"->exactRank,
  "number_representation"->"Exact rational values of stored coefficients; Rationalize[x,0]",
  "wolfram_version"->$Version|>];
 Print[group,": ",exactRank];
,{group,{"so","sp"}}];
Export[FileNameJoin[{out,"cartan_exports.json"}],records,"RawJSON"];
Exit[0];
