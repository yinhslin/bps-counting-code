(* One stage per fresh kernel. Invoke through tools/run.py. *)
$HistoryLength = 0;
sourceDirectory = DirectoryName[$InputFileName];
cfg = Import[Environment["BPS_JOB_CONFIG"], "RawJSON"];
If[!AssociationQ[cfg], Print["Invalid job configuration"]; Exit[2]];
NN = cfg["N"]; charges = cfg["charges"]; degree = cfg["degree"];
job = cfg["stage"]; numerical = cfg["numerical"];
soQ = cfg["group"] === "so"; spQ = cfg["group"] === "sp";
specialQ = True; schurQ = False; su121Q = False; su122Q = False;
minDeg = 2; maxDeg = Total[charges]; levelvector = {3,3,2,2,2};
level = charges . levelvector; time = cfg["time_limit"];
numKernels = cfg["kernels"]; chunk = 1000; memory = 1000;
MyShare[] := 0;
dataDirectoryRoot = FileNameJoin[{cfg["data_root"], "bps_"<>cfg["group"], "all"}];
stages = <|"singletrace"->"singletrace", "singlegraviton"->"singlegraviton",
  "multitrace"->"multitrace", "multigraviton"->"multigraviton",
  "independentoperator"->"independentoperator", "exact"->"exact",
  "independentexact"->"independentexact", "independentgraviton"->"independentgraviton",
  "reducedgrav"->"reducedgraviton", "reducedexact"->"reducedexact",
  "cohomologyC"->"cohomology", "countC"->"count"|>;
If[!KeyExistsQ[stages,job] || !MemberQ[{True,False},numerical] ||
   !VectorQ[charges, IntegerQ] || Length[charges]!=5 || Min[charges]<0 ||
   !IntegerQ[degree] || !IntegerQ[NN] || NN<2 || !(soQ || spQ) || (spQ && OddQ[NN]), Exit[2]];
If[$SystemWordLength != 64, Print["A 64-bit Wolfram kernel is required"]; Exit[2]];
pathFor[d_] := FileNameJoin[{dataDirectoryRoot,d}]<>$PathnameSeparator;
necklaceDirectory = pathFor["necklace"];
singleDirectory = pathFor["singletrace"]; singleGravitonDirectory = pathFor["singlegraviton"];
multiDirectory = pathFor["multitrace"]; multiGravitonDirectory = pathFor["multigraviton"];
operatorDirectory = pathFor["independentoperator"]; exactDirectory = pathFor["exact"];
indExactDirectory = pathFor["independentexact"]; indGravitonDirectory = pathFor["independentgraviton"];
reducedGravitonDirectory = pathFor["reducedgraviton"]; reducedExactDirectory = pathFor["reducedexact"];
cohomologyDirectory = pathFor["cohomology"]; countDirectory = pathFor["count"];
juliaDirectory = pathFor["julia"]; multiTraceChargeListDirectory = pathFor["multitracechargelist"];
Do[If[!DirectoryQ[pathFor[d]],CreateDirectory[pathFor[d],CreateIntermediateDirectories->True]],
 {d,DeleteDuplicates[Join[Values[stages],{"necklace","julia","multitracechargelist"}]]}];
stem[n_] := StringRiffle[ToString /@ Join[{level},charges,{n,NN}],"_"];
resultPath = pathFor[stages[job]]<>stem[degree]<>If[MemberQ[{"cohomologyC","countC"},job],".csv",".mx"];
If[FileExistsQ[resultPath],Print["Already present: ",resultPath]; Exit[0]];
(* Missing inputs must never be interpreted as an empty vector space. *)
inputs = Switch[job,
 "independentoperator", {{"multitrace",degree}},
 "exact", {{"independentoperator",degree-1}},
 "independentexact", {{"independentoperator",degree-1},{"exact",degree}},
 "independentgraviton", {{"independentexact",degree},{"multigraviton",degree}},
 "reducedgrav", {{"independentgraviton",degree}},
 "reducedexact", {{"independentexact",degree}},
 "cohomologyC", {{"independentoperator",degree},{"independentexact",degree},
                 {"independentexact",degree+1},{"independentgraviton",degree}},
 "countC", {{"independentoperator",degree},{"independentexact",degree+1},{"independentgraviton",degree+1}},
 _, {}];
If[2<=degree<=maxDeg,
 Do[If[!FileExistsQ[pathFor[input[[1]]]<>stem[input[[2]]]<>".mx"],
   Print["Missing input: ",input];Exit[3]],{input,inputs}]];
Quiet[Needs["Combinatorica`"]];
$RecursionLimit = Infinity; $IterationLimit = Infinity;
table = If[numKernels>0,ParallelTable,Table]; do = If[numKernels>0,ParallelDo,Do];
ResetKernels[] := (Print["Stage failed or timed out; no successful result claimed."]; Abort[]);
Check[Get[FileNameJoin[{sourceDirectory,job<>".m"}]],Exit[4]];
If[numKernels>0,
 Check[LaunchKernels[numKernels],Exit[4]];
 If[Length[Kernels[]]!=numKernels,Exit[4]];
 ParallelEvaluate[Quiet[Needs["Combinatorica`"]];$RecursionLimit=Infinity;Stuff[];]];
(* Boundary spaces outside 2 <= n <= total charge are explicitly empty. *)
symbolNames = <|"singletrace"->"singleTrace","singlegraviton"->"singleGraviton",
 "multitrace"->"multiTrace","multigraviton"->"multiGraviton",
 "independentoperator"->"independentOperator","exact"->"exact",
 "independentexact"->"independentExact","independentgraviton"->"independentGraviton",
 "reducedgrav"->"reducedGraviton","reducedexact"->"reducedExact"|>;
started = AbsoluteTime[];
ok = CheckAbort[
 If[(degree<2 || degree>maxDeg) && KeyExistsQ[symbolNames,job],
  emptyValue = If[MemberQ[{"singletrace","singlegraviton","multitrace","multigraviton","exact"},job],{},{{},{}}];
  With[{sym=ToExpression[symbolNames[job]]},sym[charges,degree,NN]=emptyValue;DumpSave[resultPath,sym]],
  Exec[]]; True,
 False];
If[numKernels>0,CloseKernels[]];
If[!TrueQ[ok] || !FileExistsQ[resultPath],Print["Stage did not produce a result"];Exit[5]];
Export[resultPath<>".run.json",<|"stage"->job,"group"->cfg["group"],"N"->NN,
 "charges"->charges,"degree"->degree,"numerical"->numerical,"wolfram_version"->$Version,
 "system_id"->$SystemID,"elapsed_seconds"->N[AbsoluteTime[]-started]|>,"RawJSON"];
Print["Result: ",resultPath];
Exit[0];
