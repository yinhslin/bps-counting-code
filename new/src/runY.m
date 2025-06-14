(* ::Package:: *)

(* ::Section:: *)
(*Input*)


options = $CommandLine;
(*options = {"-N", "2", "-l", "16", "-i", "10", "-d", "5"};*)
param[flag_] := Module[
		{position, flagList}
	, 
		flagList = StringSplit[options];
		position = Position[flagList, "-" <> flag];
		Switch[Length[position], 
			1, If[position[[1, 1]] >= Length[flagList], 
				True, 
				flagList[[position[[1, 1]]+1]][[1]]
				], 
			0, Null, 
			_, WriteString["stdout", "flag -" <> flag <> " duplicated\n"];
				Abort[]
		]
	];

NN = param["N"] // ToExpression;
specialQ = param["u"] // ToExpression;
If[specialQ === Null, specialQ = True, specialQ = False];
soQ = param["so"] // ToExpression;
If[soQ === Null, soQ = False, soQ = True];
spQ = param["sp"] // ToExpression;
If[spQ === Null, spQ = False, spQ = True];
level = param["l"] // ToExpression;
ind = param["i"] // ToExpression;
degree = param["d"] // ToExpression;
time = param["t"] // ToExpression;
If[time === Null, time = Infinity];
numKernels = param["k"] // ToExpression;
perm = param["p"] // ToExpression;
If[perm === Null, perm = False];
job = param["j"];
Print["\n\nBEGIN "<>job<>"\n"];
share = param["s"] // ToExpression;
If[share === Null, share = False];
numerical = param["n"] // ToExpression;
If[numerical === Null, numerical = False, numerical = True];
chunk = param["c"] // ToExpression;
If[chunk === Null, chunk = 10^3];
memory = param["m"] // ToExpression;
If[memory === Null, memory = 10^3];
schurQ = param["sch"] // ToExpression;
If[schurQ === Null, schurQ = False, schurQ = True];
su122Q = param["su122"] // ToExpression;
If[su122Q === Null, su122Q = False, su122Q = True];
su121Q = param["su121"] // ToExpression;
If[su121Q === Null, su121Q = False, su121Q = True];


user = $Username;
home = Switch[user,
	"zhangqim",
		Which[
			spQ,
			GetEnvironment["SCRATCH"][[2]]<>"/bps_sp/"<>Which[schurQ, "schur/", su122Q, "su122/", su121Q, "su121/", True, "all/"],
			soQ,
			GetEnvironment["SCRATCH"][[2]]<>"/bps_so/"<>Which[schurQ, "schur/", su122Q, "su122/", su121Q, "su121/", True, "all/"],
			specialQ,
			GetEnvironment["SCRATCH"][[2]]<>"/bps_su/"<>Which[schurQ, "schur/", su122Q, "su122/", su121Q, "su121/", True, "all/"],
			!specialQ,
			GetEnvironment["SCRATCH"][[2]]<>"/bps_u/"<>Which[schurQ, "schur/", su122Q, "su122/", su121Q, "su121/", True, "all/"]
		]
	,
	"a0s001729",
		Which[
			spQ,
			GetEnvironment["SCRATCH"][[2]]<>"/bps_sp/"<>Which[schurQ, "schur/", su122Q, "su122/", su121Q, "su121/", True, "all/"],
			soQ,
			GetEnvironment["SCRATCH"][[2]]<>"/bps_so/"<>Which[schurQ, "schur/", su122Q, "su122/", su121Q, "su121/", True, "all/"],
			specialQ,
			GetEnvironment["SCRATCH"][[2]]<>"/bps_su/"<>Which[schurQ, "schur/", su122Q, "su122/", su121Q, "su121/", True, "all/"],
			!specialQ,
			GetEnvironment["SCRATCH"][[2]]<>"/bps_u/"<>Which[schurQ, "schur/", su122Q, "su122/", su121Q, "su121/", True, "all/"]
		]
	,
	"a6s001997",
		Which[
			spQ,
			"/public3/home/a6s001997/scratch"<>"/bps_sp/"<>Which[schurQ, "schur/", su122Q, "su122/", su121Q, "su121/", True, "all/"],
			soQ,
			"/public3/home/a6s001997/scratch"<>"/bps_so/"<>Which[schurQ, "schur/", su122Q, "su122/", su121Q, "su121/", True, "all/"],
			specialQ,
			"/public3/home/a6s001997/scratch"<>"/bps_su/"<>Which[schurQ, "schur/", su122Q, "su122/", su121Q, "su121/", True, "all/"],
			!specialQ,
			"/public3/home/a6s001997/scratch"<>"/bps_u/"<>Which[schurQ, "schur/", su122Q, "su122/", su121Q, "su121/", True, "all/"]
		]
	,
	_,
		Which[
			spQ,
			Directory[]<>"/bps_sp/"<>Which[schurQ, "schur/", su122Q, "su122/", su121Q, "su121/", True, "all/"],
			soQ,
			Directory[]<>"/bps_so/"<>Which[schurQ, "schur/", su122Q, "su122/", su121Q, "su121/", True, "all/"],
			specialQ,
			Directory[]<>"/bps_su/"<>Which[schurQ, "schur/", su122Q, "su122/", su121Q, "su121/", True, "all/"],
			!specialQ,
			Directory[]<>"/bps_u/"<>Which[schurQ, "schur/", su122Q, "su122/", su121Q, "su121/", True, "all/"]
		]
];

necklaceDirectory = home <> "necklace/";
singleDirectory = home <> "singletrace/";
multiDirectory = home <> "multitrace/";
singleGravitonDirectory = home <> "singlegraviton/";
multiGravitonDirectory = home <> "multigraviton/";
countDirectory = home <> "count/";
cohomologyDirectory = home <> "cohomology/";
juliaDirectory = home <> "julia/";
hDirectory = home <> "h/";
adDirectory = home <> "ad/";
multiTraceChargeListDirectory = home <> "multitracechargelist/";
directories = {home,necklaceDirectory,singleDirectory,multiDirectory,singleGravitonDirectory,multiGravitonDirectory,countDirectory,cohomologyDirectory,juliaDirectory,hDirectory,adDirectory,multiTraceChargeListDirectory};

On[Assert];

Quiet[<<Combinatorica`];
$RecursionLimit=Infinity;

If[share, MyShare=Share, MyShare[]:=0];

If[specialQ,
	minDeg=2;
,
	minDeg=1;
];

Which[schurQ,
	If[perm === False,
		ChargeList[level_] := Flatten[#]&/@DeleteDuplicates[Map[Sort,{{0,nz},{0,n\[Theta]1,n\[Theta]2}}/.Solve[2 nz+n\[Theta]1+n\[Theta]2==level,{nz,n\[Theta]1,n\[Theta]2},NonNegativeIntegers],{2}]];
		,
		ChargeList[level_] := {0,nz,0,n\[Theta]1,n\[Theta]2}/.Solve[2 nz+n\[Theta]1+n\[Theta]2 == level,{nz,n\[Theta]1,n\[Theta]2},NonNegativeIntegers];
	];
	levelvector={0,2,0,1,1};
	,
	su122Q, 
	If[perm === False,
		ChargeList[level_] := Flatten[#]&/@DeleteDuplicates[ {Sort[#[[1]]], Sort[#[[2]]], #[[3]]} &/@ ({{nzn,nzp},{n\[Theta]1,n\[Theta]2},{n\[Theta]3}}/.Solve[3 nzn+3 nzp+2 n\[Theta]1+2 n\[Theta]2+2 n\[Theta]3==level,{nzn,nzp,n\[Theta]1,n\[Theta]2,n\[Theta]3},NonNegativeIntegers]) ];
		,
		ChargeList[level_] := {nzn,nzp,n\[Theta]1,n\[Theta]2,n\[Theta]3}/.Solve[3 nzn+3 nzp+2 n\[Theta]1+2 n\[Theta]2+2 n\[Theta]3==level,{nzn,nzp,n\[Theta]1,n\[Theta]2,n\[Theta]3},NonNegativeIntegers];
	];
	levelvector={3,3,2,2,2};
	,
	su121Q,
	If[perm === False,
		ChargeList[level_] := Flatten[#]&/@DeleteDuplicates[ {Sort[#[[1]]],#[[2]]} &/@ ({{nzn,nzp},{n\[Theta]1,n\[Theta]2,n\[Theta]2}}/.Solve[3 nzn+3 nzp+2 n\[Theta]1+4 n\[Theta]2==level,{nzn,nzp,n\[Theta]1,n\[Theta]2},NonNegativeIntegers]) ];
		,
		ChargeList[level_] := {nzn,nzp,n\[Theta]1,n\[Theta]2,n\[Theta]2}/.Solve[3 nzn+3 nzp+2 n\[Theta]1+4 n\[Theta]2==level,{nzn,nzp,n\[Theta]1,n\[Theta]2},NonNegativeIntegers];
	];
	levelvector={3,3,2,2,2};
	,
	True, 
	If[perm === False,
		ChargeList[level_] := Flatten[#]&/@DeleteDuplicates[Map[Sort,{{nzn,nzp},{n\[Theta]1,n\[Theta]2,n\[Theta]3}}/.Solve[3 nzn+3 nzp+2 n\[Theta]1+2 n\[Theta]2+2 n\[Theta]3==level,{nzn,nzp,n\[Theta]1,n\[Theta]2,n\[Theta]3},NonNegativeIntegers],{2}]];
		,
		ChargeList[level_] := {nzn,nzp,n\[Theta]1,n\[Theta]2,n\[Theta]3}/.Solve[3 nzn+3 nzp+2 n\[Theta]1+2 n\[Theta]2+2 n\[Theta]3==level,{nzn,nzp,n\[Theta]1,n\[Theta]2,n\[Theta]3},NonNegativeIntegers];
	];
	levelvector={3,3,2,2,2};
];

SetAttributes[{pTable,pDo},HoldAll];
pTable[expr_,iter__] := ParallelTable[ReleaseHold[Hold[expr]],iter,Method->"FinestGrained"];
pDo[expr_,iter__] := ParallelDo[ReleaseHold[Hold[expr]],iter,Method->"FinestGrained"];
If[numKernels === Null, table=Table; do=Do;, table=pTable; do=pDo;];

InitiateKernels[] := Module[{},
	Check[
		LaunchKernels[numKernels];
	,
		Quit[];
	];
	Print[ParallelEvaluate[$KernelID]];
	If[Length[ParallelEvaluate[$KernelID]]!=numKernels,Quit[]];
	ParallelEvaluate[Quiet[<<Combinatorica`];];
	ParallelEvaluate[$RecursionLimit=Infinity;];
	ParallelEvaluate[Stuff[];];
];

ResetKernels[] := Module[{},
	If[numKernels =!= Null, TimeConstrained[
		AbortKernels[];
		AbortKernels[];
		AbortKernels[];
		ParallelEvaluate[Quiet[<<Combinatorica`];];
		ParallelEvaluate[$RecursionLimit=Infinity;];
		ParallelEvaluate[Stuff[];];
	,
		60
	,
		Print["> kernels frozen"];
		TimeConstrained[
			CloseKernels[];
		,
			60
		,
			Print["> cannot close kernels"];
			Quit[];
		];
		Print["> relaunch kernels"];
		InitiateKernels[];
	];];
];

Get[job<>".m"];

If[numKernels =!= Null,
	InitiateKernels[];
];


(* ::Section:: *)
(*Execute*)


If[RefLink[$SystemWordLength,paclet:ref/$SystemWordLength]!=64, Print["SystemWordLength not 64"]; Quit[];];

Do[
	If[!FileExistsQ[directory],CreateDirectory[directory]];
,
	{directory,directories}
];

t = Timing[
	numLevels = Length[ChargeList[level]];
	charges = ChargeList[level][[ind]];
	maxDeg=Plus@@charges;
	Print["level ",level,", charges ",ind,"/",numLevels,": ",charges,", degree ",degree,"/",maxDeg];
	Exec[];
];
Print[t[[1]]];
