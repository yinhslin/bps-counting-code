(* ::Package:: *)

(* ::Section:: *)
(*Input*)


options = $CommandLine;
(*options = {"-N", "2", "-lmin", "4", "-lmax", "12"};*)
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
level = param["l"] // ToExpression;
ind = param["i"] // ToExpression;
time = param["t"] // ToExpression;
If[time === Null, time = Infinity];
numKernels = param["k"] // ToExpression;
perm = param["p"] // ToExpression;
If[perm === Null, perm = False];
job = param["j"];
share = param["s"] // ToExpression;
If[share === Null, share = False];
numerical = param["n"] // ToExpression;
If[numerical === Null, numerical = False, numerical = True];
chunk = param["c"] // ToExpression;
If[chunk === Null, chunk = 10^3];
schurQ = param["sch"] // ToExpression;
If[schurQ === Null, schurQ = False, schurQ = True];


user = $Username;
home = Switch[user,
	"yhlin",
		If[specialQ,
			"/n/holyscratch01/yin_lab/Users/yhlin/bps/"<>If[schurQ,"grav/","grav16/"]
			,
			"/n/holyscratch01/yin_lab/Users/yhlin/bps_u/"<>If[schurQ,"grav/","grav16/"]
		]
	,
	_,
		If[specialQ,
			Directory[]<>"/bps/"<>If[schurQ,"grav/","grav16/"]
			,
			Directory[]<>"/bps_u/"<>If[schurQ,"grav/","grav16/"]
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
directories = {home,necklaceDirectory,singleDirectory,multiDirectory,singleGravitonDirectory,multiGravitonDirectory,countDirectory,cohomologyDirectory,juliaDirectory,hDirectory,adDirectory};

On[Assert];

Quiet[<<Combinatorica`];
$RecursionLimit=Infinity;

If[share, MyShare=Share, MyShare[]:=0];

If[specialQ,
	minDeg=2;
,
	minDeg=1;
];

If[schurQ,
	(*If[perm === False,
		ChargeList[level_] := Flatten[#]&/@DeleteDuplicates[Map[Sort,{{0,nz},{0,n\[Theta]1,n\[Theta]2}}/.Solve[3 nz+2 n\[Theta]1+2 n\[Theta]2==level,{nz,n\[Theta]1,n\[Theta]2},NonNegativeIntegers],{2}]];
		,
		ChargeList[level_] := {0,nz,0,n\[Theta]1,n\[Theta]2}/.Solve[3 nz+2 n\[Theta]1+2 n\[Theta]2 ==level,{nz,n\[Theta]1,n\[Theta]2},NonNegativeIntegers];
	];*)
	If[perm === False,
		ChargeList[level_] := Flatten[#]&/@DeleteDuplicates[Map[Sort,{{0,nz},{0,n\[Theta]1,n\[Theta]2}}/.Solve[2 nz+n\[Theta]1+n\[Theta]2==level,{nz,n\[Theta]1,n\[Theta]2},NonNegativeIntegers],{2}]];
		,
		ChargeList[level_] := {0,nz,0,n\[Theta]1,n\[Theta]2}/.Solve[2 nz+n\[Theta]1+n\[Theta]2 == level,{nz,n\[Theta]1,n\[Theta]2},NonNegativeIntegers];
	];
	levelvector={0,2,0,1,1};
	,
	If[perm === False,
		ChargeList[level_] := Flatten[#]&/@DeleteDuplicates[Map[Sort,{{nzn,nzp},{n\[Theta]1,n\[Theta]2,n\[Theta]3}}/.Solve[3 nzn+3 nzp+2 n\[Theta]1+2 n\[Theta]2+2 n\[Theta]3==level,{nzn,nzp,n\[Theta]1,n\[Theta]2,n\[Theta]3},NonNegativeIntegers],{2}]];
		,
		ChargeList[level_] := {nzn,nzp,n\[Theta]1,n\[Theta]2,n\[Theta]3}/.Solve[3 nzn+3 nzp+2 n\[Theta]1+2 n\[Theta]2+2 n\[Theta]3==level,{nzn,nzp,n\[Theta]1,n\[Theta]2,n\[Theta]3},NonNegativeIntegers];
	];
	levelvector={3,3,2,2,2};
];

If[numKernels === Null, table=Table; do=Do;, table=ParallelTable; do=ParallelDo;];

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
	Print["level: ",level];
	Print["charges ",ind,"/",numLevels,": ", charges];
	If[job=="singlegraviton",
		maxDeg=NN;
		,
		maxDeg=Plus@@charges;
	];
	Do[
		Print["level ",level,", charges ",ind,"/",numLevels,": ",charges,", degree ",degree,"/",maxDeg];
		Exec[];
	,
		{degree,minDeg,maxDeg}
	];
];
Print[t[[1]]];
