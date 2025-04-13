(* ::Package:: *)

(* ::Section:: *)
(*Input*)


options = $CommandLine;
(*options = {"-N", "2", "-lmin", "2", "-lmax", "12"};*)
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
specialQ = param["s"] // ToExpression;
If[specialQ === Null, specialQ = True];
soQ = param["so"] // ToExpression;
If[soQ === Null, soQ = False, soQ = True];
spQ = param["sp"] // ToExpression;
If[spQ === Null, spQ = False, spQ = True];
minLevel = param["lmin"] // ToExpression;
maxLevel = param["lmax"] // ToExpression;
ind = param["i"] // ToExpression;
If[ind === Null, ind = 1];
type = param["t"];
perm = param["p"];
If[perm === Null, perm = False, perm = True];
delete = param["d"];
If[delete === Null, delete = False, delete = True];
schurQ = param["sch"] // ToExpression;
If[schurQ === Null, schurQ = False, schurQ = True];

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
directory = home<>ToLowerCase[type]<>"/";


(* ::Section:: *)
(*Execute*)


Unprotect[NonCommutativeMultiply];

$RecursionLimit = Infinity;
0 ** _ := 0
_ ** 0 := 0

Protect[NonCommutativeMultiply];


(* ::Section:: *)
(*Execute*)


If[RefLink[$SystemWordLength,paclet:ref/$SystemWordLength]!=64, Print["SystemWordLength not 64"]; Quit[];];
On[Assert];

If[specialQ,
	minDeg=2;
,
	minDeg=1;
];
If[type==="count", minDeg -= 1];

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

list = {};
Do[
	numLevels = Length[ChargeList[level]];
	Print["level: ",level];
	cnt = ind-1;
	Do[
		cnt += 1;
		Print["level: ",level,", charges ",cnt,"/",numLevels,": ", charges];
		maxDeg=Plus@@charges;
		If[type =!= "count" && type =!= "cohomology" && type =!= "ad"
		,
		Do[
			filename = directory<>ToString[level]<>"_"<>StringRiffle[ToString[#]&/@charges,"_"]<>"_"<>ToString[degree]<>"_"<>ToString[NN]<>".mx";
			If[!FileExistsQ[filename]
			,
				(*Print["charges ",cnt,"/",numLevels,": ", charges, " degree ", degree, " has no file"];*)
				AppendTo[list,{level,cnt,degree}];
			,
				If[
					Check[
						Get[filename];
						Assert[ValueQ[ToExpression[type][charges,degree,NN]]];
						Assert[ListQ[ToExpression[type][charges,degree,NN]]];
						(*Print[DeleteCases[DeleteDuplicates[ToExpression[type][charges,degree,NN]/.{XB[__]->0,XF[__]->0}],0]];*)
						Assert[DeleteCases[DeleteDuplicates[ToExpression[type][charges,degree,NN]/.{X[_]->0}],0]==={}];
						
						(*Assert[(ToExpression[type][charges,degree,NN]/.{singleTrace[__]->0,multiTrace[__]->0,SingleTrace[__]->0,MultiTrace[__]->0})=!=0];*)
						(*Print["> ",ToExpression[type][charges,degree,NN][[1,1]]];*)
					,
					err]==err
				, 
					Print["charges ",cnt,"/",numLevels,": ", charges, " degree ", degree, " has error"];
					Print[DeleteCases[DeleteDuplicates[ToExpression[type][charges,degree,NN]/.{X[_]->0}],0]];
					AppendTo[list,{level,cnt,degree}];
					(* DANGEROUS *)
					If[delete,
						DeleteFile[filename];
					];
				];
			];
			Clear[singleTrace,multiTrace,singleGraviton,multiGraviton];
		,
			{degree,minDeg,maxDeg}
		]
		,
		Do[
			filename = directory<>ToString[level]<>"_"<>StringRiffle[ToString[#]&/@charges,"_"]<>"_"<>ToString[degree]<>"_"<>ToString[NN]<>".csv";
			If[!FileExistsQ[filename]
			,
				(*Print["charges ",cnt,"/",numLevels,": ", charges, " degree ", degree, " has no file"];*)
				AppendTo[list,{level,cnt,degree}];
			,
				If[
					Check[
						tmp = Import[filename][[1]];
						If[type === "count",
							Assert[Length[tmp]==3];
						];
						If[type === "cohomology",
							Assert[Length[tmp]==10];
						];
						If[type === "ad",
							Assert[Length[tmp]>=8];
						];
					,
					err]==err
				, 
					Print["charges ",cnt,"/",numLevels,": ", charges, " degree ", degree, " has error"];
					AppendTo[list,{level,cnt,degree}];
					(* DANGEROUS *)
					If[delete,
						DeleteFile[filename];
					];
				];
			];
		,
			{degree,minDeg,maxDeg}
		]
		]
	,
		{charges,ChargeList[level][[ind;;]]}
	]
,
	{level,minLevel,maxLevel}
];

Print[list];
