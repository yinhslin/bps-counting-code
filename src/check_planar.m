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

specialQ = param["s"] // ToExpression;
If[specialQ === Null, specialQ = True];
minLevel = param["lmin"] // ToExpression;
maxLevel = param["lmax"] // ToExpression;
ind = param["i"] // ToExpression;
If[ind === Null, ind = 1];
type = param["t"];
perm = param["p"];
If[perm === Null, perm = False, perm = True];
delete = param["d"];
If[delete === Null, delete = False, delete = True];

user = $Username;
home = Switch[user,
	"yhlin",
		If[specialQ,
			"/n/holyscratch01/yin_lab/Users/yhlin/bps/"
			,
			"/n/holyscratch01/yin_lab/Users/yhlin/bps_u/"
		]
	,
	_,
		If[specialQ,
			Directory[]<>"/bps/"
			,
			Directory[]<>"/bps_u/"
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

If[perm,
	ChargeList[level_] := {nzn,nzp,n\[Theta]1,n\[Theta]2,n\[Theta]3}/.Solve[3 nzn+3 nzp+2 n\[Theta]1+2 n\[Theta]2+2 n\[Theta]3==level,{nzn,nzp,n\[Theta]1,n\[Theta]2,n\[Theta]3},NonNegativeIntegers];
	,
	ChargeList[level_] := Flatten[#]&/@DeleteDuplicates[Map[Sort,{{nzn,nzp},{n\[Theta]1,n\[Theta]2,n\[Theta]3}}/.Solve[3 nzn+3 nzp+2 n\[Theta]1+2 n\[Theta]2+2 n\[Theta]3==level,{nzn,nzp,n\[Theta]1,n\[Theta]2,n\[Theta]3},NonNegativeIntegers],{2}]];
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
			filename = directory<>ToString[level]<>"_"<>StringRiffle[ToString[#]&/@charges,"_"]<>"_"<>ToString[degree]<>"_P.mx";
			If[!FileExistsQ[filename]
			,
				(*Print["charges ",cnt,"/",numLevels,": ", charges, " degree ", degree, " has no file"];*)
				AppendTo[list,{level,cnt,degree}];
			,
				If[
					Check[
						Get[filename];
						Assert[ValueQ[ToExpression[type][charges,degree]]];
						Assert[ListQ[ToExpression[type][charges,degree]]];
						Assert[DeleteCases[DeleteDuplicates[ToExpression[type][charges,degree]/.{X[_]->0}],0]==={}];
					,
					err]==err
				, 
					Print["charges ",cnt,"/",numLevels,": ", charges, " degree ", degree, " has error"];
					Print[DeleteCases[DeleteDuplicates[ToExpression[type][charges,degree]/.{X[_]->0}],0]];
					AppendTo[list,{level,cnt,degree}];
					(* DANGEROUS *)
					If[delete,
						DeleteFile[filename];
					];
				];
			];
			Clear[singleTrace,multiTrace];
		,
			{degree,minDeg,maxDeg}
		]
		,
		Do[
			filename = directory<>ToString[level]<>"_"<>StringRiffle[ToString[#]&/@charges,"_"]<>"_"<>ToString[degree]<>"_P.csv";
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
							Assert[Length[tmp]>=7];
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
			Clear[singleTrace,multiTrace];
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
