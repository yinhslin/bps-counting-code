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

specialQ = True;
maxLevel = param["l"] // ToExpression;
perm = True;
schurQ = param["sch"] // ToExpression;
If[schurQ === Null, schurQ = False, schurQ = True];


user = $Username;
home = Switch[user,
	"yhlin",
		If[specialQ,
			"/n/holyscratch01/yin_lab/Users/yhlin/bps/"<>If[schurQ,"schur/","all/"]
			,
			"/n/holyscratch01/yin_lab/Users/yhlin/bps_u/"<>If[schurQ,"schur/","all/"]
		]
	,
	_,
		If[specialQ,
			Directory[]<>"/bps/"<>If[schurQ,"schur/","all/"]
			,
			Directory[]<>"/bps_u/"<>If[schurQ,"schur/","all/"]
		]
];

multiTraceChargeListDirectory = home <> "multitracechargelist/";
If[!FileExistsQ[multiTraceChargeListDirectory],CreateDirectory[multiTraceChargeListDirectory]];


If[schurQ,
	(*If[perm === False,?
		ChargeList[level_] := Flatten[#]&/@DeleteDuplicates[Map[Sort,{{0,nz},{0,n\[Theta]1,n\[Theta]2}}/.Solve[3 nz+2 n\[Theta]1+2 n\[Theta]2==level,{nz,n\[Theta]1,n\[Theta]2},NonNegativeIntegers],{2}]];
		,
		ChargeList[level_] := {0,nz,0,n\[Theta]1,n\[Theta]2}/.Solve[3 nz+2 n\[Theta]1+2 n\[Theta]2 ==level,{nz,n\[Theta]1,n\[Theta]2},NonNegativeIntegers];
	];*)
	If[perm === False,
		ChargeList[level_] := ChargeList[level] = Flatten[#]&/@DeleteDuplicates[Map[Sort,{{0,nz},{0,n\[Theta]1,n\[Theta]2}}/.Solve[2 nz+n\[Theta]1+n\[Theta]2==level,{nz,n\[Theta]1,n\[Theta]2},NonNegativeIntegers],{2}]];
		,
		ChargeList[level_] := ChargeList[level] = {0,nz,0,n\[Theta]1,n\[Theta]2}/.Solve[2 nz+n\[Theta]1+n\[Theta]2 == level,{nz,n\[Theta]1,n\[Theta]2},NonNegativeIntegers];
	];
	levelvector={0,2,0,1,1};
	,
	If[perm === False,
		ChargeList[level_] := ChargeList[level] = Flatten[#]&/@DeleteDuplicates[Map[Sort,{{nzn,nzp},{n\[Theta]1,n\[Theta]2,n\[Theta]3}}/.Solve[3 nzn+3 nzp+2 n\[Theta]1+2 n\[Theta]2+2 n\[Theta]3==level,{nzn,nzp,n\[Theta]1,n\[Theta]2,n\[Theta]3},NonNegativeIntegers],{2}]];
		,
		ChargeList[level_] := ChargeList[level] = {nzn,nzp,n\[Theta]1,n\[Theta]2,n\[Theta]3}/.Solve[3 nzn+3 nzp+2 n\[Theta]1+2 n\[Theta]2+2 n\[Theta]3==level,{nzn,nzp,n\[Theta]1,n\[Theta]2,n\[Theta]3},NonNegativeIntegers];
	];
	levelvector={3,3,2,2,2};
];


(* ::Section:: *)
(*Multi Trace Charge List*)


file=multiTraceChargeListDirectory<>"progress.mx";
minLevel=If[schurQ,2,4];
If[FileExistsQ[file],Get[file],curLevel=minLevel];

SingleTraceChargeList[level_]:=SingleTraceChargeList[level]=ChargeList[level];
Do[
	Do[
		charges=c;
		MultiTraceChargeList[c]={{c}};
		Clear[multiTraceChargeList];
		multiTraceChargeList[charges]=MultiTraceChargeList[charges];
		DumpSave[multiTraceChargeListDirectory<>ToString[l]<>"_"<>StringRiffle[ToString[#]&/@charges,"_"]<>".mx",multiTraceChargeList];
	,
		{c,ChargeList[l]}
	];
	
	Do[
		Print["level "<>ToString[l]<>", sublevel "<>ToString[ll]];
		cl1=SingleTraceChargeList[ll];
		cl2=ChargeList[l-ll];
		Do[
			Do[
				AppendTo[MultiTraceChargeList[c1+c2],Sort[Join[{c1},c3]]]
			,
				{c3,MultiTraceChargeList[c2]}
			];
			charges=c1+c2;
			MultiTraceChargeList[charges]=DeleteDuplicates[MultiTraceChargeList[charges]];
		,
			{c1,cl1},{c2,cl2}
		];
	,
		{ll,minLevel,l-minLevel}
	];
	
	Do[
		Clear[multiTraceChargeList];
		multiTraceChargeList[charges]=MultiTraceChargeList[charges];
		DumpSave[multiTraceChargeListDirectory<>ToString[l]<>"_"<>StringRiffle[ToString[#]&/@charges,"_"]<>".mx",multiTraceChargeList]
	,
		{charges,ChargeList[l]}
	];
	
	curLevel=l+1;
	DumpSave[file,{MultiTraceChargeList,curLevel}];
,
	{l,curLevel,maxLevel}
];