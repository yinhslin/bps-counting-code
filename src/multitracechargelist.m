(* ::Package:: *)

(* ::Section:: *)
(*Input*)


options = $CommandLine;
(*options = {"-N", "2", "-l", "12", "-su121"};*)
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
soQ = param["so"] // ToExpression;
If[soQ === Null, soQ = False, soQ = True];
spQ = param["sp"] // ToExpression;
If[spQ === Null, spQ = False, spQ = True];
maxLevel = param["l"] // ToExpression;
perm = True;
schurQ = param["sch"] // ToExpression;
If[schurQ === Null, schurQ = False, schurQ = True];
su122Q = param["su122"] // ToExpression;
If[su122Q === Null, su122Q = False, su122Q = True];
su121Q = param["su121"] // ToExpression;
If[su121Q === Null, su121Q = False, su121Q = True];


user = $Username;
home = Switch[user,
	"yhlin",
		Which[
			spQ,
			"/n/holyscratch01/yin_lab/Users/yhlin/bps_sp/"<>Which[schurQ, "schur/", su122Q, "su122/", su121Q, "su121/", True, "all/"],
			soQ,
			"/n/holyscratch01/yin_lab/Users/yhlin/bps_so/"<>Which[schurQ, "schur/", su122Q, "su122/", su121Q, "su121/", True, "all/"],
			specialQ,
			"/n/holyscratch01/yin_lab/Users/yhlin/bps_su/"<>Which[schurQ, "schur/", su122Q, "su122/", su121Q, "su121/", True, "all/"],
			!specialQ,
			"/n/holyscratch01/yin_lab/Users/yhlin/bps_u/"<>Which[schurQ, "schur/", su122Q, "su122/", su121Q, "su121/", True, "all/"]
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

multiTraceChargeListDirectory = home <> "multitracechargelist/";
If[!FileExistsQ[multiTraceChargeListDirectory],CreateDirectory[multiTraceChargeListDirectory]];


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
