(* ::Package:: *)

(* ::Section::Closed:: *)
(*Input*)


options = $CommandLine;
(*options = {"-N", "4", "-n", "15", "-t", "fm"};*)
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
n = param["n"] // ToExpression;
type = param["t"]; (* "16", "us", "fs", "um", "fm", "a" *)


(* ::Section::Closed:: *)
(*Directories*)


user = $Username;
home = Switch[user,
	"yhlin",
		(*"/n/holyscratch01/yin_lab/Users/yhlin/bps/"<>"index/"*)
		"/n/home07/yhlin/bps/index/"
	,
	_,
		Directory[]<>"/bps/"<>"index/"
];

snDirectory = home <> "sn/";
rawUDirectory = home <> "rawU/";
rawDirectory = home <> "raw/";
indUDirectory = home <> "indU/";
indUInvDirectory = home <> "indU/";
indDirectory = home <> "ind/";

directories = {home,snDirectory,rawDirectory,rawUDirectory,indDirectory,indUDirectory,indUInvDirectory};

Do[
	If[!FileExistsQ[directory],CreateDirectory[directory]];
,
	{directory,directories}
];


(* ::Section::Closed:: *)
(*GAP*)


SnChar[n_,NN_]:=SnChar[n,NN]=Module[{fn=snDirectory<>ToString[n]<>"_"<>ToString[NN]<>".m"},
	If[FileExistsQ[fn],
		Get[fn],
		Print["Missing n="<>ToString[n]<>" N="<>ToString[NN]];
	]
];


(* ::Section::Closed:: *)
(*Index*)


Switch[type,
	"16", is[x_,b_,s_,a_]:=1-(1-x^2)^3/(1-x^3)^2,
	"us", is[x_,b_,s_,a_]:=1-(1-x)^2/(1-x^2),
	"fs", is[x_,b_,s_,a_]:=1-((1-b x)(1-b^-1 x))/(1-x^2),
	"um", is[x_,b_,s_,a_]:=1-((1-s x)(1-s x))/(1-x^2),
	"fm", is[x_,b_,s_,a_]:=1-((1-b s x)(1-b^-1 s x))/(1-x^2),
	"a", is[x_,b_,s_,a_]:=1-((1-x s b)(1-x s b^-1)(1- x a s^-2))/((1-x^2)(1-a x)),
	_, Print["Unknown type"]; Quit[];
];


z[P_]:=(Times@@P)Product[i[[2]]!,{i,Tally[P]}];

indexGAP[N_,level_]:=Module[{snchar},
	snchar=SnChar[level,N];
	Sum[Product[is[x^i,b^i,s^i,a^i],{i,P[[1]]}] 1/z[P[[1]]] P[[2]],{P,snchar}]
];


(* ::Section::Closed:: *)
(*Execute*)


If[RefLink[$SystemWordLength,paclet:ref/$SystemWordLength]!=64, Print["SystemWordLength not 64"]; Quit[];];
label=type<>"_"<>ToString[NN]<>"_"<>ToString[n];


file=rawUDirectory<>label<>".mx";
If[FileExistsQ[file]
,
Get[file];
,
Print["raw U: ", Timing[f=Series[1+Sum[indexGAP[NN,i],{i,1,n}],{x,0,n}]][[1]]];
DumpSave[file, f];
];


file=indUDirectory<>label<>".mx";
If[FileExistsQ[file]
,
Get[file];
,
Print["ind U: ", Timing[f=Simplify[f]][[1]]];
DumpSave[file, f];
];


If[NN==1,
file=indUInvDirectory<>type<>"_"<>ToString[n]<>".mx";
If[FileExistsQ[file]
,
Get[file];
,
Print["inv: ", Timing[u1inv=Simplify[1/f]][[1]]];
DumpSave[file, u1inv];
];
];


If[NN!=1,
file=indUInvDirectory<>type<>"_"<>ToString[n]<>".mx";
If[FileExistsQ[file]
,
Get[file];
,
Print["U1 inv incomplete"];Quit[]];
];


If[NN!=1,
file=rawDirectory<>label<>".mx";
If[FileExistsQ[file]
,
Get[file];
,
Print["raw: ", Timing[f=f*u1inv][[1]]];
DumpSave[file, f];
];
];


If[NN!=1,
file=indDirectory<>label<>".mx";
If[FileExistsQ[file]
,
Get[file];
,
Print["ind: ", Timing[f=Simplify[f]][[1]]];
DumpSave[file, f];
];
];
