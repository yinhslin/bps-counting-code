(* ::Package:: *)

(* ::Section::Closed:: *)
(*Input*)


options = $CommandLine;
(*options = {"-N", "5", "-n", "15", "-t", "fm"};*)
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
type = param["t"]; (* "16", "us", "fs", "um", "fm" *)


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
rawDirectory = home <> "raw/";
indDirectory = home <> "ind/";

directories = {home,snDirectory,rawDirectory,indDirectory};

Do[
	If[!FileExistsQ[directory],CreateDirectory[directory]];
,
	{directory,directories}
];


(* ::Section::Initialization::Closed:: *)
(*GAP*)


SnChar[n_,NN_]:=SnChar[n,NN]=Module[{fn=snDirectory<>ToString[n]<>"_"<>ToString[NN]<>".m"},
	If[FileExistsQ[fn],
		Get[fn],
		Print["Missing n="<>ToString[n]<>" N="<>ToString[NN]];
	]
];


Switch[type,
	"16", is[x_,b_,s_]:=1-(1-x^2)^3/(1-x^3)^2,
	"us", is[x_,b_,s_]:=1-(1-x)^2/(1-x^2),
	"fs", is[x_,b_,s_]:=1-((1-b x)(1-b^-1 x))/(1-x^2),
	"um", is[x_,b_,s_]:=1-((1-s x)(1-s x))/(1-x^2),
	"fm", is[x_,b_,s_]:=1-((1-b s x)(1-b^-1 s x))/(1-x^2),
	_, Print["Unknown type"]; Quit[];
];


(* ::Section::Initialization::Closed:: *)
(*Index*)


z[P_]:=(Times@@P)Product[i[[2]]!,{i,Tally[P]}];

indexGAP[N_,level_]:=Module[{snchar},
	snchar=SnChar[level,N];
	Sum[Product[is[x^i,b^i,s^i],{i,P[[1]]}] 1/z[P[[1]]] P[[2]],{P,snchar}]
];


(* ::Section::Closed:: *)
(*Execute*)


If[RefLink[$SystemWordLength,paclet:ref/$SystemWordLength]!=64, Print["SystemWordLength not 64"]; Quit[];];

label=type<>"_"<>ToString[NN]<>"_"<>ToString[n];

Print["raw: ", Timing[tmp=Series[(1+Sum[indexGAP[NN,i],{i,1,n}])/(1+Sum[indexGAP[1,i],{i,1,n}]),{x,0,n}]][[1]]];
DumpSave[rawDirectory<>label<>".mx", tmp];

Print["ind: ", Timing[tmp=Sum[Normal[Simplify[SeriesCoefficient[tmp,{x,0,i}]]]x^i,{i,0,n}]+O[x]^(n+1)][[1]]];
DumpSave[indDirectory<>label<>".mx", tmp];
