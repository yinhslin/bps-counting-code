(* ::Package:: *)

(* ::Section::Closed:: *)
(*Input*)


options = $CommandLine;
options = {"-N", "3", "-lmin", "4", "-lmax", "4"};
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
If[specialQ === Null, specialQ = True, specialQ = !specialQ];
minLevel = param["lmin"] // ToExpression;
maxLevel = param["lmax"] // ToExpression;
numerical = param["n"] // ToExpression;
If[numerical === Null, numerical = False, numerical = True];
time = param["t"] // ToExpression;
If[time === Null, time = Infinity];
numKernels = param["k"] // ToExpression;

If[$FrontEnd===Null,
	user = $Username;
	home = Switch[user,
		"yhlin",
			If[specialQ,
				"/n/holyscratch01/yin_lab/Users/yhlin/bps/"
				,
				"/n/holyscratch01/yin_lab/Users/yhlin/bps_u/"
			];
		,
		_,
			Directory[]<>"/"
	];
,
	home = NotebookDirectory[];
];

singleDirectory = home <> "singletrace/";
multiDirectory = home <> "multitrace/";
multiGravitonDirectory = home <> "multigraviton/";
countDirectory = home <> "count/";
juliaDirectory = home <> "julia/";
miscDirectory = home <> "misc/";


(* ::Section:: *)
(*Inner product*)


index[a1_,a2_,a3_,a4_,a5_,i_,j_]:=Mod[a3+a4+a5+1,2]*2^15+a1*2^11+a2*2^7+a3*2^6+a4*2^5+a5*2^4+(i-1)*2^2+(j-1);
fp[a_]:=Quotient[a,2^15];
nz1[a_]:=Quotient[Mod[a,2^15],2^11];
nz2[a_]:=Quotient[Mod[a,2^11],2^7];
n\[Theta]1[a_]:=Quotient[Mod[a,2^7],2^6];
n\[Theta]2[a_]:=Quotient[Mod[a,2^6],2^5];
n\[Theta]3[a_]:=Quotient[Mod[a,2^5],2^4];
mati[a_]:=Quotient[Mod[a,2^4],2^2]+1;
matj[a_]:=Mod[a,2^2]+1;


(* TODO: Can make more efficient by bit shifting *)
decode[m_]:=Module[{n,a1,a2,a3,a4,a5,i,j},
	n=m;
	j=1+Mod[n,2^2];
	n=Quotient[n-j+1,2^2];
	i=1+Mod[n,2^2];
	n=Quotient[n-i+1,2^2];
	a5=Mod[n,2^1];
	n=Quotient[n-a5,2^1];
	a4=Mod[n,2^1];
	n=Quotient[n-a4,2^1];
	a3=Mod[n,2^1];
	n=Quotient[n-a3,2^1];
	a2=Mod[n,2^4];
	n=Quotient[n-a2,2^4];
	a1=Mod[n,2^4];
	{a1,a2,a3,a4,a5,i,j}
];

(* (3.30) and (3.6-3.8) *)
factor[m_]:=Module[{a1,a2,a3,a4,a5,i,j,norm},
	{a1,a2,a3,a4,a5,i,j}=decode[m];
	norm=If[i==j && specialQ,
		Switch[i,
			1, 2,
			2, 6,
			3, 12
		]
	,
		1
	];
	norm=1;
	2^(2a1+2a2+1+4(a3-1)(a4-1)(a5-1))*a1!*a2!*(a1+a2+a3+a4+a5-1)!/norm
];

(* Inner product of monomials *)
IPmono[m1_,m2_]:=Module[{l1,l2,t1,t2},
	l1=(m1/.NonCommutativeMultiply->Times/.Times->List)/.{X[n_]^p_:>Array[X[n]&,{p}]}//Flatten;
	If[!ListQ[l1],l1={l1}];
	l1=Table[If[ListQ[x],Array[(x[[1]])&,{x[[2]]}],x],{x,l1}]//Flatten;
	l2=(m2/.NonCommutativeMultiply->Times/.Times->List)/.{X[n_]^p_:>Array[X[n]&,{p}]}//Flatten;
	If[!ListQ[l2],l2={l2}];
	l2=Table[If[ListQ[x],Array[(x[[1]])&,{x[[2]]}],x],{x,l2}]//Flatten;
	t1=Tally[l1];
	t2=Tally[l2];
	If[t1=!=t2,Return[0]];
	Product[t[[2]]!*factor[t[[1,1]]],{t,t1}]
];
(*IPmono[m1_,m2_]:=Module[{l1,l2,t1,t2},
	l1=m1/.NonCommutativeMultiply->Times/.{Power->List,Times->List};
	If[!ListQ[l1],l1={l1}];
	l1=Table[If[ListQ[x],Array[(x[[1]])&,{x[[2]]}],x],{x,l1}]//Flatten;
	l2=m2/.NonCommutativeMultiply->Times/.{Power->List,Times->List};
	If[!ListQ[l2],l2={l2}];
	l2=Table[If[ListQ[x],Array[(x[[1]])&,{x[[2]]}],x],{x,l2}]//Flatten;
	t1=Tally[l1];
	t2=Tally[l2];
	If[t1=!=t2,Return[0]];
	Product[t[[2]]!*factor[t[[1,1]]],{t,t1}]
];*)

(* Inner product of polynomials using 2-finger algorithm *)
IP[p1_,p2_]:=Module[{l1,l2,i=1,j=1,ans,comp},
	l1=p1/.Plus->List;
	l1=If[NumericQ[#[[1]]],{#[[2]],#[[1]]},{#,1}]&/@l1//Sort;
	l2=p2/.Plus->List;
	l2=If[NumericQ[#[[1]]],{#[[2]],#[[1]]},{#,1}]&/@l2//Sort;
	Print[l1];
	ans = 0;
	While[i<=Length[l1] && j<=Length[l2],
		comp = Order[l1[[i]],l2[[j]]];
		Switch[comp,
			0, ans+=l1[[i,2]]*l2[[j,2]]*IPmono[l1[[i,1]],l2[[j,1]]]; i+=1; j+=1;,
			1, i+=1,
			-1, j+=1
		];
	];
	ans
];

(* Valid for U(N) and SU(2) *)
(* T-matrix for list of monomials using 2-finger algorithm *)
TDiag[l_]:=Module[{ans},
	ans=SparseArray[{},{Length[l],Length[l]}];
	Do[
		ans[[i,i]]=IPmono[l[[i]],l[[i]]]
	,
		{i,1,Length[l]}
	];
	ans
];
(* TO DEPRECIATE *)
T[l1_,l2_]:=Module[{i=1,j=1,ans,comp,ord1,ord2,ll1,ll2},
	(* sort l1, l2 *)
	ord1 = Ordering[l1];
	ll1 = l1[[ord1]];
	ord2 = Ordering[l2];
	ll2 = l2[[ord2]];
	ans = SparseArray[{},{Length[l1],Length[l2]}];
	While[i<=Length[l1] && j<=Length[l2],
		comp = Order[ll1[[i]],ll2[[j]]];
		Switch[comp,
			0, ans[[ord1[[i]],ord2[[j]]]]=IPmono[ll1[[i]],ll2[[j]]]; i+=1; j+=1;,
			1, i+=1,
			-1, j+=1
		];
	];
	ans
];

(* (3.6-3.8) *)
ChangeIJ[n_,i_,j_]:=2^4*Quotient[n,2^4]+(i-1)*2^2+(j-1);
Sub[n_]:=Module[{i,j},
	{i,j}={mati[n],matj[n]};
	If[i==j,
		Switch[NN,
			3,
				Switch[i,
					1, -X[n]+X[ChangeIJ[n,2,2]],
					2, X[n]+X[ChangeIJ[n,2,2]]
				],
			4,
				Switch[i,
					1, -X[n]-X[ChangeIJ[n,2,2]]+X[ChangeIJ[n,3,3]],
					2, 2X[ChangeIJ[n,2,2]]+X[ChangeIJ[n,3,3]],
					3, X[n]-X[ChangeIJ[n,2,2]]+X[ChangeIJ[n,3,3]]
				]
		]
	,
		X[n]
	]
]/;NN>2;
Sub[n_]:=X[n]/;NN==2;

(* T-matrix for list of polynomials *)
UnTimes[n_,a__]:=n UnTimes[a]/;NumericQ[n];
UnTimes[a_]:=a;
T[l_]:=Module[{ll,allTerms,matrix},
	ll=l/.X[n_]:>Sub[n]//Expand;
	ll=ll/.Times->UnTimes;
	allTerms = CollectTerms[ll];
	matrix = CoefficientArrays[ll,allTerms][[2]];
	allTerms = allTerms/.UnTimes->Times;
	matrix . TDiag[allTerms] . Transpose[matrix]
];


(* ::Section:: *)
(*Test *)


Get[#]&/@FileNames[multiDirectory<>"*"<>ToString[NN]<>".mx"];


(* ::Subsection:: *)
(*T matrix for non-diagonal product*)


CollectTerms[lis_]:=DeleteCases[DeleteDuplicates[Flatten[lis/.Plus->List/.{n_ a_:>a/;NumberQ[n]}/.{-a_:>a}]],0];
p=multiTrace[{0,0,0,0,3},3,NN];
l=CollectTerms[Flatten[p]];


l
ll=l/.X[n_]:>Sub[n]//Expand
T[l]//Normal//MatrixForm


l[[1]]
l[[1]]/.{X[n_]:>Sub[n]}//Expand


Sub[16]
decode[16]
decode[21]


(* ::Subsection:: *)
(*T-matrix*)


CollectTerms[lis_]:=DeleteCases[DeleteDuplicates[Flatten[lis/.Plus->List/.{n_ a_:>a/;NumberQ[n]}/.{-a_:>a}]],0];
p=multiTrace[{0,0,1,1,2},4,NN];
l=CollectTerms[Flatten[p]];

tmp1 = T[l,l]//Normal
tmp2 = Table[IPmono[x,y],{x,l},{y,l}]
tmp3 = TDiag[l]//Normal
tmp1==tmp2==tmp3


(* ::Subsection:: *)
(*Inner product*)


p1=multiTrace[{1,1,0,0,0},2,NN][[1]]
l1=p1/.Plus->List;
l1=If[NumericQ[#[[1]]],{#[[2]],#[[1]]},{#,1}]&/@l1//Sort

p2=multiTrace[{0,0,1,1,1},2,NN][[1]]
l2=p2/.Plus->List;
l2=If[NumericQ[#[[1]]],{#[[2]],#[[1]]},{#,1}]&/@l2//Sort

IP[p1,p1]
(*IP[p1,p2]
IP[p2,p2]*)
