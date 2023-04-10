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
(*Count*)


MultiTrace[charges_,degree_,NN_] := Module[{level,filename,ans},
	level = charges . {3,3,2,2,2};
	filename = multiDirectory<>ToString[level]<>"_"<>StringRiffle[ToString[#]&/@charges,"_"]<>"_"<>ToString[degree]<>"_"<>ToString[NN]<>".mx";
	If[FileExistsQ[filename],
		Get[filename];
	,
		Return[{}];
	];
	ans = multiTrace[charges,degree,NN];
	Clear[multiTrace];
	ans
	];


(* ::Subsubsection::Closed:: *)
(*Q and Non-commutative multiply*)


Stuff[] := Module[{},
(* index relations *)
index[a1_,a2_,a3_,a4_,a5_,i_,j_]:=Mod[a3+a4+a5+1,2]*2^15+a1*2^11+a2*2^7+a3*2^6+a4*2^5+a5*2^4+(i-1)*2^2+(j-1);
fp[a_]:=Quotient[a,2^15];
nz1[a_]:=Quotient[Mod[a,2^15],2^11];
nz2[a_]:=Quotient[Mod[a,2^11],2^7];
n\[Theta]1[a_]:=Quotient[Mod[a,2^7],2^6];
n\[Theta]2[a_]:=Quotient[Mod[a,2^6],2^5];
n\[Theta]3[a_]:=Quotient[Mod[a,2^5],2^4];
mati[a_]:=Quotient[Mod[a,2^4],2^2]+1;
matj[a_]:=Mod[a,2^2]+1;

(* resture default NonCommutativeMultiply *)
Unprotect[NonCommutativeMultiply];
ClearAll[NonCommutativeMultiply];
SetAttributes[NonCommutativeMultiply,Flat];
SetAttributes[NonCommutativeMultiply,OneIdentity];
Protect[NonCommutativeMultiply];

(* Q action *)
Q[a_Plus]:=Q[#]&/@a;
Q[a_Times]:=Module[{alist,sign,A},
	alist=Apply[List,a];
	sign=1;A=0;
	Do[A=A+sign NonCommutativeMultiply@@(ReplacePart[alist,n->Q[alist[[n]]]]);
		sign=sign (-1)^Grading[alist[[n]]];
	,{n,alist//Length}];
	A
];
Q[n_]:=0/;NumericQ[n];
Q[X[a_]^n_]:=n X[a]^(n-1)Q[X[a]]/;fp[a]==0;
(*Q[X[a_]**b_]:=Q[X[a]]**b - X[a]**Q[b]/;fp[a]==1;*)
Q[a_NonCommutativeMultiply]:=Module[{alist,sign,A},
	alist=Apply[List,a];
	sign=1;A=0;
	Do[A=A+sign NonCommutativeMultiply@@(ReplacePart[alist,n->Q[alist[[n]]]]);
		sign=sign (-1)^Grading[alist[[n]]];
	,{n,alist//Length}];
	A
];
Q[X[a_]]:=Module[{g=fp[a],L1=nz1[a],L2=nz2[a],M1=n\[Theta]1[a],M2=n\[Theta]2[a],M3=n\[Theta]3[a],i=mati[a],j=matj[a]},
	If[g==0,
		Sum[(-1)^(m1+m2+m3+(M2-m2)m3+(M1-m1)(m2+m3)) 
			Binomial[L1,l1] Binomial[L2,l2] 
			Sum[X[index[l1,l2,m1,m2,m3,i,k]]X[index[L1-l1,L2-l2,M1-m1,M2-m2,M3-m3,k,j]],{k,1,NN}]
			,{l1,0,L1},{l2,0,L2},{m1,0,M1},{m2,0,M2},{m3,0,M3}]
		,
		Sum[(-1)^((M2-m2)m3+(M1-m1)(m2+m3)) 
			Binomial[L1,l1] Binomial[L2,l2] 
			Sum[X[index[l1,l2,m1,m2,m3,i,k]]**X[index[L1-l1,L2-l2,M1-m1,M2-m2,M3-m3,k,j]],{k,1,NN}]
			,{l1,0,L1},{l2,0,L2},{m1,0,M1},{m2,0,M2},{m3,Mod[m1+m2,2],M3,2}]
		+
		Sum[(-1)^(1+(M2-m2)m3+(M1-m1)(m2+m3)) 
			Binomial[L1,l1] Binomial[L2,l2] 
			Sum[X[index[l1,l2,m1,m2,m3,i,k]]X[index[L1-l1,L2-l2,M1-m1,M2-m2,M3-m3,k,j]],{k,1,NN}]
			,{l1,0,L1},{l2,0,L2},{m1,0,M1},{m2,0,M2},{m3,Mod[m1+m2+1,2],M3,2}]
	]
];
(*Q[X[a_]]:=
	Sum[(-1)^(m1+m2+m3+(n\[Theta]2[a]-m2)m3+(n\[Theta]1[a]-m1)(m2+m3)) 
		Binomial[nz1[a],l1] Binomial[nz2[a],l2] 
		Sum[X[index[l1,l2,m1,m2,m3,mati[a],k]]X[index[nz1[a]-l1,nz2[a]-l2,n\[Theta]1[a]-m1,n\[Theta]2[a]-m2,n\[Theta]3[a]-m3,k,matj[a]]],{k,1,NN}]
		,{l1,0,nz1[a]},{l2,0,nz2[a]},{m1,0,n\[Theta]1[a]},{m2,0,n\[Theta]2[a]},{m3,0,n\[Theta]3[a]}]/;fp[a]==0;
Q[X[a_]]:=
	Sum[(-1)^((n\[Theta]2[a]-m2)m3+(n\[Theta]1[a]-m1)(m2+m3)) 
		Binomial[nz1[a],l1] Binomial[nz2[a],l2] 
		Sum[X[index[l1,l2,m1,m2,m3,mati[a],k]]**X[index[nz1[a]-l1,nz2[a]-l2,n\[Theta]1[a]-m1,n\[Theta]2[a]-m2,n\[Theta]3[a]-m3,k,matj[a]]],{k,1,NN}]
		,{l1,0,nz1[a]},{l2,0,nz2[a]},{m1,0,n\[Theta]1[a]},{m2,0,n\[Theta]2[a]},{m3,Mod[m1+m2,2],n\[Theta]3[a],2}]
	+Sum[(-1)^(1+(n\[Theta]2[a]-m2)m3+(n\[Theta]1[a]-m1)(m2+m3)) 
		Binomial[nz1[a],l1] Binomial[nz2[a],l2] 
		Sum[X[index[l1,l2,m1,m2,m3,mati[a],k]]X[index[nz1[a]-l1,nz2[a]-l2,n\[Theta]1[a]-m1,n\[Theta]2[a]-m2,n\[Theta]3[a]-m3,k,matj[a]]],{k,1,NN}]
		,{l1,0,nz1[a]},{l2,0,nz2[a]},{m1,0,n\[Theta]1[a]},{m2,0,n\[Theta]2[a]},{m3,Mod[m1+m2+1,2],n\[Theta]3[a],2}]/;fp[a]==1;*)

	(* matrix and product *)
	If[specialQ,
		X[a_] := -Sum[X[Quotient[a,2^4]*2^4 + 5 k],{k,0,NN-2}]/;Mod[a-(NN-1)*2^2-(NN-1),2^4]==0;
	];
	X[a_]:=0/;Quotient[a,2^5]==2^10;

	Grading[ a_Plus ] := Max @@ (Grading /@ (List @@ a));
	Grading[ a_Times ] := Plus @@ (Grading /@ (List @@ a));
	Grading[ a_NonCommutativeMultiply ] := Plus @@ (Grading /@ (List @@ a));
	Grading[ _ ] := 0;
	Grading[ a_X ] := fp[a[[1]]];

	Unprotect[NonCommutativeMultiply];
	SetAttributes[NonCommutativeMultiply, Listable];
	ClearAttributes[NonCommutativeMultiply, Flat];
	NonCommutativeMultiply[a___, b_NonCommutativeMultiply, c___] := NonCommutativeMultiply[a, Sequence@@b, c];
	GetGradeds[a___] := (*GetGradeds[a] =*) Select[{a}, Grading[#] != 0 &];
	GetFermions[a___] := (*GetFermions[a] =*) Select[{a}, OddQ[Grading[#]] &];
	NonCommutativeMultiply[a___] /; Length[GetGradeds[a]] <= 1 := Times[a];
	NonCommutativeMultiply[a___] /; !FreeQ[{a}, Times, 2] := NonCommutativeMultiply @@ ReplacePart[ {a}, Sequence, Position[{a}, Times, 2] ];
	NonCommutativeMultiply[b___, a_, c___, a_, d___] /; OddQ[Grading[a]] := 0;
	(*NonCommutativeMultiply[a___] /; (!OrderedQ[GetGradeds[a]] || Length[GetGradeds[a]] != Length[{a}] ) :=
		Signature[GetFermions[a]] * (Times @@ Select[{a}, !MemberQ[GetGradeds[a], #]&]) * NonCommutativeMultiply @@ Sort[GetGradeds[a]];*)
	NonCommutativeMultiply[a___] := Module[{grade},grade=GetGradeds[a];
			Signature[GetFermions[a]] * (Times @@ Select[{a}, !MemberQ[grade, #]&]) * NonCommutativeMultiply @@ Sort[grade]
				/; (!OrderedQ[grade] || Length[grade] != Length[{a}] ) ];
	Protect[NonCommutativeMultiply];
	GExpand[a_, patt___] := Expand[a //. {x_NonCommutativeMultiply :> Distribute[x]}, patt];

];

Stuff[];


(* ::Subsubsection::Closed:: *)
(*Inner product*)


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

CollectTerms[lis_]:=DeleteCases[DeleteDuplicates[Flatten[lis/.Plus->List/.{n_ a_:>a/;NumericQ[n]}/.{-a_:>a}]],0];

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


(* ::Subsubsection:: *)
(*Anomalous dimension*)


If[numerical,
	julia = "julia";
	(*qr = home <> "qr.jl";*)
	qr = "/n/home07/yhlin/bps/qr.jl";
	qr = StringReplace[StringReplace[qr,{" "->"\ "}],{"("->"\(",")"->"\)","\ "->"\\\ "}];
	(* A must be a sparse matrix *)
	MyRowReduce[A_] := Module[{ans,id,dir,dirX},
		id = ToString[RandomInteger[10^10]];
		dir = juliaDirectory<>id<>"/";
		While[FileExistsQ[dir],
			id = ToString[RandomInteger[10^10]];
			dir = juliaDirectory<>id<>"/";
		];
		dirX = StringReplace[dir,{"("->"\(",")"->"\)","\ "->"\\\ "}];
		CreateDirectory[dir];
		Export[dir<>"in.mtx",A];
		Run[julia<>" "<>qr<>" Float64 1e-5 "<>dirX<>"in.mtx"<>" "<>dirX<>"out.mtx"];
		ans = Import[dir<>"out.mtx","MTX"];
		
		DeleteFile[dir<>"in.mtx"];
		DeleteFile[dir<>"out.mtx"];
		DeleteDirectory[dir];
		ans
	];
,
	MyRowReduce := RowReduce;
];

If[numKernels === Null,
	table = Table,
	table = ParallelTable
];

(* CM *)
UnTimes[n_,a__]:=n UnTimes[a]/;NumericQ[n];
UnTimes[a_]:=a;
IndStuff[traces_]:=Module[{Allterms,reducedTraces,CoVector,SimpVector},
	If[traces=={},{{},{}},
		reducedTraces=traces/.Times->UnTimes;
		Allterms=CollectTerms[reducedTraces];
		CoVector=CoefficientArrays[reducedTraces,Allterms][[2]];
		SimpVector = DeleteCases[CoVector//MyRowReduce,Table[0,{l,1,Length[CoVector[[1]]]}]];
		{SimpVector , Allterms/.UnTimes->Times}
	]
];

ActQ[SimpVector_,Allterms_] :=Module[{QStuff,reducedQStuff,Qmatrix,AllQTerms},
	QStuff = table[
		Stuff[];
		Q[t]//GExpand
	,
		{t,Allterms}
	];
	QStuff = QStuff/.Times->UnTimes;
	reducedQStuff = DeleteCases[DeleteCases[QStuff,0],0.](*/.Times->UnTimes*);
	If[reducedQStuff==={},
	{{},{}}
	,
	(*AllQTerms = CollectTerms[reducedQStuff];
	Qmatrix = CoefficientArrays[reducedQStuff,AllQTerms][[2]];*)
	AllQTerms = CollectTerms[QStuff];
	Qmatrix = CoefficientArrays[QStuff,AllQTerms][[2]];
	{DeleteCases[SparseArray[Chop[SimpVector . Qmatrix ]]//MyRowReduce,Table[0,{l,1,Length[Qmatrix[[1]]]}]], AllQTerms/.UnTimes->Times}
	]
];

(* No row reduction *)
ActQNoReduce[SimpVector_,Allterms_] :=Module[{QStuff,reducedQStuff,Qmatrix,AllQTerms},
	QStuff = table[
		Stuff[];
		Q[t]//GExpand
	,
		{t,Allterms}
	];
	QStuff = QStuff/.Times->UnTimes;
	reducedQStuff = DeleteCases[DeleteCases[QStuff,0],0.](*/.Times->UnTimes*);
	If[reducedQStuff==={},
	{{},{}}
	,
	(*AllQTerms = CollectTerms[reducedQStuff];
	Qmatrix = CoefficientArrays[reducedQStuff,AllQTerms][[2]];*)
	AllQTerms = CollectTerms[QStuff];
	Qmatrix = CoefficientArrays[QStuff,AllQTerms][[2]];
	{DeleteCases[SparseArray[Chop[SimpVector . Qmatrix ]],Table[0,{l,1,Length[Qmatrix[[1]]]}]], AllQTerms/.UnTimes->Times}
	]
];

MyNormalize[list_] := Module[{fac,rat,den,ans},
	fac = Select[Abs[list],#>0&];
	rat = Rationalize[list/Max[fac]];
	den = LCM@@Denominator[rat];
	ans = rat*den;
	ans
];

AD[charges_,degree_,NN_] := Module[{bare,ind,Qbare,Qind,grav,Allterms,SimpQVector,gravCoVector,SimpVector,QindNR,Q,Qt,M,MQ,h1,h2,h,basis},
	
	(*** Part 2 ***)
	
	bare = DeleteCases[DeleteCases[MultiTrace[charges,degree,NN],0],0.];
	ind = IndStuff[bare];
	If[numerical,
		ind = {MyNormalize[#]&/@ind[[1]],ind[[2]]};
	];
	basis = ind;
	(*Print[basis];*)
	Qind = ActQ@@ind;
	If[numerical,
		Qind = {MyNormalize[#]&/@Qind[[1]],Qind[[2]]};
	];
	QindNR = ActQNoReduce@@ind;
	If[numerical,
		QindNR = {MyNormalize[#]&/@QindNR[[1]],QindNR[[2]]};
	];
	
	M = T[(# . ind[[2]])&/@ind[[1]]]//Inverse;
	MQ = T[(# . Qind[[2]])&/@Qind[[1]]]//Inverse;
	Q = LinearSolve[Transpose[Qind[[1]]],Transpose[QindNR[[1]]]];
	Qt = Transpose[Q];
	h2 = M . Qt . MQ . Q;
	
	h2/2
	
	(* TODO *)
	(*
	(*** Part 1 ***)
	
	bare = DeleteCases[DeleteCases[MultiTrace[charges,degree-1,NN],0],0.];
	If[Length[bare]==0,Return[h2/2]];
	ind = IndStuff[bare];
	If[numerical,
		ind = {MyNormalize[#]&/@ind[[1]],ind[[2]]};
	];
	
	(*Qind = ActQ@@ind;
	If[numerical,
		Qind = {MyNormalize[#]&/@Qind[[1]],Qind[[2]]};
	];
	Qind = CoefficientArrays[Qind[[1]].Qind[[2]]/.Times->UnTimes,basis[[2]]/.Times->UnTimes];
	Print[Qind];
	a = Qind[[1]];
	b = basis[[1]];
	Qind = LinearSolve[Qind[[1]],basis[[1]]];
	Print[Qind];
	Return[];*)
	
	QindNR = ActQNoReduce@@ind;
	If[numerical,
		QindNR = {MyNormalize[#]&/@QindNR[[1]],QindNR[[2]]};
	];
	
	tmp = QindNR;
	b = basis;
	Return[];
	
	QindNR = CoefficientArrays[QindNR[[1]].QindNR[[2]]/.Times->UnTimes,basis[[2]]/.Times->UnTimes];
	Q = LinearSolve[Transpose[QindNR[[1]]],Transpose[basis[[1]]]];
	Return[Q];
	
	M = T[(#.ind[[2]])&/@ind[[1]]]//Inverse;
	MQ = T[(#.Qind[[2]])&/@Qind[[1]]]//Inverse;
	Q = LinearSolve[Transpose[Qind[[1]]],Transpose[QindNR[[1]]]];
	Qt = Transpose[Q];
	h1 = MQ . Q . M . Qt;
	
	h = (h1 + h2)/2;
	h*)
];
(* CM *)


(* ::Section:: *)
(*Test *)


Get[#]&/@FileNames[multiDirectory<>"*"<>ToString[NN]<>".mx"];


(* ::Subsection:: *)
(*AD*)


AD[{0,0,1,1,2},3,3]


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
