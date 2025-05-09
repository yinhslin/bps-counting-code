(* ::Package:: *)

(* ::Section:: *)
(*Anomalous dimension*)


(* ::Subsubsection::Closed:: *)
(*Multi-trace*)


MultiTrace[charges_,degree_,NN_] := Module[{level,filename,ans},
	level = charges . levelvector;
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
(*Numerical*)


(* ::Text:: *)
(*Install Julia from https://julialang.org/*)
(*Install necessary packages by running the following commands within Julia:*)
(*import(Pkg);*)
(*Pkg.add(["LinearAlgebra", "SparseArrays", "SuiteSparse", "DelimitedFiles", "DoubleFloats", "MultiFloats", "MatrixMarket", "RowEchelon", "ZChop", "JLD2"]);*)


If[numerical,
	Switch[user,
		"yhlin", 
			julia = "julia";
			qr = "/n/home07/yhlin/bps/src/qr.jl";
			qr = StringReplace[StringReplace[qr,{" "->"\ "}],{"("->"\(",")"->"\)","\ "->"\\\ "}];
		,
		_,
			julia = "/Applications/Julia-1.6.app/Contents/Resources/julia/bin/julia";
			qr = Directory[] <> "/qr.jl";
	];
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


(* ::Subsubsection:: *)
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
	2^(-4-2a1-2a2)*a1!*a2!*(a1+a2+a3+a4+a5-1)!/norm
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
	Product[t[[2]]!*factor[t[[1,1]]]^(t[[2]]),{t,t1}]
];

(* TO DEPRECIATE *)
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

(* TO DEPRECIATE *)
(* Inner product of polynomials using 2-finger algorithm *)
(*IP[p1_,p2_]:=Module[{l1,l2,i=1,j=1,ans,comp},
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
];*)

(* Valid for U(N) and SU(2) *)
(* T-matrix for list of monomials *)

(* original *)
TDiag[l_]:=Module[{ans},
	ans=SparseArray[{},{Length[l],Length[l]}];
	Do[
		ans[[i,i]]=IPmono[l[[i]],l[[i]]]
	,
		{i,1,Length[l]}
	];
	ans
];

(* TODO *)
(* transpose *)
(*SwapIJ[n_]:=2^4*Quotient[n,2^4]+(matj[n]-1)*2^2+(mati[n]-1);
TDiag[l_]:=Module[{tp,j,ans},
	ans=SparseArray[{},{Length[l],Length[l]}];
	Do[
		tp=l[[i]]/.X[n_]:>X[SwapIJ[n]]/.-expr_:>expr;
		j=Position[l,tp][[1,1]];
		ans[[i,j]]=IPmono[l[[i]],l[[i]]];
	,
		{i,1,Length[l]}
	];
	ans
];*)

(* TO DEPRECIATE *)
(*T[l1_,l2_]:=Module[{i=1,j=1,ans,comp,ord1,ord2,ll1,ll2},
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
];*)

(* (3.6-3.8) *)
SetIJ[n_,i_,j_]:=2^4*Quotient[n,2^4]+(i-1)*2^2+(j-1);
Sub[n_]:=Module[{i,j},
	{i,j}={mati[n],matj[n]};
	If[i==j,
		Switch[NN,
			3,
				Switch[i,
					1, -X[n]+X[SetIJ[n,2,2]],
					2, X[SetIJ[n,1,1]]+X[n]
				],
			4,
				Switch[i,
					1, -X[n]-X[SetIJ[n,2,2]]+X[SetIJ[n,3,3]],
					2, 2X[n]+X[SetIJ[n,3,3]],
					3, X[SetIJ[n,1,1]]-X[SetIJ[n,2,2]]+X[n]
				]
		]
	,
		X[n]
	]
]/;specialQ&&NN>2;
Sub[n_]:=X[n]/;!specialQ||NN==2;

CollectTerms[lis_]:=DeleteCases[DeleteDuplicates[Flatten[lis/.Plus->List/.{n_ a_:>a/;NumericQ[n]}/.{-a_:>a}]],0];

(* T-matrix for list of polynomials *)
UnTimes[n_,a__]:=n UnTimes[a]/;NumericQ[n];
UnTimes[a_]:=a;
Un[a_]:=a/.Power->UnPower/.Times->UnTimes;
Nu[a_]:=a/.UnTimes->Times/.UnPower->Power;
T[l_]:=Module[{ll,allTerms,matrix},
	ll=l/.X[n_]:>Sub[n];
	ll=(#/.nc_NonCommutativeMultiply:>Distribute[nc]//Expand)&/@ll;
	ll=ll//Un;
	allTerms = CollectTerms[ll];
	matrix = CoefficientArrays[ll,allTerms][[2]];
	allTerms = allTerms//Nu;
	(* TODO: dagger *)
	(*Print[allTerms];*)
	matrix . TDiag[allTerms] . Transpose[matrix]
];


(* ::Subsubsection:: *)
(*Anomalous dimension*)


(*(* dagger *)
SwapIJ[n_]:=2^4*Quotient[n,2^4]+(matj[n]-1)*2^2+(mati[n]-1);
DaggerPermutation[basis_]:=Module[{dag},
	dag=basis/.X[n_]:>X[SwapIJ[n]]//Un;
	CoefficientArrays[dag,basis//Un][[2]]
];
DP[basis_]:=DaggerPermutation[basis];*)

(* Basis of monomials *)
Basis[traces_]:=Module[{Allterms,reducedTraces},
	reducedTraces=traces//Un;
	Allterms=CollectTerms[reducedTraces];
	Allterms//Nu
];

(* Row reduction *)
IndStuffBasis[traces_,basis_]:=Module[{Allterms,reducedTraces,CoVector,SimpVector},
	If[traces=={},{{},{}},
		reducedTraces=traces//Un;
		CoVector=CoefficientArrays[reducedTraces,basis//Un][[2]];
		SimpVector = DeleteCases[CoVector//MyRowReduce,Table[0,{l,1,Length[CoVector[[1]]]}]];
		SparseArray[SimpVector]
	]
];

MyNormalize[list_] := Module[{fac,rat,den,ans},
	fac = Select[Abs[list],#>0&];
	rat = Rationalize[list/Max[fac]];
	den = LCM@@Denominator[rat];
	ans = rat*den;
	ans
];

(* Basis and IndStuffBasis together *)
GetBasis[charges_,degree_,NN_]:=Module[{bare,basis,Ared},
	bare = DeleteCases[DeleteCases[MultiTrace[charges,degree,NN],0],0.];
	If[Length[bare]==0,
		Return[{{},{{}}(*,{}*)}]
	];
	basis = Basis[bare];
	Ared = IndStuffBasis[bare,basis];
	If[numerical,
		Ared = MyNormalize[#]&/@Ared;
	];
	Ared = Transpose[Ared];
	{basis,Ared(*,DP[basis]*)}
];

(* Extract Q matrix in given bases *)
ActQBasis[cur_,next_] :=Module[{QStuff,reducedQStuff,Qmatrix,AllQTerms,t},
	QStuff = table[
		Stuff[];
		Q[t]//GExpand
	,
		{t,cur}
	];
	QStuff = QStuff//Un;
	reducedQStuff = DeleteCases[DeleteCases[QStuff,0],0.];
	If[reducedQStuff==={},
	SparseArray[{},{Length[next],Length[cur]}]
	(*{{},{}}*)
	,
	Qmatrix = CoefficientArrays[QStuff,next//Un][[2]];
	Qmatrix = Transpose[Qmatrix];
	Qmatrix
	]
];

H[charges_,degree_,NN_] := H[charges,degree,NN] = Module[{basis,Ared,TT,M,invM,q,QQ,h,HH,dp,dim},
	(* prev (-1) -> cur (0) -> next (1) *)
	
	Do[
		Print["p", " ", Timing[
			{basis[i],Ared[i](*,dp[i]*)} = GetBasis[charges,degree+i,NN];
		][[1]], " ", i];
		(*Ared[i] = N[Ared[i]];*)
		dim[i] = Dimensions[Ared[i]][[2]];
		
		If[i==0 && dim[0]==0, Break[]];
		
		If[
			Length[basis[i]]>0
		,
		Print["T", " ", Timing[
			TT[i] = T[basis[i]];
			(*TT[i] = N[TT[i]];*)
			M[i] = Transpose[Ared[i]] . TT[i] . Ared[i];
			invM[i] = SparseArray[Inverse[M[i]]];
			][[1]], " ", i];
		];

		If[i==-1,
			If[Length[basis[-1]]>0
			,
			Print["-", " ", Timing[
				q[-1] = ActQBasis[basis[-1],basis[0]];
				(*q[-1] = N[q[-1]];*)
				QQ[-1] = Transpose[Ared[0]] . TT[0] . q[-1] . Ared[-1];
				HH[-1] = 2 * QQ[-1] . invM[-1] . Transpose[QQ[-1]];
				h[-1] = 2 * invM[0] . QQ[-1] . invM[-1] . Transpose[QQ[-1]];
			][[1]]];
			,
				h[-1] = SparseArray[{},{dim[0],dim[0]}];
			];
		];
		
		If[i==1,
			If[Length[basis[1]]>0
			,
			Print["1", " ", Timing[
				q[0] = ActQBasis[basis[0],basis[1]];
				(*q[0] = N[q[0]];*)
				QQ[0] = Transpose[Ared[1]] . TT[1] . q[0] . Ared[0];
				HH[0] = 2 * Transpose[QQ[0]] . invM[1] . QQ[0];
				h[0] = 2 * invM[0] . Transpose[QQ[0]] . invM[1] . QQ[0];
			][[1]]];
			,
				h[0] = SparseArray[{},{dim[0],dim[0]}];
			];
		];
	,
		{i,{0,-1,1}}
	];
	
	If[dim[0]==0, Return[{{}}]];
	
	(h[-1]+h[0])
];

AD[charges_,degree_,NN_] := Module[{HH=H[charges,degree,NN],tmp},
	tmp = If[HH==={{}},
		{},
		Eigenvalues[Normal[N[HH]]]
	];
	tmp = If[Element[Round[#,10^-5],Integers],Round[#],N[Round[#,10^-5]]]&/@tmp;
	tmp = Join[{charges . levelvector,charges,degree,NN},tmp]//Flatten;
	tmp
];


(* ::Section:: *)
(*Execute*)


Exec[] := Module[{},
	filenameH = hDirectory<>ToString[level]<>"_"<>StringRiffle[ToString[#]&/@charges,"_"]<>"_"<>ToString[degree]<>"_"<>ToString[NN]<>".m";
	filenameHmtx = hDirectory<>ToString[level]<>"_"<>StringRiffle[ToString[#]&/@charges,"_"]<>"_"<>ToString[degree]<>"_"<>ToString[NN]<>".mtx";
	filename = adDirectory<>ToString[level]<>"_"<>StringRiffle[ToString[#]&/@charges,"_"]<>"_"<>ToString[degree]<>"_"<>ToString[NN]<>".csv";
	If[!FileExistsQ[filename],
		Share[];
		ClearAll[ad];
		TimeConstrained[
			Check[
				Print["h", " ", Timing[h[charges,degree,NN] = H[charges,degree,NN]][[1]]];
				ad[charges,degree,NN] = AD[charges,degree,NN];
			,
				Print["> terminated due to error"];
				ResetKernels[];
				Continue[];
			];
			Save[filenameH,h];
			If[h[charges,degree,NN]=!={{}}, Export[filenameHmtx,h[charges,degree,NN]]];
			Export[filename,{ad[charges,degree,NN]}];
			tmp = Import[filename,"CSV"]//ToExpression;
			(*Print[ad[charges,degree,NN], " ", tmp[[1]]];*)
			(*Print["> ", tmp[[1]] === ad[charges,degree,NN]];*)
			(*If[
				tmp[[1]] =!= ad[charges,degree,NN]
				,
				Print["PROBLEM!"];
				Quit[];
			];*)
			If[Length[tmp]>0 && tmp[[1]] =!= ad[charges,degree,NN],
				Print[tmp[[1]]];
				Print[ad[charges,degree,NN]];
				DeleteFile[filename];
			];
		,
			time
		,
			Print["> overtime"];
			ResetKernels[];
		];
	];
];
