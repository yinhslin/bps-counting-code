(* ::Package:: *)

(* ::Section:: *)
(*Anomalous dimension*)


(* ::Subsubsection::Closed:: *)
(*Multi-trace*)


SingleTrace[charges_,degree_] := Module[{level,filename,ans},
	level = charges . {3,3,2,2,2};
	filename = singleDirectory<>ToString[level]<>"_"<>StringRiffle[ToString[#]&/@charges,"_"]<>"_"<>ToString[degree]<>"_P"<>".mx";
	If[FileExistsQ[filename],
		Get[filename];
	,
		Return[{}];
	];
	ans = singleTrace[charges,degree];
	Clear[singleTrace];
	ans
	];


(* ::Subsubsection::Closed:: *)
(*Q and Non-commutative multiply*)


Stuff[] := Module[{},
	(* index relations *)
	index[a1_,a2_,a3_,a4_,a5_]:=Mod[a3+a4+a5+1,2]*2^15+a1*2^11+a2*2^7+a3*2^6+a4*2^5+a5*2^4;
	fp[a_]:=Quotient[a,2^15];
	nz1[a_]:=Quotient[Mod[a,2^15],2^11];
	nz2[a_]:=Quotient[Mod[a,2^11],2^7];
	n\[Theta]1[a_]:=Quotient[Mod[a,2^7],2^6];
	n\[Theta]2[a_]:=Quotient[Mod[a,2^6],2^5];
	n\[Theta]3[a_]:=Quotient[Mod[a,2^5],2^4];

	(* Q action *)
	Q[a_Plus]:=Q[#]&/@a;
	Q[n_ a_]:=n Q[a]/;NumericQ[n];
	Q[n_]:=0/;NumericQ[n];
	Q[a_NonCommutativeMultiply]:=Module[{alist,sign,A},
		alist=Apply[List,a];
		sign=1;A=0;
		Do[A=A+sign NonCommutativeMultiply@@(ReplacePart[alist,n->Q[alist[[n]]]]);
			sign=sign (-1)^Grading[alist[[n]]];
		,{n,alist//Length}];
		A
	];
	Q[X[a_]]:=Module[{g=fp[a],L1=nz1[a],L2=nz2[a],M1=n\[Theta]1[a],M2=n\[Theta]2[a],M3=n\[Theta]3[a]},
		Sum[(-1)^(m1+m2+m3+(M2-m2)m3+(M1-m1)(m2+m3)) 
			Binomial[L1,l1] Binomial[L2,l2] 
			X[index[l1,l2,m1,m2,m3]]**X[index[L1-l1,L2-l2,M1-m1,M2-m2,M3-m3]]
			,{l1,0,L1},{l2,0,L2},{m1,0,M1},{m2,0,M2},{m3,0,M3}]
	];

	(* matrix and product *)
	X[a_]:=0/;Quotient[a,2^5]==2^10;

	Grading[ a_Plus ] := Max @@ (Grading /@ (List @@ a));
	Grading[ a_List ] := Plus @@ (Grading /@ (List @@ a));
	(*Grading[ a_Times ] := Plus @@ (Grading /@ (List @@ a));*)
	Grading[ n_ a_ ]:= Grading[ a ]/;NumericQ[n];
	Grading[ a_NonCommutativeMultiply ] := Plus @@ (Grading /@ (List @@ a));
	Grading[ _ ] := 0;
	Grading[ a_X ] := fp[a[[1]]];
	
	Unprotect[NonCommutativeMultiply];
	NonCommutativeMultiply[a___,n_ c__,b___]:=n NonCommutativeMultiply[a,c,b]/;NumberQ[n];
	NonCommutativeMultiply[a__,n_,b__]:= n NonCommutativeMultiply[a,b]/;NumberQ[n];
	NonCommutativeMultiply[n_,a__]:= n NonCommutativeMultiply[a]/;NumberQ[n];
	NonCommutativeMultiply[a__,n_]:= n NonCommutativeMultiply[a]/;NumberQ[n];
	Protect[NonCommutativeMultiply];
	
	GExpand[a_, patt___] := Expand[a //. {x_NonCommutativeMultiply :> Distribute[x]}, patt];
	CyclicOrdering[ a_NonCommutativeMultiply ]:=Module[{aList,cyclicList},
		aList = List@@a;
		cyclicList = Table[(-1)^( Grading[aList[[1;;i]]]*Grading[aList[[(i+1);;]]] ) NonCommutativeMultiply@@RotateLeft[aList,i]
			,{i,1,Length[aList]}];
		If[MemberQ[cyclicList,x_/;MemberQ[cyclicList,-x]],
			0
			,
			Last[Sort[cyclicList]]
		]
	];
	CyclicOrdering[ a_Plus ]:= Plus @@ (CyclicOrdering /@ (List @@ a));
	CyclicOrdering[ n_ a_ ]:= n CyclicOrdering[ a ]/;NumericQ[n];
	CyclicOrdering[ n_ ]:= n/;NumericQ[n];
	
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
	n=Quotient[n,2^4];
	a5=Mod[n,2^1];
	n=Quotient[n-a5,2^1];
	a4=Mod[n,2^1];
	n=Quotient[n-a4,2^1];
	a3=Mod[n,2^1];
	n=Quotient[n-a3,2^1];
	a2=Mod[n,2^4];
	n=Quotient[n-a2,2^4];
	a1=Mod[n,2^4];
	{a1,a2,a3,a4,a5}
];

(* (3.30) and (3.6-3.8) *)
factor[m_]:=Module[{a1,a2,a3,a4,a5},
	{a1,a2,a3,a4,a5}=decode[m];
	2^(1-2a1-2a2)*a1!*a2!*(a1+a2+a3+a4+a5-1)!
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

(* T-matrix for list of monomials *)
(* original *)
(*TDiag[l_]:=Module[{ans},
	ans=SparseArray[{},{Length[l],Length[l]}];
	Do[
		ans[[i,i]]=IPmono[l[[i]],l[[i]]]
	,
		{i,1,Length[l]}
	];
	ans
];*)
SymmetryFactor[list_]:=Module[{cyc},
	(*cyc=Table[Permute[list,c],{c,GroupElements[CyclicGroup[Length[list]]]}];*)
	cyc=Permute[list,CyclicGroup[Length[list]]];
	Length[cyc]/Length[DeleteDuplicates[cyc]]
];
TDiag[l_]:=Module[{ans,factors},
	ans=SparseArray[{},{Length[l],Length[l]}];
	Do[
		factors=List@@(l[[i]]);
		ans[[i,i]]=SymmetryFactor[factors]*Product[factor[f[[1]]],{f,factors}];
	,
		{i,1,Length[l]}
	];
	ans
];

CollectTerms[lis_]:=DeleteCases[DeleteDuplicates[Flatten[lis/.Plus->List/.{n_ a_:>a/;NumericQ[n]}/.{-a_:>a}]],0];

(* T-matrix for list of polynomials *)
(*UnTimes[n_,a__]:=n UnTimes[a]/;NumericQ[n];
UnTimes[a_]:=a;*)
Un[a_]:=a(*/.Power->UnPower/.Times->UnTimes*);
Nu[a_]:=a(*/.UnTimes->Times/.UnPower->Power*);
T[l_]:=Module[{ll,allTerms,matrix},
	ll=l(*/.X[n_]:>Sub[n]*);
	ll=(#/.nc_NonCommutativeMultiply:>Distribute[nc]//Expand)&/@ll;
	ll=ll//Un;
	allTerms = CollectTerms[ll];
	matrix = CoefficientArrays[ll,allTerms][[2]];
	allTerms = allTerms//Nu;
	matrix . TDiag[allTerms] . Transpose[matrix]
];


(* ::Subsubsection::Closed:: *)
(*Anomalous dimension*)


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
GetBasis[charges_,degree_]:=Module[{bare,basis,Ared},
	bare = DeleteCases[DeleteCases[SingleTrace[charges,degree],0],0.];
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
		Q[t]//GExpand//CyclicOrdering
	,
		{t,cur}
	];
	QStuff = QStuff//Un;
	reducedQStuff = DeleteCases[DeleteCases[QStuff,0],0.];
	If[reducedQStuff==={},
	{{},{}}
	,
	Qmatrix = CoefficientArrays[QStuff,next//Un][[2]];
	Qmatrix = Transpose[Qmatrix];
	Qmatrix
	]
];

H[charges_,degree_] := H[charges,degree] = Module[{basis,Ared,TT,M,invM,q,QQ,h,HH,dp,dim},
	(* prev (-1) -> cur (0) -> next (1) *)
	
	Do[
		Print["p", " ", Timing[{basis[i],Ared[i](*,dp[i]*)} = GetBasis[charges,degree+i]][[1]], " ", i];
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
	
	(h[-1]+h[0])/32
];

AD[charges_,degree_] := Module[{HH=H[charges,degree],tmp},
	tmp = If[HH==={{}},
		{},
		Eigenvalues[Normal[N[HH]]]
	];
	tmp = If[Element[Round[#,10^-5],Integers],Round[#],N[Round[#,10^-5]]]&/@tmp;
	tmp = Join[{charges . {3,3,2,2,2},charges,degree},tmp]//Flatten;
	tmp
];


(* ::Section:: *)
(*Execute*)


Exec[] := Module[{},
	filename = adDirectory<>ToString[level]<>"_"<>StringRiffle[ToString[#]&/@charges,"_"]<>"_"<>ToString[degree]<>"_P"<>".csv";
	If[!FileExistsQ[filename],
		Share[];
		ClearAll[ad];
		TimeConstrained[
			Check[
				Print["h", " ", Timing[h[charges,degree] = H[charges,degree]][[1]]];
				ad[charges,degree] = AD[charges,degree];
			,
				Print["> terminated due to error"];
				ResetKernels[];
				Continue[];
			];
			Export[filename,{ad[charges,degree]}];
			tmp = Import[filename,"CSV"]//ToExpression;
			If[Length[tmp]>0 && tmp[[1]] =!= ad[charges,degree],
				Print[tmp[[1]]];
				Print[ad[charges,degree]];
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
