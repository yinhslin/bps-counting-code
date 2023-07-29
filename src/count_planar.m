(* ::Package:: *)

(* ::Section:: *)
(*Count*)


(* ::Subsubsection:: *)
(*Single-trace*)


minDeg -= 1;

SingleTrace[charges_,degree_] := Module[{level,filename,ans},
	level = charges . levelvector;
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



(* ::Subsubsection:: *)
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


(* ::Subsubsection:: *)
(*Numerical*)


(* ::Text:: *)
(*Install Julia from https://julialang.org/*)
(*Install necessary packages by running the following commands within Julia:*)
(*import(Pkg);*)
(*Pkg.add(["LinearAlgebra", "SparseArrays", "SuiteSparse", "DelimitedFiles", "DoubleFloats", "MultiFloats", "MatrixMarket", "RowEchelon", "ZChop", "JLD2"]);*)


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


(* ::Subsubsection:: *)
(*Independence*)


CollectTerms[lis_]:=DeleteCases[DeleteDuplicates[Flatten[lis/.Plus->List/.{n_ a_:>a/;NumericQ[n]}/.{-a_:>a}]],0];

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
		Q[t]//GExpand//CyclicOrdering
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

MyNormalize[list_] := Module[{fac,rat,den,ans},
	fac = Select[Abs[list],#>0&];
	rat = Rationalize[list/Max[fac]];
	den = LCM@@Denominator[rat];
	ans = rat*den;
	ans
];

CountQ[charges_,degree_] := Module[{bare,ind,Qbare,Qind},
	bare = DeleteCases[DeleteCases[SingleTrace[charges,degree],0],0.];
	ind = IndStuff[bare];
	If[numerical,
		ind = {MyNormalize[#]&/@ind[[1]],ind[[2]]};
	];
	Qind = ActQ@@ind;
	
	Flatten[ {(*charges, degree, NN,*) Length[ind[[1]]]-Length[Qind[[1]]], Length[Qind[[1]]]} ]
];
(* CM *)


(* ::Section:: *)
(*Execute*)


Exec[] := Module[{},
	filename = countDirectory<>ToString[level]<>"_"<>StringRiffle[ToString[#]&/@charges,"_"]<>"_"<>ToString[degree]<>"_P"<>".csv";
	If[!FileExistsQ[filename],
		ClearAll[countQ];
		TimeConstrained[
			Check[
				countQ[charges,degree] = CountQ[charges,degree];
			,
				Print["> terminated due to error"];
				ResetKernels[];
				Continue[];
			];
			Export[filename,{countQ[charges,degree]}];
			tmp = Import[filename,"CSV"];
			(*Print[countQ[charges,degree,NN], " ", tmp[[1]]];*)
			(*Print["> ", tmp[[1]] === countQ[charges,degree,NN]];*)
			(*If[
				tmp[[1]] =!= countQ[charges,degree,NN]
				,
				Print["PROBLEM!"];
				Quit[];
			];*)
			If[tmp[[1]] =!= countQ[charges,degree],
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
