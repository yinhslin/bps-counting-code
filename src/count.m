(* ::Package:: *)

(* ::Section:: *)
(*Count*)


(* ::Subsubsection:: *)
(*Multi-trace and Multi-graviton*)


minDeg -= 1;

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
	
MultiGraviton[charges_,degree_,NN_] := Module[{level,filename,ans},
	level = charges . levelvector;
	filename = multiGravitonDirectory<>ToString[level]<>"_"<>StringRiffle[ToString[#]&/@charges,"_"]<>"_"<>ToString[degree]<>"_"<>ToString[NN]<>".mx";
	If[FileExistsQ[filename],
		Get[filename];
	,
		Return[{}];
	];
	ans = multiGraviton[charges,degree,NN];
	Clear[multiGraviton];
	ans
	];


(* ::Subsubsection:: *)
(*Q and Non-commutative multiply*)


Stuff[] := Module[{},
	(* index relations *)
	Log2NN=Log[2,NN]//Ceiling;
	index[a1_,a2_,a3_,a4_,a5_,i_,j_]:=Mod[a3+a4+a5+1,2]*2^(2*Log2NN+11)+a1*2^(2*Log2NN+7)+a2*2^(2*Log2NN+3)+a3*2^(2*Log2NN+2)+a4*2^(2*Log2NN+1)+a5*2^(2*Log2NN)+(i-1)*2^Log2NN+(j-1);
	fp[a_]:=Quotient[a,2^(2*Log2NN+11)];
	nz1[a_]:=Quotient[Mod[a,2^(2*Log2NN+11)],2^(2*Log2NN+7)];
	nz2[a_]:=Quotient[Mod[a,2^(2*Log2NN+7)],2^(2*Log2NN+3)];
	n\[Theta]1[a_]:=Quotient[Mod[a,2^(2*Log2NN+3)],2^(2*Log2NN+2)];
	n\[Theta]2[a_]:=Quotient[Mod[a,2^(2*Log2NN+2)],2^(2*Log2NN+1)];
	n\[Theta]3[a_]:=Quotient[Mod[a,2^(2*Log2NN+1)],2^(2*Log2NN)];
	mati[a_]:=Quotient[Mod[a,2^(2*Log2NN)],2^Log2NN]+1;
	matj[a_]:=Mod[a,2^Log2NN]+1;

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
	If[specialQ&&(!spQ),
		X[a_] := -Sum[X[index[nz1[a],nz2[a],n\[Theta]1[a],n\[Theta]2[a],n\[Theta]3[a],k,k]],{k,1,NN-1}]/;mati[a]==NN&&matj[a]==NN;
	];
	If[spQ,
		X[a_] := - X[index[nz1[a],nz2[a],n\[Theta]1[a],n\[Theta]2[a],n\[Theta]3[a],matj[a]+NN/2,mati[a]+NN/2]]/;NN/2>=mati[a]&&NN/2>=matj[a];
		X[a_] := X[index[nz1[a],nz2[a],n\[Theta]1[a],n\[Theta]2[a],n\[Theta]3[a],matj[a]+NN/2,mati[a]-NN/2]]/;NN/2<mati[a]&&NN/2>=matj[a]&&mati[a]-NN/2>matj[a];
		X[a_] := X[index[nz1[a],nz2[a],n\[Theta]1[a],n\[Theta]2[a],n\[Theta]3[a],matj[a]-NN/2,mati[a]+NN/2]]/;NN/2>=mati[a]&&NN/2<matj[a]&&mati[a]+NN/2>matj[a];
	];
	If[soQ,
		X[a_] := - X[index[nz1[a],nz2[a],n\[Theta]1[a],n\[Theta]2[a],n\[Theta]3[a],matj[a],mati[a]]]/;mati[a]>matj[a];
		X[a_] := 0/;mati[a]==matj[a];
	];
	X[a_]:=0/;nz1[a]==0&&nz2[a]==0&&n\[Theta]1[a]==0&&n\[Theta]2[a]==0&&n\[Theta]3[a]==0;

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
	(*qr = "/n/home07/yhlin/bps/src/qrX.jl";*)
	Switch[user,
		"yhlin", qr = "/n/home07/yhlin/bps/src/qr.jl"
		,
		"zhangqim", qr = "/home/zhangqim/WORK/Q_coho/src/qr.jl"
		,
		_, qr = home <> "qr.jl"
	];
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
		reducedTraces=traces/.Times->UnTimes/.Power->UnPower;
		Allterms=CollectTerms[reducedTraces];
		CoVector=CoefficientArrays[reducedTraces,Allterms][[2]];
		SimpVector = DeleteCases[CoVector//MyRowReduce,Table[0,{l,1,Length[CoVector[[1]]]}]];
		{SimpVector , Allterms/.UnTimes->Times/.UnPower->Power}
	]
];

ActQ[SimpVector_,Allterms_] :=Module[{QStuff,reducedQStuff,Qmatrix,AllQTerms},
	QStuff = table[
		Stuff[];
		Q[t]//GExpand
	,
		{t,Allterms}
	];
	QStuff = QStuff/.Times->UnTimes/.Power->UnPower;
	reducedQStuff = DeleteCases[DeleteCases[QStuff,0],0.](*/.Times->UnTimes*);
	If[reducedQStuff==={},
	{{},{}}
	,
	(*AllQTerms = CollectTerms[reducedQStuff];
	Qmatrix = CoefficientArrays[reducedQStuff,AllQTerms][[2]];*)
	AllQTerms = CollectTerms[QStuff];
	Qmatrix = CoefficientArrays[QStuff,AllQTerms][[2]];
	{DeleteCases[SparseArray[Chop[SimpVector . Qmatrix ]]//MyRowReduce,Table[0,{l,1,Length[Qmatrix[[1]]]}]], AllQTerms/.UnTimes->Times/.UnPower->Power}
	]
];

MyNormalize[list_] := Module[{fac,rat,den,ans},
	fac = Select[Abs[list],#>0&];
	rat = Rationalize[list/Max[fac]];
	den = LCM@@Denominator[rat];
	ans = rat*den;
	ans
];

CountQ[charges_,degree_,NN_] := Module[{bare,ind,Qbare,Qind,grav,Allterms,SimpQVector,gravCoVector,SimpVector},
	bare = DeleteCases[DeleteCases[MultiTrace[charges,degree,NN],0],0.];
	ind = IndStuff[bare];
	If[numerical,
		ind = {MyNormalize[#]&/@ind[[1]],ind[[2]]};
	];
	Qind = ActQ@@ind;
	(* TODO *)
	
	grav = DeleteCases[DeleteCases[MultiGraviton[charges,degree+1,NN],0],0.];
	grav = grav/.Times->UnTimes/.Power->UnPower;
	If[grav=={},
		Return[Flatten[ {(*charges, degree, NN,*) Length[ind[[1]]]-Length[Qind[[1]]], Length[Qind[[1]]], 0} ]]
	];
	Allterms = DeleteDuplicates[Join[Qind[[2]],CollectTerms[grav]/.UnTimes->Times/.UnPower->Power]]/.Times->UnTimes/.Power->UnPower;
	SimpQVector = SparseArray[Qind[[1]],{Length[Qind[[1]]],Length[Allterms]}];
	gravCoVector = CoefficientArrays[grav,Allterms][[2]];
	SimpVector = DeleteCases[Join[SimpQVector,gravCoVector]//MyRowReduce,Table[0,Length[gravCoVector[[1]]]]];
	(* END TODO *)
	
	Flatten[ {(*charges, degree, NN,*) Length[ind[[1]]]-Length[Qind[[1]]], Length[Qind[[1]]], Length[SimpVector]-Length[Qind[[1]]]} ]
];
(* CM *)


(* ::Section:: *)
(*Execute*)


Exec[] := Module[{},
	filename = countDirectory<>ToString[level]<>"_"<>StringRiffle[ToString[#]&/@charges,"_"]<>"_"<>ToString[degree]<>"_"<>ToString[NN]<>".csv";
	If[!FileExistsQ[filename],
		ClearAll[countQ];
		TimeConstrained[
			Check[
				countQ[charges,degree,NN] = CountQ[charges,degree,NN];
			,
				Print["> terminated due to error"];
				ResetKernels[];
				Continue[];
			];
			Export[filename,{countQ[charges,degree,NN]}];
			tmp = Import[filename,"CSV"];
			(*Print[countQ[charges,degree,NN], " ", tmp[[1]]];*)
			(*Print["> ", tmp[[1]] === countQ[charges,degree,NN]];*)
			(*If[
				tmp[[1]] =!= countQ[charges,degree,NN]
				,
				Print["PROBLEM!"];
				Quit[];
			];*)
			If[tmp[[1]] =!= countQ[charges,degree,NN],
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
