(* ::Package:: *)

(* ::Section:: *)
(*Count*)


(* ::Subsubsection:: *)
(*Multi-trace and Multi-graviton*)


minDeg -= 1;
	
MultiGraviton[charges_,degree_,NN_] := Module[{level,filename,ans},
	level = charges . {3,3,2,2,2};
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


(* ::Subsubsection::Closed:: *)
(*Non-commutative multiply*)


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

MyNormalize[list_] := Module[{fac,rat,den,ans},
	fac = Select[Abs[list],#>0&];
	rat = Rationalize[list/Max[fac]];
	den = LCM@@Denominator[rat];
	ans = rat*den;
	ans
];

CountGrav[charges_,degree_,NN_] := Module[{grav,Allterms,gravCoVector,SimpVector},
	grav = DeleteCases[DeleteCases[MultiGraviton[charges,degree+1,NN],0],0.];
	grav = grav/.Times->UnTimes;
	If[grav=={},
		Return[ {0} ]
	];
	Allterms = DeleteDuplicates[CollectTerms[grav]/.UnTimes->Times]/.Times->UnTimes;	
	If[Length[Allterms]==1,
		gravCoVector = SparseArray[({grav/Allterms[[1]]})//Transpose];
		,
		gravCoVector = CoefficientArrays[grav,Allterms][[2]];
		];
	SimpVector = DeleteCases[gravCoVector//MyRowReduce,Table[0,Length[gravCoVector[[1]]]]];
	(* END TODO *)
	
	Flatten[ {(*charges, degree, NN,*) Length[SimpVector] } ]
];
(* CM *)


(* ::Section:: *)
(*Execute*)


Exec[] := Module[{},
	filename = countDirectory<>ToString[level]<>"_"<>StringRiffle[ToString[#]&/@charges,"_"]<>"_"<>ToString[degree]<>"_"<>ToString[NN]<>".csv";
	If[!FileExistsQ[filename],
		ClearAll[countGrav];
		TimeConstrained[
			Check[
				countGrav[charges,degree,NN] = CountGrav[charges,degree,NN];
			,
				Print["> terminated due to error"];
				ResetKernels[];
				Continue[];
			];
			Export[filename,{countGrav[charges,degree,NN]}];
			tmp = Import[filename,"CSV"];
			(*Print[countQ[charges,degree,NN], " ", tmp[[1]]];*)
			(*Print["> ", tmp[[1]] === countQ[charges,degree,NN]];*)
			(*If[
				tmp[[1]] =!= countQ[charges,degree,NN]
				,
				Print["PROBLEM!"];
				Quit[];
			];*)
			If[tmp[[1]] =!= countGrav[charges,degree,NN],
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