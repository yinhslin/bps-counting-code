(* ::Package:: *)

(* ::Section:: *)
(*Independent Exact*)


(* ::Subsubsection:: *)
(*Q-exact*)


IndependentOperator[charges_,degree_,NN_] := Module[{level,filename,ans},
	level = charges . levelvector;
	filename = operatorDirectory<>ToString[level]<>"_"<>StringRiffle[ToString[#]&/@charges,"_"]<>"_"<>ToString[degree]<>"_"<>ToString[NN]<>".mx";
	If[FileExistsQ[filename],
		Get[filename];
	,
		Return[{{},{}}];
	];
	ans = independentOperator[charges,degree,NN];
	Clear[independentOperator];
	ans
];
Exact[charges_,degree_,NN_] := Module[{level,filename,ans},
	level = charges . levelvector;
	filename = exactDirectory<>ToString[level]<>"_"<>StringRiffle[ToString[#]&/@charges,"_"]<>"_"<>ToString[degree]<>"_"<>ToString[NN]<>".mx";
	If[FileExistsQ[filename],
		Get[filename];
	,
		Return[{}];
	];
	ans = exact[charges,degree,NN];
	Clear[exact];
	ans
];


(* ::Subsubsection:: *)
(*Numerical*)


(* ::Text:: *)
(*Install Julia from https://julialang.org/*)
(*Install necessary packages by running the following commands within Julia:*)
(*import(Pkg);*)
(*Pkg.add(["LinearAlgebra", "SparseArrays", "SuiteSparse", "DelimitedFiles", "DoubleFloats", "MultiFloats", "MatrixMarket", "RowEchelon", "ZChop", "JLD2"]);*)


(*If[numerical,
	julia = "julia";
	(*qr = home <> "qr.jl";*)
	qr = GetEnvironment["HOME"][[2]]<>"/projects/bps/src/qrC.jl";
	qr = StringReplace[StringReplace[qr,{" "->"\ "}],{"("->"\(",")"->"\)","\ "->"\\\ "}];
	(* A must be a sparse matrix *)
	MyRowReduce[A_] := Module[{ans,id,dir,dirX},
		Print["density: ", A["Density"]];
		Print["dimensions: ", Dimensions[A]];
		id = ToString[RandomInteger[10^10]];
		dir = juliaDirectory<>id<>"/";
		While[FileExistsQ[dir],
			id = ToString[RandomInteger[10^10]];
			dir = juliaDirectory<>id<>"/";
		];
		Print[dir];
		dirX = StringReplace[dir,{"("->"\(",")"->"\)","\ "->"\\\ "}];
		Print["Exporting "<>dir<>"in.mtx"];
		Export[dir<>"in.mtx",A];
		Print["Exported "<>dir<>"in.mtx"];
		Print["Running Julia"];
		Run[julia<>" "<>qr<>" Float64 1e-10 "<>dirX<>"in.mtx"<>" "<>dirX<>"out.txt"];
		Print["Finished Julia"];
		Print["Exported to "<>dir<>"out.txt"];
		ans = A[[ Sort[ Transpose[ Import[dir<>"out.txt","Table"] ][[1]] ] ]];
		ans
	];
,
	MyRowReduce := RowReduce;
];*)

(*If[numerical,
	julia = "julia";
	(*qr = home <> "qr.jl";*)
	qr = GetEnvironment["HOME"][[2]]<>"/projects/bps/src/qr.jl";
	qr = StringReplace[StringReplace[qr,{" "->"\ "}],{"("->"\(",")"->"\)","\ "->"\\\ "}];
	(* A must be a sparse matrix *)
	MyRowReduce[A_] := Module[{ans,id,dir,dirX},
		Print["density: ", A["Density"]];
		Print["dimensions: ", Dimensions[A]];
		id = ToString[RandomInteger[10^10]];
		dir = juliaDirectory<>id<>"/";
		While[FileExistsQ[dir],
			id = ToString[RandomInteger[10^10]];
			dir = juliaDirectory<>id<>"/";
		];
		Print[dir];
		dirX = StringReplace[dir,{"("->"\(",")"->"\)","\ "->"\\\ "}];
		Print["Exporting "<>dir<>"in.mtx"];
		Export[dir<>"in.mtx",A];
		Print["Exported "<>dir<>"in.mtx"];
		Print["Running Julia"];
		Run[julia<>" "<>qr<>" Float64 1e-5 "<>dirX<>"in.mtx"<>" "<>dirX<>"out.mtx"];
		Print["Finished Julia"];
		Print["Exported to "<>dir<>"out.mtx"];
		Print["Spliting mtx file"];
		Run["bash ~/projects/bps/src/split.sh "<>juliaDirectory<>id<>"/out.mtx "<>juliaDirectory<>id<>"/chunks "<>ToString[800000000]];
		Print["Reading mtx files"];
		Do[
			sub[f] = Import[f,"MTX"];
			,
			{f,FileNames["*",juliaDirectory<>id<>"/chunks"]}
		];
		Print["Summing sparse matrices"];
		ans = Sum[sub[f],{f,FileNames["*",juliaDirectory<>id<>"/chunks"]}];
		(*DeleteFile[dir<>"in.mtx"];
		DeleteFile[dir<>"out.mtx"];
		DeleteDirectory[dir];*)
		ans
	];
,
	MyRowReduce := RowReduce;
];
*)

(*ExportMatrix[filename_, A_] := Module[{dims, rules, II, J, V, m, n},
	dims = Dimensions[A];
	rules = Most @ ArrayRules[A];
	II = rules[[All, 1, 1]];
	J = rules[[All, 1, 2]];
	V = rules[[All, 2]];
	m = dims[[1]]; n = dims[[2]];
	Export[filename,<|"I" -> II, "J" -> J, "V" -> V,"m" -> m, "n" -> n|>,"MAT"];
];

ImportMatrix[filename_] := Module[{m, II, J, V, mr, nc, A},
	m = Import[filename];
	II  = m["I"];
	J  = m["J"];
	V  = m["V"];
	mr = m["m"]; nc = m["n"];
	A = SparseArray[Thread[{II, J} -> V], {mr, nc}];
	A
];*)

If[numerical,
	julia = "julia";
	(*qr = home <> "qr.jl";*)
	dotqr = GetEnvironment["HOME"][[2]]<>"/projects/bps/src/dotqrC.jl";
	dotqr = StringReplace[StringReplace[dotqr,{" "->"\ "}],{"("->"\(",")"->"\)","\ "->"\\\ "}];
	(* A must be a sparse matrix *)
	RowReduceProduct[A_,B_] := Module[{ans,id,dir,dirX},
		Print["A density: ", A["Density"]];
		Print["A dimension: ", Dimensions[A]];
		Print["B density: ", B["Density"]];
		Print["B dimension: ", Dimensions[B]];
		id = ToString[RandomInteger[10^10]];
		dir = juliaDirectory<>id<>"/";
		While[FileExistsQ[dir],
			id = ToString[RandomInteger[10^10]];
			dir = juliaDirectory<>id<>"/";
		];
		Print[dir];
		dirX = StringReplace[dir,{"("->"\(",")"->"\)","\ "->"\\\ "}];
		
		(*Print["Exporting "<>dir<>"in_A.mtx"];
		Export[dir<>"in_A.mtx",A];
		Print["Exporting "<>dir<>"in_B.mtx"];
		Export[dir<>"in_B.mtx",B];
		Print["Running Julia"];
		Print["Memory Available: ",MemoryAvailable[]/2^30//N," GB"];
		Run[julia<>" "<>dotqr<>" Float64 1e-10 "<>dirX<>"in_A.mtx"<>" "<>dirX<>"in_B.mtx"<>" "<>dirX<>"out.mtx"];
		Print["Finished Julia"];*)
		
		Print["Exporting "<>dir<>"in_A.mat"];
		Export[dir<>"in_A.mat",A];
		Print["Exporting "<>dir<>"in_B.mat"];
		Export[dir<>"in_B.mat",B];
		Print["Running Julia"];
		Print["Memory Available: ",MemoryAvailable[]/2^30//N," GB"];
		Run[julia<>" "<>dotqr<>" Float64 1e-7 "<>dirX<>"in_A.mat"<>" "<>dirX<>"in_B.mat"<>" "<>dirX<>"out.mtx"];
		Print["Finished Julia"];
		
		Print["Importing "<>dir<>"out.mtx"];
		Print["Spliting mtx file"];
		Print["Memory Available: ",MemoryAvailable[]/2^30//N," GB"];
		Run["bash ~/projects/bps/src/split.sh "<>dir<>"out.mtx "<>dir<>"chunks "<>ToString[800000000]];
		Print["Reading mtx files"];
		Print["Memory Available: ",MemoryAvailable[]/2^30//N," GB"];
		Do[
			sub[f] = Import[f,"MTX"];
			,
			{f,FileNames["*",dir<>"chunks"]}
		];
		
		Print["Summing sparse matrices"];
		Print["Memory Available: ",MemoryAvailable[]/2^30//N," GB"];
		ans = Sum[sub[f],{f,FileNames["*",dir<>"chunks"]}];
		
		Do[DeleteFile[f];,{f,FileNames["*",dir<>"chunks"]}];
		DeleteFile[dir<>"in_A.mat"];
		DeleteFile[dir<>"in_B.mat"];
		DeleteFile[dir<>"out.mtx"];
		DeleteDirectory[dir<>"chunks"];
		DeleteDirectory[dir];
		
		ans
	];
];

(*If[numerical,
	julia = "julia";
	(*qr = home <> "qr.jl";*)
	qr = GetEnvironment["HOME"][[2]]<>"/projects/bps/src/qrX.jl";
	qr = StringReplace[StringReplace[qr,{" "->"\ "}],{"("->"\(",")"->"\)","\ "->"\\\ "}];
	(* A must be a sparse matrix *)
	MyRowReduce[A0_] := Module[{ans,id,dir,dirX,A,U},
		A = A0 . Transpose[A0];
		U = DiagonalMatrix[ SparseArray[ Table[ If[A[[i,i]] == 0, 1, A[[i,i]]^(-1/2)] ,{i,1,Length[A]}] ] ];
		A = U . A . U;
		(* TODO *)
		Print["density: ", A["Density"]];
		Print["dimensions: ", Dimensions[A]];
		id = ToString[RandomInteger[10^10]];
		dir = juliaDirectory<>id<>"/";
		While[FileExistsQ[dir],
			id = ToString[RandomInteger[10^10]];
			dir = juliaDirectory<>id<>"/";
		];
		Print[dir];
		dirX = StringReplace[dir,{"("->"\(",")"->"\)","\ "->"\\\ "}];
		CreateDirectory[dir];
		(*Export[dir<>"inRec.mtx",A0];*)
		Export[dir<>"in.mtx",A];
		(*Export[dir<>"in.csv",Normal[A]];*)
		Print["done exporting"];
		Run[julia<>" "<>qr<>" Float64 1e-5 "<>dirX<>"in.mtx"<>" "<>dirX<>"out.txt"<>" "<>dirX<>"R.csv"];
		ans = Import[dir<>"out.txt"]//ToExpression;
		(*DeleteFile[dir<>"in.mtx"];*)
		(*DeleteFile[dir<>"out.txt"];*)
		(*DeleteDirectory[dir];*)
		ans
	];
,
	MyRowReduce[A0_] := Module[{A,U},
		A = A0 . Transpose[A0];
		U = DiagonalMatrix[ SparseArray[ Table[ If[A[[i,i]] == 0, 1, A[[i,i]]^(-1/2)] ,{i,1,Length[A]}] ] ];
		A = U . A . U;
		MatrixRank[N[A]]
	];
];*)


(* ::Subsubsection:: *)
(*Independence*)


CollectTerms[lis_]:=DeleteCases[DeleteDuplicates[Flatten[lis/.Plus->List/.{n_ a_:>a/;NumericQ[n]}/.{-a_:>a}]],0];

Stuff[] := Module[{},
	times[n_,a__]:=n times[a]/;NumericQ[n];
	times[a_]:=a;
];
Stuff[];

T2t[traces_]:=Module[{rTraces},
	rTraces = Table[t/.Times->times/.Power->power,{t,traces}];
	rTraces
];
t2T[traces_]:=Module[{rTraces},
	rTraces = Table[t/.times->Times/.power->Power,{t,traces}];
	rTraces
];

IndependentExact[charges_,degree_,NN_] := Module[{filename,level,ind,exact,reducedExact,AllQTerms,Qmatrix,QVector,SimpQVector},
	level = charges . levelvector;
	filename = indExactDirectory<>ToString[level]<>"_"<>StringRiffle[ToString[#]&/@charges,"_"]<>"_"<>ToString[degree]<>"_"<>ToString[NN]<>"-temp.mx";
	If[!FileExistsQ[filename],
		ind = IndependentOperator[charges,degree-1,NN][[1]];
		exact = Exact[charges,degree,NN];
		reducedExact = DeleteCases[DeleteCases[exact,0],0.];
		If[reducedExact==={},
			Return[{{},{}}]
			,
			ClearAll[reducedExact];
		];
		
		Print["T2t Q stuff"];
		Print["Memory Available: ",MemoryAvailable[]/2^30//N," GB"];
		exact = T2t[exact];
		
		Print["Collecting terms"];
		Print["Memory Available: ",MemoryAvailable[]/2^30//N," GB"];
		AllQTerms = CollectTerms[DeleteDuplicates[exact]];	
		
		Print["Finding Q matrix"];
		Print["Memory Available: ",MemoryAvailable[]/2^30//N," GB"];
		Qmatrix = CoefficientArrays[exact,AllQTerms][[2]];
		
		Print["t2T all Q terms"];
		Print["Memory Available: ",MemoryAvailable[]/2^30//N," GB"];
		AllQTerms = t2T[AllQTerms];
		
		Print["Saving temporary results"];
		independentExactTemp[charges,degree,NN] = {ind, Qmatrix, AllQTerms};
		DumpSave[filename,independentExactTemp];
		ClearAll[independentExactTemp,AllQTerms,exact];
	,
		Print["Loading back ind and Qmatrix"];
		Print["Memory Available: ",MemoryAvailable[]/2^30//N," GB"];
		Get[filename];
		ind = independentExactTemp[charges,degree,NN][[1]];
		Qmatrix = independentExactTemp[charges,degree,NN][[2]];
		ClearAll[independentExactTemp];
	];
	
	Print["Computing Q vector and starting row reduce"];
	Print["Memory Available: ",MemoryAvailable[]/2^30//N," GB"];
	If[numerical,
		SimpQVector = RowReduceProduct[ind,Qmatrix];
		ClearAll[ind,Qmatrix];
	,
		QVector = SparseArray[ind . Qmatrix];
		ClearAll[ind,Qmatrix];
		SimpQVector = RowReduce[QVector];
		SimpQVector = DeleteCases[SimpQVector,Table[0,{l,1,Length[SimpQVector[[1]]]}]];
	];

(*	Print["Computing Q vector"];
	Print["Memory Available: ",MemoryAvailable[]/2^30//N," GB"];
	QVector = SparseArray[Chop[ind . Qmatrix ]];
	ClearAll[ind,Qmatrix];
	
	Print["Starting row reduce"];
	Print["Memory Available: ",MemoryAvailable[]/2^30//N," GB"];
	SimpQVector = MyRowReduce[QVector];
	SimpQVector = DeleteCases[SimpQVector,Table[0,{l,1,Length[SimpQVector[[1]]]}]];*)
	
	Print["Loading back AllQTerms"];
	Print["Memory Available: ",MemoryAvailable[]/2^30//N," GB"];
	Get[filename];
	AllQTerms = independentExactTemp[charges,degree,NN][[3]];
	
	Print["Memory Available: ",MemoryAvailable[]/2^30//N," GB"];
	{SimpQVector,AllQTerms}
];


(* ::Section:: *)
(*Execute*)


Exec[] := Module[{},
	filename = indExactDirectory<>ToString[level]<>"_"<>StringRiffle[ToString[#]&/@charges,"_"]<>"_"<>ToString[degree]<>"_"<>ToString[NN]<>".mx";
	If[!FileExistsQ[filename],
		ClearAll[independentExact];
		TimeConstrained[
			Check[
				independentExact[charges,degree,NN] = IndependentExact[charges,degree,NN];
			,
				Print["> terminated due to error"];
				ResetKernels[];
				Continue[];
			];
			DumpSave[filename,independentExact];	
			Print["Saved result"];
			tmp = independentExact[charges,degree,NN];
			ClearAll[independentExact];
			Get[filename];
			If[tmp =!= independentExact[charges,degree,NN],
				DeleteFile[filename];
				,
				If[FileExistsQ[StringReplace[filename,".mx"->"-temp.mx"]],
					DeleteFile[StringReplace[filename,".mx"->"-temp.mx"]];
				];
			];
		,
			time
		,
			Print["> overtime"];
			ResetKernels[];
		];
	];
];
