(* ::Package:: *)

(* ::Section:: *)
(*Independent Graviton*)


(* ::Subsubsection:: *)
(*Independent exact and Multi-graviton*)


IndependentExact[charges_,degree_,NN_] := Module[{level,filename,ans},
	level = charges . levelvector;
	filename = indExactDirectory<>ToString[level]<>"_"<>StringRiffle[ToString[#]&/@charges,"_"]<>"_"<>ToString[degree]<>"_"<>ToString[NN]<>".mx";
	If[FileExistsQ[filename],
		Get[filename];
	,
		Return[{{},{}}];
	];
	ans = independentExact[charges,degree,NN];
	Clear[independentExact];
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
(*Numerical*)


(* ::Text:: *)
(*Install Julia from https://julialang.org/*)
(*Install necessary packages by running the following commands within Julia:*)
(*import(Pkg);*)
(*Pkg.add(["LinearAlgebra", "SparseArrays", "SuiteSparse", "DelimitedFiles", "DoubleFloats", "MultiFloats", "MatrixMarket", "RowEchelon", "ZChop", "JLD2"]);*)


(*ExportMatrix[filename_, A_] := Module[{dims, rules, II, J, V, m, n},
	dims = Dimensions[A];
	rules = Most @ ArrayRules[A];
	II = rules[[All, 1, 1]];
	J = rules[[All, 1, 2]];
	V = rules[[All, 2]];
	m = dims[[1]]; n = dims[[2]];
	Export[filename,<|"I" -> II, "J" -> J, "V" -> V,"m" -> m, "n" -> n|>,"MAT"];
];*)

If[numerical,
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
		
		(*Print["Exporting "<>dir<>"in.mtx"];
		Export[dir<>"in.mtx",A];
		Print["Running Julia"];
		Run[julia<>" "<>qr<>" Float64 1e-10 "<>dirX<>"in.mtx"<>" "<>dirX<>"out.txt"];
		Print["Finished Julia"];*)
		
		Print["Exporting "<>dir<>"in.mat"];
		Export[dir<>"in.mat",A];
		Run[julia<>" "<>qr<>" Float64 1e-7 "<>dirX<>"in.mat"<>" "<>dirX<>"out.txt"];
		Print["Finished Julia"];
		
		Print["Exported to "<>dir<>"out.txt"];
		ans = A[[ Sort[ Transpose[ Import[dir<>"out.txt","Table"] ][[1]] ] ]];
		
		DeleteFile[dir<>"in.mat"];
		DeleteFile[dir<>"out.txt"];
		
		ans
	];
,
	MyRowReduce := RowReduce;
];

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
];*)

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

(*IndGrav[grav_,Qind_] := Module[{rGrav,Allterms,SimpQVector,gravCoVector,SimpVector},
	Print["T2t grav"];
	rGrav = T2t[grav];
	Print["Collecting terms"];
	Allterms = DeleteDuplicates[Join[T2t[Qind[[2]]],CollectTerms[rGrav]]];
	Print["Finding grav covector"];
	gravCoVector = CoefficientArrays[rGrav,Allterms][[2]];
	Print["t2T all terms"];
	Allterms = t2T[Allterms];
	Print["Starting row reduce"];
	SimpQVector = SparseArray[Qind[[1]],{Length[Qind[[1]]],Length[Allterms]}];
	SimpVector = Join[SimpQVector,gravCoVector]//MyRowReduce;
	SimpVector = DeleteCases[SimpVector,Table[0,Length[gravCoVector[[1]]]]];
	{SimpVector, Allterms}
];*)

IndependentGraviton[charges_,degree_,NN_]:=Module[{filename,grav,reducedgrav,indExact,AllExactTerms,AllGravTerms,Allterms,gravCoVector,SimpQVector,SimpVector,indGrav},
	level = charges . levelvector;
	filename = indGravitonDirectory<>ToString[level]<>"_"<>StringRiffle[ToString[#]&/@charges,"_"]<>"_"<>ToString[degree]<>"_"<>ToString[NN]<>"-temp.mx";
	If[!FileExistsQ[filename],	
		grav = DeleteCases[DeleteCases[MultiGraviton[charges,degree,NN],0],0.];
		indExact = IndependentExact[charges,degree,NN];
		reducedgrav = DeleteCases[DeleteCases[grav,0],0.];
		If[reducedgrav=={},
			Return[indExact]
			,
			ClearAll[reducedgrav];
		];
		Print["T2t grav"];
		Print["Memory Available: ",MemoryAvailable[]/2^30//N," GB"];
		grav = T2t[grav];
		AllExactTerms = T2t[indExact[[2]]];
		
		Print["Collecting terms"];
		Print["Memory Available: ",MemoryAvailable[]/2^30//N," GB"];
		AllGravTerms = CollectTerms[grav];
		Allterms = DeleteDuplicates[Join[AllExactTerms,AllGravTerms]];
		ClearAll[AllGravTerms,AllExactTerms];
		
		Print["Finding grav covector"];
		Print["Memory Available: ",MemoryAvailable[]/2^30//N," GB"];
		gravCoVector = CoefficientArrays[grav,Allterms][[2]];
		SimpQVector = SparseArray[indExact[[1]],{Length[indExact[[1]]],Length[Allterms]}];
		gravCoVector = Join[SimpQVector,gravCoVector];
		ClearAll[grav, SimpQVector];
	
		Print["t2T all terms"];
		Print["Memory Available: ",MemoryAvailable[]/2^30//N," GB"];
		Allterms = t2T[Allterms];
		
		Print["Saving temporary results"];
		independentGravitonTemp[charges,degree,NN] = {gravCoVector, Allterms};
		DumpSave[filename,independentGravitonTemp];
		ClearAll[independentGravitonTemp,Allterms];
	,
		Print["Loading back gravCoVector"];
		Print["Memory Available: ",MemoryAvailable[]/2^30//N," GB"];
		Get[filename];
		gravCoVector = independentGravitonTemp[charges,degree,NN][[1]];
		ClearAll[independentGravitonTemp];
	];
			
	Print["Starting row reduce"];
	Print["Memory Available: ",MemoryAvailable[]/2^30//N," GB"];
	SimpVector = MyRowReduce[gravCoVector];
	SimpVector = DeleteCases[SimpVector,Table[0,Length[SimpVector[[1]]]]];
	
	Print["Loading back AllTerms"];
	Print["Memory Available: ",MemoryAvailable[]/2^30//N," GB"];
	Get[filename];
	Allterms = independentGravitonTemp[charges,degree,NN][[2]];

	{SimpVector,Allterms}
];


(* ::Section:: *)
(*Execute*)


Exec[] := Module[{},
	filename = indGravitonDirectory<>ToString[level]<>"_"<>StringRiffle[ToString[#]&/@charges,"_"]<>"_"<>ToString[degree]<>"_"<>ToString[NN]<>".mx";
	If[!FileExistsQ[filename],
		ClearAll[exact];
		TimeConstrained[
			Check[
				independentGraviton[charges,degree,NN] = IndependentGraviton[charges,degree,NN];
			,
				Print["> terminated due to error"];
				ResetKernels[];
				Continue[];
			];
			DumpSave[filename,independentGraviton];
			Print["Saved result"];
			tmp = independentGraviton[charges,degree,NN];
			ClearAll[independentGraviton];
			Get[filename];
			If[tmp =!= independentGraviton[charges,degree,NN],
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
