(* Computational core from the author source. See docs/PROVENANCE.md. *)
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

Get[FileNameJoin[{sourceDirectory, "numerics.wl"}]];

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

	Print["Loading back AllQTerms"];
	Print["Memory Available: ",MemoryAvailable[]/2^30//N," GB"];
	Get[filename];
	AllQTerms = independentExactTemp[charges,degree,NN][[3]];
	
	Print["Memory Available: ",MemoryAvailable[]/2^30//N," GB"];
	{SimpQVector,AllQTerms}
];

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
				Abort[];
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
