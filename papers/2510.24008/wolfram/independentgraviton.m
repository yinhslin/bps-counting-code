(* Computational core from the author source. See docs/PROVENANCE.md. *)
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
	If[Length[SimpVector]>0,SimpVector = DeleteCases[SimpVector,Table[0,Length[SimpVector[[1]]]]]];
	
	Print["Loading back AllTerms"];
	Print["Memory Available: ",MemoryAvailable[]/2^30//N," GB"];
	Get[filename];
	Allterms = independentGravitonTemp[charges,degree,NN][[2]];

	{SimpVector,Allterms}
];

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
				Abort[];
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
