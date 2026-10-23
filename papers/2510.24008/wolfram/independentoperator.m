(* Computational core from the author source. See docs/PROVENANCE.md. *)
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

IndependentOperator[charges_,degree_,NN_] := Module[{level,filename,traces,rTraces,Allterms,CoVector,SimpVector},
	level = charges . levelvector;
	filename = operatorDirectory<>ToString[level]<>"_"<>StringRiffle[ToString[#]&/@charges,"_"]<>"_"<>ToString[degree]<>"_"<>ToString[NN]<>"-temp.mx";
	If[!FileExistsQ[filename],
		traces = DeleteCases[DeleteCases[MultiTrace[charges,degree,NN],0],0.];
		If[traces==={},
			Return[{{},{}}]
		];
		
		Print["T2t traces"];
		Print["Memory Available: ",MemoryAvailable[]/2^30//N," GB"];
		rTraces = T2t[traces];
		
		Print["Collecting terms"];
		Print["Memory Available: ",MemoryAvailable[]/2^30//N," GB"];
		Allterms = CollectTerms[rTraces];
		
		Print["Finding covector"];
		Print["Memory Available: ",MemoryAvailable[]/2^30//N," GB"];
		CoVector = CoefficientArrays[rTraces,Allterms][[2]];
		
		Print["t2T all terms"];
		Print["Memory Available: ",MemoryAvailable[]/2^30//N," GB"];
		Allterms = t2T[Allterms];
		independentOperatorTemp[charges,degree,NN] = {CoVector, Allterms};
		DumpSave[filename,independentOperatorTemp];
		ClearAll[independentOperatorTemp,Allterms,rTraces,traces];	
	,
		Print["Loading back CoVector"];
		Print["Memory Available: ",MemoryAvailable[]/2^30//N," GB"];
		Get[filename];
		CoVector = independentOperatorTemp[charges,degree,NN][[1]];
		ClearAll[independentOperatorTemp];
	];
	
	Print["Starting row reduce"];
	Print["Memory Available: ",MemoryAvailable[]/2^30//N," GB"];
	SimpVector = CoVector//MyRowReduce;
	If[Length[SimpVector]>0,SimpVector = DeleteCases[SimpVector,Table[0,{l,1,Length[SimpVector[[1]]]}]]];
	
	Print["Loading back Allterms"];
	Print["Memory Available: ",MemoryAvailable[]/2^30//N," GB"];
	Get[filename];
	Allterms = independentOperatorTemp[charges,degree,NN][[2]];
	
	{SimpVector,Allterms}
];

Exec[] := Module[{},
	filename = operatorDirectory<>ToString[level]<>"_"<>StringRiffle[ToString[#]&/@charges,"_"]<>"_"<>ToString[degree]<>"_"<>ToString[NN]<>".mx";
	If[!FileExistsQ[filename],
		ClearAll[independentOperator];
		TimeConstrained[
			Check[
				independentOperator[charges,degree,NN] = IndependentOperator[charges,degree,NN];
			,
				Print["> terminated due to error"];
				ResetKernels[];
				Abort[];
			];
			DumpSave[filename,independentOperator];	
			Print["Saved result"];
			tmp = independentOperator[charges,degree,NN];
			ClearAll[independentOperator];
			Get[filename];
			If[tmp =!= independentOperator[charges,degree,NN],
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
