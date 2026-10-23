(* Computational core from the author source. See docs/PROVENANCE.md. *)
IndependentOperator[charges_,degree_,NN_] := Module[{level,filename,ans},
	level = charges . levelvector;
	filename = operatorDirectory<>ToString[level]<>"_"<>StringRiffle[ToString[#]&/@charges,"_"]<>"_"<>ToString[degree]<>"_"<>ToString[NN]<>".mx";
	If[FileExistsQ[filename],
		Get[filename];
	,
		Return[{}];
	];
	ans = independentOperator[charges,degree,NN];
	Clear[independentOperator];
	ans
];

IndependentExact[charges_,degree_,NN_] := Module[{level,filename,ans},
	level = charges . levelvector;
	filename = indExactDirectory<>ToString[level]<>"_"<>StringRiffle[ToString[#]&/@charges,"_"]<>"_"<>ToString[degree]<>"_"<>ToString[NN]<>".mx";
	If[FileExistsQ[filename],
		Get[filename];
	,
		Return[{}];
	];
	ans = independentExact[charges,degree,NN];
	Clear[independentExact];
	ans
];

IndependentGraviton[charges_,degree_,NN_] := Module[{level,filename,ans},
	level = charges . levelvector;
	filename = indGravitonDirectory<>ToString[level]<>"_"<>StringRiffle[ToString[#]&/@charges,"_"]<>"_"<>ToString[degree]<>"_"<>ToString[NN]<>".mx";
	If[FileExistsQ[filename],
		Get[filename];
	,
		Return[{}];
	];
	ans = independentGraviton[charges,degree,NN];
	Clear[independentGraviton];
	ans
];

CountQ[charges_,degree_,NN_] := Module[{ind,indExact,indGrav},
	ind = IndependentOperator[charges,degree,NN];
	indExact = IndependentExact[charges,degree+1,NN];
	indGrav = IndependentGraviton[charges,degree+1,NN];
	Flatten[ {Length[ind[[1]]]-Length[indExact[[1]]], Length[indExact[[1]]], Length[indGrav[[1]]]-Length[indExact[[1]]]} ]
];

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
				Abort[];
			];
			Export[filename,{countQ[charges,degree,NN]}];
			tmp = Import[filename,"CSV"];

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
