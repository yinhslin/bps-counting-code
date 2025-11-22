(* ::Package:: *)

(* ::Section:: *)
(*Cohomology*)


(* ::Subsubsection:: *)
(*Independent Operator,  Independent Exact, and Independent Graviton*)


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

IndependentGraviton[charges_,degree_,NN_] := Module[{level,filename,ans},
	level = charges . levelvector;
	filename = indGravitonDirectory<>ToString[level]<>"_"<>StringRiffle[ToString[#]&/@charges,"_"]<>"_"<>ToString[degree]<>"_"<>ToString[NN]<>".mx";
	If[FileExistsQ[filename],
		Get[filename];
	,
		Return[{{},{}}];
	];
	ans = independentGraviton[charges,degree,NN];
	Clear[independentGraviton];
	ans
];


(* ::Subsubsection:: *)
(*Cohomology*)


Cohomology[charges_,degree_,NN_] := Module[{all,exact,nonclosed,grav},
	all = IndependentOperator[charges,degree,NN][[1]];
	exact = IndependentExact[charges,degree,NN][[1]];
	nonclosed = IndependentExact[charges,degree+1,NN][[1]];
	grav = IndependentGraviton[charges,degree,NN][[1]];
	Print["all: ",Length[all]];
	Print["exact: ",Length[exact]];
	Print["nonclosed: ",Length[nonclosed]];
	Print["grav: ",Length[grav]];
	Print["cohomology: ",Length[all]-Length[exact]-Length[nonclosed]];
	Print["graviton cohomology: ",Length[grav]-Length[exact]];
	{charges . levelvector,charges,degree,NN,Length[all]-Length[exact]-Length[nonclosed],Length[grav]-Length[exact]}//Flatten
];


(* ::Section:: *)
(*Execute*)


Exec[] := Module[{},
	filename = cohomologyDirectory<>ToString[level]<>"_"<>StringRiffle[ToString[#]&/@charges,"_"]<>"_"<>ToString[degree]<>"_"<>ToString[NN]<>".csv";
	If[!FileExistsQ[filename],
		ClearAll[cohomology];
		TimeConstrained[
			Check[
				cohomology[charges,degree,NN] = Cohomology[charges,degree,NN];
			,
				Print["> terminated due to error"];
				ResetKernels[];
				Continue[];
			];
			Export[filename,{cohomology[charges,degree,NN]}];
			tmp = Import[filename,"CSV"];
			(*Print[countQ[charges,degree,NN], " ", tmp[[1]]];*)
			(*Print["> ", tmp[[1]] === countQ[charges,degree,NN]];*)
			(*If[
				tmp[[1]] =!= countQ[charges,degree,NN]
				,
				Print["PROBLEM!"];
				Quit[];
			];*)
			If[tmp[[1]] =!= cohomology[charges,degree,NN],
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
