(* ::Package:: *)

(* ::Section:: *)
(*Cohomology*)


CountQ[charges_,degree_,NN_] := Module[{level,filename},
	level = charges . levelvector;
	filename = countDirectory<>ToString[level]<>"_"<>StringRiffle[ToString[#]&/@charges,"_"]<>"_"<>ToString[degree]<>"_"<>ToString[NN]<>".csv";
	If[FileExistsQ[filename],
		Import[filename][[1]]
		,
		(*{0,0,0}*)
		Null
	]
];
Cohomology[charges_,degree_,NN_] := {charges . levelvector,charges,degree,NN,CountQ[charges,degree,NN][[1]]-CountQ[charges,degree-1,NN][[2]],CountQ[charges,degree-1,NN][[3]]}//Flatten;
Cohomology[charges_,degree_,NN_] := Module[{count1 = CountQ[charges,degree,NN], count2 = CountQ[charges,degree-1,NN]},
	If[count1 =!= Null && count2 =!= Null,
		{charges . levelvector,charges,degree,NN,count1[[1]]-count2[[2]]}//Flatten
	,
		Null
	]
];

(*CountQ[charges_,degree_,NN_] := Module[{level,filename},
	level = charges . levelvector;
	filename = countDirectory<>ToString[level]<>"_"<>StringRiffle[ToString[#]&/@charges,"_"]<>"_"<>ToString[degree]<>"_"<>ToString[NN]<>".csv";
	If[FileExistsQ[filename],
		Import[filename][[1]]
		,
		{0,0}
	]
];
Cohomology[charges_,degree_,NN_] := {charges . levelvector,charges,degree,NN,CountQ[charges,degree,NN][[1]]-CountQ[charges,degree-1,NN][[2]]}//Flatten;*)


(* ::Section:: *)
(*Execute*)


Exec[] := Module[{},
	filename = cohomologyDirectory<>ToString[level]<>"_"<>StringRiffle[ToString[#]&/@charges,"_"]<>"_"<>ToString[degree]<>"_"<>ToString[NN]<>".csv";
	If[!FileExistsQ[filename],
		ClearAll[countQ];
		cohomology[charges,degree,NN] = Cohomology[charges,degree,NN];
		If[cohomology[charges,degree,NN] =!= Null,
			Export[filename,{cohomology[charges,degree,NN]}];
			tmp = Import[filename,"CSV"];
			If[tmp[[1]] =!= cohomology[charges,degree,NN],
				DeleteFile[filename];
			];
		];
	];
];
