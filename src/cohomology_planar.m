(* ::Package:: *)

(* ::Section:: *)
(*Cohomology*)


CountQ[charges_,degree_] := Module[{level,filename},
	level = charges . {3,3,2,2,2};
	filename = countDirectory<>ToString[level]<>"_"<>StringRiffle[ToString[#]&/@charges,"_"]<>"_"<>ToString[degree]<>"_P"<>".csv";
	If[FileExistsQ[filename],
		Import[filename][[1]]
		,
		(*{0,0,0}*)
		Null
	]
];
Cohomology[charges_,degree_] := {charges . {3,3,2,2,2},charges,degree,CountQ[charges,degree][[1]]-CountQ[charges,degree-1][[2]]}//Flatten;
Cohomology[charges_,degree_] := Module[{count1 = CountQ[charges,degree], count2 = CountQ[charges,degree-1]},
	If[count1 =!= Null && count2 =!= Null,
		{charges . {3,3,2,2,2},charges,degree,count1[[1]]-count2[[2]]}//Flatten
	,
		Null
	]
];

(*CountQ[charges_,degree_,NN_] := Module[{level,filename},
	level = charges . {3,3,2,2,2};
	filename = countDirectory<>ToString[level]<>"_"<>StringRiffle[ToString[#]&/@charges,"_"]<>"_"<>ToString[degree]<>"_"<>ToString[NN]<>".csv";
	If[FileExistsQ[filename],
		Import[filename][[1]]
		,
		{0,0}
	]
];
Cohomology[charges_,degree_,NN_] := {charges . {3,3,2,2,2},charges,degree,NN,CountQ[charges,degree,NN][[1]]-CountQ[charges,degree-1,NN][[2]]}//Flatten;*)


(* ::Section:: *)
(*Execute*)


Exec[] := Module[{},
	filename = cohomologyDirectory<>ToString[level]<>"_"<>StringRiffle[ToString[#]&/@charges,"_"]<>"_"<>ToString[degree]<>"_P"<>".csv";
	If[!FileExistsQ[filename],
		ClearAll[countQ];
		cohomology[charges,degree] = Cohomology[charges,degree];
		If[cohomology[charges,degree] =!= Null,
			Export[filename,{cohomology[charges,degree]}];
			tmp = Import[filename,"CSV"];
			If[tmp[[1]] =!= cohomology[charges,degree],
				DeleteFile[filename];
			];
		];
	];
];
