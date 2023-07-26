(* ::Package:: *)

(* ::Section:: *)
(*Cohomology*)


CountGrav[charges_,degree_,NN_] := Module[{level,filename},
	level = charges . {3,3,2,2,2};
	filename = countDirectory<>ToString[level]<>"_"<>StringRiffle[ToString[#]&/@charges,"_"]<>"_"<>ToString[degree]<>"_"<>ToString[NN]<>".csv";
	If[FileExistsQ[filename],
		Import[filename][[1]]
		,
		(*{0,0,0}*)
		Null
	]
];
Cohomology[charges_,degree_,NN_] := Module[{count = CountGrav[charges,degree,NN]},
	If[count =!= Null ,
		{charges . {3,3,2,2,2},charges,degree,NN,count[[1]]}//Flatten
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
	filename = cohomologyDirectory<>ToString[level]<>"_"<>StringRiffle[ToString[#]&/@charges,"_"]<>"_"<>ToString[degree]<>"_"<>ToString[NN]<>".csv";
	If[!FileExistsQ[filename],
		cohomology[charges,degree,NN] = Cohomology[charges,degree,NN];
		If[graviton[charges,degree,NN] =!= Null,
			Export[filename,{cohomology[charges,degree,NN]}];
			tmp = Import[filename,"CSV"];
			If[tmp[[1]] =!= cohomology[charges,degree,NN],
				DeleteFile[filename];
			];
		];
	];
];
