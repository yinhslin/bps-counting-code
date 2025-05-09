(* ::Package:: *)

(* ::Section:: *)
(*Multi Graviton*)


(*multiGravitonDirectory = home <> "multigravitonY/";
If[!FileExistsQ[multiGravitonDirectory],CreateDirectory[multiGravitonDirectory]];*)


(*Protect[z1,z2,th1,th2,th3,X];*)
Unprotect[X];

Stuff[] := Module[{},
	index[a1_,a2_,a3_,a4_,a5_,i_,j_]:=Mod[a3+a4+a5+1,2]*2^15+a1*2^11+a2*2^7+a3*2^6+a4*2^5+a5*2^4+(i-1)*2^2+(j-1);

	If[specialQ,
		X[a_] := -Sum[X[Quotient[a,2^4]*2^4 + 5 k],{k,0,NN-2}]/;Mod[a-(NN-1)*2^2-(NN-1),2^4]==0;
	];
	X[a_]:=0/;Quotient[a,2^5]==2^10;

	Grading[ a_Plus ] := (Grading /@ (List @@ a))[[1]];
	Grading[ a_Times ] := Mod[Plus @@ (Grading /@ (List @@ a)),2];
	Grading[ a_NonCommutativeMultiply ] := Mod[Plus @@ (Grading /@ (List @@ a)),2];
	Grading[ _ ] := 0;
	Grading[ a_X ] := Quotient[a[[1]],2^15];
	(*GetGradeds[a___] := (*GetGradeds[a] =*) Select[{a}, Grading[#] != 0 &];
	GetFermions[a___] := (*GetFermions[a] =*) Select[{a}, OddQ[Grading[#]] &];*)
	GetGradeds[a___] := (*GetGradeds[a] =*) Select[{a}, Grading[#] != 0 &];

	Unprotect[NonCommutativeMultiply];
	SetAttributes[NonCommutativeMultiply, Listable];
	ClearAttributes[NonCommutativeMultiply, Flat];
	Protect[NonCommutativeMultiply];
	NonCommutativeMultiplyRules={
		NonCommutativeMultiply[a___, b_NonCommutativeMultiply, c___] :> NonCommutativeMultiply[a, Sequence@@b, c],
		NonCommutativeMultiply[a___] /; Length[GetGradeds[a]] <= 1 :> Times[a],
		NonCommutativeMultiply[a___] /; !FreeQ[{a}, Times, 2] :> NonCommutativeMultiply @@ ReplacePart[ {a}, Sequence, Position[{a}, Times, 2] ],
		NonCommutativeMultiply[b___, a_, c___, a_, d___] /; OddQ[Grading[a]] :> 0,
		(*NonCommutativeMultiply[a___] /; (!OrderedQ[GetGradeds[a]] || Length[GetGradeds[a]] != Length[{a}] ) :>
			Signature[GetFermions[a]] * (Times @@ Select[{a}, !MemberQ[GetGradeds[a], #]&]) * NonCommutativeMultiply @@ Sort[GetGradeds[a]]*)
		NonCommutativeMultiply[a___] :> Module[{grade},grade=GetGradeds[a];
			Signature[grade] * (Times @@ Select[{a}, !MemberQ[grade, #]&]) * NonCommutativeMultiply @@ Sort[grade]
				/; (!OrderedQ[grade] || Length[grade] != Length[{a}] ) ]
	};
	GExpandRule = {x_NonCommutativeMultiply :> Distribute[x]};
];

Stuff[];

Seeds[multiGravitonCharge_,nTrace_] := Module[{pivot = Position[multiGravitonCharge,_?(#>0&)][[1,1]],range},
	Table[
		range = Range[0,100];
		If[i==pivot,
			IntegerPartitions[multiGravitonCharge[[i]],{nTrace},range]
		,
			Flatten[(Permutations[#]&/@IntegerPartitions[multiGravitonCharge[[i]],{nTrace},range]),1]
		]
	,
		{i,1,5}
	]
];

DistriCharges[tmp_] := Module[{lis = {},x},
	Do[
		x = {x1,x2,x3,x4,x5};
		If[Min[Total[x]] >= minDeg,
			AppendTo[lis,x];
		];
	,
		{x1,tmp[[1]]},{x2,tmp[[2]]},{x3,tmp[[3]]},{x4,tmp[[4]]},{x5,tmp[[5]]}
	];
	DeleteDuplicates[Sort/@Transpose/@lis]
];

(*MultiGravitonChargeList[charges_] :=Join@@Table[DistriCharges[Seeds[charges,nTrace] ],{nTrace,1,Total[charges]/minDeg}];*)
MultiGravitonChargeList[charges_] := Module[{level,filename},
	level = charges . levelvector;
	filename = multiGravitonChargeListDirectory<>ToString[level]<>"_"<>StringRiffle[ToString[#]&/@charges,"_"]<>"_"<>ToString[NN]<>".mx";
	Check[
		Get[filename];
		,
		Print[filename, " does not exist"];
		Quit[];
	];
	ans = multiGravitonChargeList[charges,NN];
	ClearAll[multiGravitonChargeList];
	ans
];

MaxDeg[charges_,N_] := Min[Plus@@charges,N];

AllDegs[charges_,N_] := (Outer@@Join[{f},Range[minDeg,#]&/@(MaxDeg[#,N]&/@charges)]//Flatten)/.f[x___]:>{x};

AllDegs[charges_,N_,degree_] := Select[AllDegs[charges,N],Total[#]==degree&];

SingleGraviton[charges_,degree_,NN_] := Module[{level,filename},
	level = charges . levelvector;
	filename = singleGravitonDirectory<>ToString[level]<>"_"<>StringRiffle[ToString[#]&/@charges,"_"]<>"_"<>ToString[degree]<>"_"<>ToString[NN]<>".mx";
	Check[
		Get[filename];
		,
		Print[filename, " does not exist"];
		Quit[];
	];
	ans = singleGraviton[charges,degree,NN];
	ClearAll[singleGraviton];
	ans
];

Distri[lis_] := Module[{tmp,ans},
	tmp = DeleteDuplicates[DeleteCases[If[Length[lis]>1,
		Outer@@Join[{NonCommutativeMultiply},lis],lis[[1]]],0]
	];
	(*Print["start parallel"];
	Print[Length[tmp]];
	Print[Timing[*)
	ans = table[
		(*Stuff[];*)
		tmp[[i]]
	,
		{i,1,Length[tmp]}
	];
	(*][[1]]];
	Print["end parallel"];*)
	ans
];

MultiGraviton[multiGravitonCharge_,degree_,NN_] := Table[Distri[
	Table[
		SingleGraviton[multiGravitonCharge[[i]],deg[[i]],NN]
	,
		{i,1,Length[multiGravitonCharge]}
	]] //.NonCommutativeMultiplyRules/.GExpandRule//.NonCommutativeMultiplyRules//Expand,{deg,AllDegs[multiGravitonCharge,NN,degree]}] // Flatten;


(* ::Section:: *)
(*Execute*)


Exec[] := Module[{},
	filename = multiGravitonDirectory<>ToString[level]<>"_"<>StringRiffle[ToString[#]&/@charges,"_"]<>"_"<>ToString[degree]<>"_"<>ToString[NN]<>".mx";
	If[!FileExistsQ[filename],
		ClearAll[multiGraviton];
		TimeConstrained[
			Check[
				multiGraviton[charges,degree,NN] = Flatten[MultiGraviton[#,degree,NN] &/@ MultiGravitonChargeList[charges]];
			,
				Print["> terminated due to error"];
				ResetKernels[];
				Continue[];
			];
			DumpSave[filename,multiGraviton];
			tmp = multiGraviton[charges,degree,NN];
			ClearAll[multiGraviton];
			Get[filename];
			If[tmp =!= multiGraviton[charges,degree,NN],
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
