(* ::Package:: *)

(* ::Section:: *)
(*Multi Trace*)


(*Protect[z1,z2,th1,th2,th3,X];*)
Unprotect[X];

Stuff[] := Module[{},
	index[a1_,a2_,a3_,a4_,a5_,i_,j_]:=Mod[a3+a4+a5+1,2]*2^15+a1*2^11+a2*2^7+a3*2^6+a4*2^5+a5*2^4+(i-1)*2^2+(j-1);

	If[specialQ,
		X[a_] := -Sum[X[Quotient[a,2^4]*2^4 + 5 k],{k,0,NN-2}]/;Mod[a-(NN-1)*2^2-(NN-1),2^4]==0;
	];
	X[a_]:=0/;Quotient[a,2^5]==2^10;

	Grading[ a_Plus ] := Max @@ (Grading /@ (List @@ a));
	Grading[ a_Times ] := Plus @@ (Grading /@ (List @@ a));
	Grading[ a_NonCommutativeMultiply ] := Plus @@ (Grading /@ (List @@ a));
	Grading[ _ ] := 0;
	Grading[ a_X ] := Quotient[a[[1]],2^15];
	GetGradeds[a___] := (*GetGradeds[a] =*) Select[{a}, Grading[#] != 0 &];
	GetFermions[a___] := (*GetFermions[a] =*) Select[{a}, OddQ[Grading[#]] &];

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
			Signature[GetFermions[a]] * (Times @@ Select[{a}, !MemberQ[grade, #]&]) * NonCommutativeMultiply @@ Sort[grade]
				/; (!OrderedQ[grade] || Length[grade] != Length[{a}] ) ]
	};
	GExpandRule = {x_NonCommutativeMultiply :> Distribute[x]};
];

Stuff[];

Seeds[multiTraceCharge_,nTrace_] := Module[{pivot = Position[multiTraceCharge,_?(#>0&)][[1,1]],range},
	Table[
		range = Range[0,100];
		If[i==pivot,
			IntegerPartitions[multiTraceCharge[[i]],{nTrace},range]
		,
			Flatten[(Permutations[#]&/@IntegerPartitions[multiTraceCharge[[i]],{nTrace},range]),1]
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

(*MultiTraceChargeList[charges_] :=Join@@Table[DistriCharges[Seeds[charges,nTrace] ],{nTrace,1,Total[charges]/minDeg}];*)
MultiTraceChargeList[charges_] := Module[{level,filename},
	level = charges . levelvector;
	filename = multiTraceChargeListDirectory<>ToString[level]<>"_"<>StringRiffle[ToString[#]&/@charges,"_"]<>".mx";
	Check[
		Get[filename];
		,
		Print[filename, " does not exist"];
		Quit[];
	];
	ans = multiTraceChargeList[charges];
	ClearAll[multiTraceChargeList];
	ans
];

MaxDeg[charges_] := Plus@@charges;

Which[
	su122Q || su121Q, AllDegs[charges_] := (Outer@@Join[{f},
		If[minDeg <= #[[5]] <= MaxDeg[#],
			{#[[5]]}
		,
			{}
		]
	&/@charges]//Flatten)/.f[x___]:>{x};,
	True, AllDegs[charges_] := (Outer@@Join[{f},Range[minDeg,#]&/@(MaxDeg[#]&/@charges)]//Flatten)/.f[x___]:>{x};
];

(*
AllDegs[charges_] := (Outer@@Join[{f},Range[minDeg,#]&/@(MaxDeg[#]&/@charges)]//Flatten)/.f[x___]:>{x};
*)

AllDegs[charges_,degree_] := Select[AllDegs[charges],Total[#]==degree&];

SingleTrace[charges_,degree_,NN_] := Module[{level,filename},
	level = charges . levelvector;
	filename = singleDirectory<>ToString[level]<>"_"<>StringRiffle[ToString[#]&/@charges,"_"]<>"_"<>ToString[degree]<>"_"<>ToString[NN]<>".mx";
	Check[
		Get[filename];
		,
		Print[filename, " does not exist"];
		Quit[];
	];
	ans = singleTrace[charges,degree,NN];
	ClearAll[singleTrace];
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

MultiTrace[multiTraceCharge_,degree_,NN_] := Table[Distri[
	Table[
		SingleTrace[multiTraceCharge[[i]],deg[[i]],NN]
	,
		{i,1,Length[multiTraceCharge]}
	]] //.GExpandRule//.NonCommutativeMultiplyRules//Expand,{deg,AllDegs[multiTraceCharge,degree]}] // Flatten;
	
(*MultiTrace[multiTraceCharge_,degree_,NN_] := Distri[
	Table[
		If[minDeg <= multiTraceCharge[[i,5]] <= MaxDeg[multiTraceCharge[[i]]],
			SingleTrace[multiTraceCharge[[i]],multiTraceCharge[[i,5]],NN]
		,
			{}
		]
	,
		{i,1,Length[multiTraceCharge]}
	]] //.GExpandRule//.NonCommutativeMultiplyRules//Expand;*)


(* ::Section:: *)
(*Execute*)


Exec[] := Module[{},
	filename = multiDirectory<>ToString[level]<>"_"<>StringRiffle[ToString[#]&/@charges,"_"]<>"_"<>ToString[degree]<>"_"<>ToString[NN]<>".mx";
	If[!FileExistsQ[filename],
		ClearAll[multiTrace];
		TimeConstrained[
			Check[
				multiTrace[charges,degree,NN] = Flatten[MultiTrace[#,degree,NN] &/@ MultiTraceChargeList[charges]];
			,
				Print["> terminated due to error"];
				ResetKernels[];
				Continue[];
			];
			DumpSave[filename,multiTrace];
			tmp = multiTrace[charges,degree,NN];
			ClearAll[multiTrace];
			Get[filename];
			If[tmp =!= multiTrace[charges,degree,NN],
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
