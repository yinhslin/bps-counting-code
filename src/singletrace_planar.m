(* ::Package:: *)

(* ::Section:: *)
(*Single Trace*)


Protect[nzn,nzp,n\[Theta]1,n\[Theta]2,n\[Theta]3,z1,z2,th1,th2,th3];

group = CyclicGroup;

Seeds[singleTraceCharge_,degree_] := Module[{pivot = Position[singleTraceCharge,_?(#>0&)][[1,1]],range},
	Table[
		range = If[i<=2,Range[0,100],{0,1}];
		If[i==pivot,
			DeleteDuplicates[Sort[Permute[#,group[degree]]][[1]]&/@Flatten[(Permutations[#]&/@IntegerPartitions[singleTraceCharge[[i]],{degree},range]),1]]
		,
			Flatten[(Permutations[#]&/@IntegerPartitions[singleTraceCharge[[i]],{degree},range]),1]
		]
	,
		{i,1,5}
	]
];

Distri[tmp_] := Module[{inds,lis,x},
	inds = #[[2]] &/@ Sort[{-Length[tmp[[#]]],#} &/@ Range[5]];
	(*inds = Range[5];*)
	lis = Flatten[
			table[
				If[Min[Total[{x1,x2,x3,x4,x5}]]>0,
					Permute[{x1,x2,x3,x4,x5},InversePermutation[inds]]
					(*{x1,x2,x3,x4,x5}*)
				,
					0
				]
			,
				{x1,tmp[[inds[[1]]]]},{x2,tmp[[inds[[2]]]]},{x3,tmp[[inds[[3]]]]},{x4,tmp[[inds[[4]]]]},{x5,tmp[[inds[[5]]]]}
			]
		,
			4
		];
	lis = DeleteCases[lis,0];
	Transpose[#]&/@lis
];

ComputeSingleNecklaces[singleTraceCharge_,degree_] := Module[{seeds,distri,res},
	seeds = Seeds[singleTraceCharge,degree];
	distri = Distri[seeds];
	Print["Distri length: ",Length[distri]];
	Check[
		res = table[
			Sort[Permute[distri[[i]],group[Length[distri[[i]]]]]][[1]] , {i,1,Length[distri]}
		];
	,
		Quit[];
	];
	DeleteDuplicates[ 
		res
	]
];

SingleNecklaces[singleTraceCharge_,degree_] := Module[{level,filename,ans},
	level = singleTraceCharge . levelvector;
	filename = necklaceDirectory<>ToString[level]<>"_"<>StringRiffle[ToString[#]&/@singleTraceCharge,"_"]<>"_"<>ToString[degree]<>".mx";
	If[FileExistsQ[filename],
	Check[
		Get[filename];
		Assert[ListQ[necklace[singleTraceCharge,degree]]];
		,
		Check[
			necklace[singleTraceCharge,degree] = ComputeSingleNecklaces[singleTraceCharge,degree];
			,
			Print["necklace error"];
			Quit[];
		];
		DumpSave[filename,necklace];
	];
	,
		Check[
			necklace[singleTraceCharge,degree] = ComputeSingleNecklaces[singleTraceCharge,degree];
			,
			Print["necklace error"];
			Quit[];
		];
		DumpSave[filename,necklace];
	];
	ans = necklace[singleTraceCharge,degree];
	ClearAll[necklace];
	ans
];

(* TODO *)

Stuff[] := Module[{},
	index[a1_,a2_,a3_,a4_,a5_]:=Mod[a3+a4+a5+1,2]*2^15+a1*2^11+a2*2^7+a3*2^6+a4*2^5+a5*2^4;
	fp[a_]:=Quotient[a,2^15];
	X[a_]:=0/;Quotient[a,2^5]==2^10;
	
	Grading[ a_Plus ] := Max @@ (Grading /@ (List @@ a));
	Grading[ a_List ] := Plus @@ (Grading /@ (List @@ a));
	(*Grading[ a_Times ] := Plus @@ (Grading /@ (List @@ a));*)
	Grading[ n_ a_ ]:= Grading[ a ]/;NumericQ[n];
	Grading[ a_NonCommutativeMultiply ] := Plus @@ (Grading /@ (List @@ a));
	Grading[ _ ] := 0;
	Grading[ a_X ] := fp[a[[1]]];
	
	CyclicOrdering[ a_NonCommutativeMultiply ]:=Module[{aList,cyclicList},
		aList = List@@a;
		cyclicList = Table[(-1)^( Grading[aList[[1;;i]]]*Grading[aList[[(i+1);;]]] ) NonCommutativeMultiply@@RotateLeft[aList,i]
			,{i,1,Length[aList]}];
		If[MemberQ[cyclicList,x_/;MemberQ[cyclicList,-x]],
			0
			,
			Last[Sort[cyclicList]]
		]
	];
	CyclicOrdering[ a_Plus ]:= Plus @@ (CyclicOrdering /@ (List @@ a));
	CyclicOrdering[ n_ a_ ]:= n CyclicOrdering[ a ]/;NumericQ[n];
	CyclicOrdering[ n_ ]:= n/;NumericQ[n];	
	
	MonoCharge[singleTrace_] := NonCommutativeMultiply@@( X[index[#[[1]],#[[2]],#[[3]],#[[4]],#[[5]]]] &/@ singleTrace)//CyclicOrdering;
];

Stuff[];

SingleTrace[singleTraceCharge_,degree_,filename_] := Module[{sn,ans,cnt,tmp,tot,subfilename,healthy},
	sn = SingleNecklaces[singleTraceCharge,degree];
	Print["length: ", Length[sn]];
	If[Length[sn]>0,
		cnt = 0;
		While[chunk*cnt<Length[sn],
			subfilename = filename<>"-"<>ToString[cnt]<>".mx";
			healthy = True;
			If[FileExistsQ[subfilename],
				Check[
					Get[subfilename];
					If[!ListQ[singleTrace[singleTraceCharge,degree]], healthy = False];
				,
					healthy = False;
				];
			,
				healthy = False
			];
			If[!healthy,
				tmp = sn[[chunk*cnt+1;;Min[chunk*(cnt+1),Length[sn]]]];
				ans = table[
					MonoCharge[tmp[[i]]]
				,
					{i,1,Length[tmp]}
				];
				singleTrace[singleTraceCharge,degree] = ans;
				DumpSave[subfilename,singleTrace];
			];
			ClearAll[singleTrace,ans,tmp];
			cnt+=1;
		];
		tot = cnt-1;
		ans = {};
		Do[
			Get[filename<>"-"<>ToString[cnt]<>".mx"];
			ans = Join[ans,singleTrace[singleTraceCharge,degree]];
			ClearAll[singleTrace];
		,
			{cnt,0,tot}
		];
		Assert[Length[ans]==Length[sn]];
		(*If[Length[ans]=!=Length[sn],
			Print[ans];
			Print[Length[ans]];
		];*)
		DeleteFile[#] &/@ FileNames[filename<>"-*"];
	,
		ans = {};
	];
	DeleteCases[ans,0]
];


(* ::Section:: *)
(*Execute*)


Exec[] := Module[{},
	fn = singleDirectory<>ToString[level]<>"_"<>StringRiffle[ToString[#]&/@charges,"_"]<>"_"<>ToString[degree]<>"_P";
	filename = fn <> ".mx";
	If[!FileExistsQ[filename],
		ClearAll[singleTrace];
		(* time constrain *)
		TimeConstrained[
			Check[
				singleTrace[charges,degree]=SingleTrace[charges,degree,fn];
			,
				Print["> terminated due to error"];
				ResetKernels[];
				Continue[];
			];
			DumpSave[filename,singleTrace];
			tmp = singleTrace[charges,degree];
			ClearAll[singleTrace];
			Get[filename];
			If[tmp =!= singleTrace[charges,degree],
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
