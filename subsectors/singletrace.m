(* ::Package:: *)

(* ::Section:: *)
(*Single Trace*)


Protect[nzn,nzp,n\[Theta]1,n\[Theta]2,n\[Theta]3,z1,z2,th1,th2,th3];

group = If[specialQ && NN==2,
	DihedralGroup,
	CyclicGroup
];

Seeds[singleTraceCharge_,degree_] := Module[{pivot = Position[singleTraceCharge,_?(#>0&)][[1,1]],range},
	Table[
		(*range = If[i<=2,Range[0,100],{0,1}];*)
		range = Which[i<=2,Range[0,100],i==3||i==4,{0,1},i==5,{1}];
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
	filename = necklaceDirectory<>ToString[level]<>"_"<>StringRiffle[ToString[#]&/@singleTraceCharge,"_"]<>"_"<>ToString[degree]<>"_"<>ToString[NN]<>".mx";
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
	
	S[A_,B_] := Inner[NonCommutativeMultiply,A,B,Plus];

	TraceP[Xlist_] := Module[{prod,LL},
		LL=Length[Xlist];
		If[LL>=2,
			prod=S[Xlist[[1]],Xlist[[2]]];
			Do[prod=S[prod,Xlist[[m]]],{m,3,LL}];
		,
			prod=Xlist[[1]]
		];
		Tr[prod]
	];

	CreateWord[singleTrace_,NN_] := (Table[ X[index[#[[1]],#[[2]],#[[3]],#[[4]],#[[5]],i,j]] ,{i,1,NN},{j,1,NN}]) &/@ singleTrace;
(*	CreateWord[singleTrace_] := (X@@#) &/@ singleTrace;
	LoadMatrix[NN_] := X[a__]:>Table[XX[EvenQ[{a}[[3]]+{a}[[4]]+{a}[[5]]],a,i,j],{i,1,NN},{j,1,NN}];*)
	MonoCharge[singleTrace_,NN_] := (TraceP[CreateWord[singleTrace,NN]]//.Join[NonCommutativeMultiplyRules,GExpandRule]//Expand);

];

Stuff[];

SingleTrace[singleTraceCharge_,degree_,NN_,filename_] := Module[{sn,ans,cnt,tmp,tot,subfilename,healthy},
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
					If[!ListQ[singleTrace[singleTraceCharge,degree,NN]], healthy = False];
				,
					healthy = False;
				];
			,
				healthy = False
			];
			If[!healthy,
				tmp = sn[[chunk*cnt+1;;Min[chunk*(cnt+1),Length[sn]]]];
				ans = table[
					MonoCharge[tmp[[i]],NN]
				,
					{i,1,Length[tmp]}
				];
				singleTrace[singleTraceCharge,degree,NN] = ans;
				DumpSave[subfilename,singleTrace];
			];
			ClearAll[singleTrace,ans,tmp];
			cnt+=1;
		];
		tot = cnt-1;
		ans = {};
		Do[
			Get[filename<>"-"<>ToString[cnt]<>".mx"];
			ans = Join[ans,singleTrace[singleTraceCharge,degree,NN]];
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
	fn = singleDirectory<>ToString[level]<>"_"<>StringRiffle[ToString[#]&/@charges,"_"]<>"_"<>ToString[degree]<>"_"<>ToString[NN];
	filename = fn <> ".mx";
	If[!FileExistsQ[filename],
		ClearAll[singleTrace];
		(* time constrain *)
		TimeConstrained[
			Check[
				singleTrace[charges,degree,NN]=SingleTrace[charges,degree,NN,fn];
			,
				Print["> terminated due to error"];
				ResetKernels[];
				Continue[];
			];
			DumpSave[filename,singleTrace];
			tmp = singleTrace[charges,degree,NN];
			ClearAll[singleTrace];
			Get[filename];
			If[tmp =!= singleTrace[charges,degree,NN],
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
