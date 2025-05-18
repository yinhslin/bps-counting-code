(* ::Package:: *)

(* ::Section:: *)
(*Single Trace*)


(*Protect[nzn,nzp,n\[Theta]1,n\[Theta]2,n\[Theta]3,z1,z2,th1,th2,th3];*)

group = If[specialQ && NN==2,
	DihedralGroup,
	CyclicGroup
];

Seeds[singleTraceCharge_,degree_] := Module[{pivot = Position[singleTraceCharge,_?(#>0&)][[1,1]],range},
	Which[
		su122Q, If[singleTraceCharge[[5]]!=degree,Return[{{},{},{},{},{}}]];
		,
		su121Q, If[singleTraceCharge[[4]]!=degree||singleTraceCharge[[5]]!=degree,Return[{{},{},{},{},{}}]];
	];
	Table[
		Which[
			su122Q, range = Which[i<=2,Range[0,100],i==3||i==4,{0,1},i==5,{1}];
			,
			su121Q, range = Which[i<=2,Range[0,100],i==3,{0,1},i==4||i==5,{1}];
			,
			True, range = If[i<=2,Range[0,100],{0,1}];
		];
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
(*	index[a1_,a2_,a3_,a4_,a5_,i_,j_]:=Mod[a3+a4+a5+1,2]*2^15+a1*2^11+a2*2^7+a3*2^6+a4*2^5+a5*2^4+(i-1)*2^2+(j-1);
	fp[a_]:=Quotient[a,2^15];
	nz1[a_]:=Quotient[Mod[a,2^15],2^11];
	nz2[a_]:=Quotient[Mod[a,2^11],2^7];
	n\[Theta]1[a_]:=Quotient[Mod[a,2^7],2^6];
	n\[Theta]2[a_]:=Quotient[Mod[a,2^6],2^5];
	n\[Theta]3[a_]:=Quotient[Mod[a,2^5],2^4];
	mati[a_]:=Quotient[Mod[a,2^4],2^2]+1;
	matj[a_]:=Mod[a,2^2]+1;*)
	Log2NN=Log[2,NN]//Ceiling;
	index[a1_,a2_,a3_,a4_,a5_,i_,j_]:=Mod[a3+a4+a5+1,2]*2^(2*Log2NN+11)+a1*2^(2*Log2NN+7)+a2*2^(2*Log2NN+3)+a3*2^(2*Log2NN+2)+a4*2^(2*Log2NN+1)+a5*2^(2*Log2NN)+(i-1)*2^Log2NN+(j-1);
	fp[a_]:=Quotient[a,2^(2*Log2NN+11)];
	nz1[a_]:=Quotient[Mod[a,2^(2*Log2NN+11)],2^(2*Log2NN+7)];
	nz2[a_]:=Quotient[Mod[a,2^(2*Log2NN+7)],2^(2*Log2NN+3)];
	n\[Theta]1[a_]:=Quotient[Mod[a,2^(2*Log2NN+3)],2^(2*Log2NN+2)];
	n\[Theta]2[a_]:=Quotient[Mod[a,2^(2*Log2NN+2)],2^(2*Log2NN+1)];
	n\[Theta]3[a_]:=Quotient[Mod[a,2^(2*Log2NN+1)],2^(2*Log2NN)];
	mati[a_]:=Quotient[Mod[a,2^(2*Log2NN)],2^Log2NN]+1;
	matj[a_]:=Mod[a,2^Log2NN]+1;
	
	If[specialQ&&(!spQ),
		X[a_] := - Sum[X[index[nz1[a],nz2[a],n\[Theta]1[a],n\[Theta]2[a],n\[Theta]3[a],k,k]],{k,1,NN-1}]/;mati[a]==NN&&matj[a]==NN;
	];
	If[spQ,
		X[a_] := - X[index[nz1[a],nz2[a],n\[Theta]1[a],n\[Theta]2[a],n\[Theta]3[a],matj[a]+NN/2,mati[a]+NN/2]]/;NN/2>=mati[a]&&NN/2>=matj[a];
		X[a_] := X[index[nz1[a],nz2[a],n\[Theta]1[a],n\[Theta]2[a],n\[Theta]3[a],matj[a]+NN/2,mati[a]-NN/2]]/;NN/2<mati[a]&&NN/2>=matj[a]&&mati[a]-NN/2>matj[a];
		X[a_] := X[index[nz1[a],nz2[a],n\[Theta]1[a],n\[Theta]2[a],n\[Theta]3[a],matj[a]-NN/2,mati[a]+NN/2]]/;NN/2>=mati[a]&&NN/2<matj[a]&&mati[a]+NN/2>matj[a];
	];
	If[soQ,
		X[a_] := - X[index[nz1[a],nz2[a],n\[Theta]1[a],n\[Theta]2[a],n\[Theta]3[a],matj[a],mati[a]]]/;mati[a]>matj[a];
		X[a_] := 0/;mati[a]==matj[a];
	];
	X[a_]:=0/;nz1[a]==0&&nz2[a]==0&&n\[Theta]1[a]==0&&n\[Theta]2[a]==0&&n\[Theta]3[a]==0;

	Grading[ a_Plus ] := Max @@ (Grading /@ (List @@ a));
	Grading[ a_Times ] := Plus @@ (Grading /@ (List @@ a));
	Grading[ a_NonCommutativeMultiply ] := Plus @@ (Grading /@ (List @@ a));
	Grading[ _ ] := 0;
	Grading[ a_X ] := fp[a[[1]]];
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

	CreateWord[singleTrace_,NNN_] := (Table[ X[index[#[[1]],#[[2]],#[[3]],#[[4]],#[[5]],i,j]] ,{i,1,NNN},{j,1,NNN}]) &/@ singleTrace;
(*	CreateWord[singleTrace_] := (X@@#) &/@ singleTrace;
	LoadMatrix[NN_] := X[a__]:>Table[XX[EvenQ[{a}[[3]]+{a}[[4]]+{a}[[5]]],a,i,j],{i,1,NN},{j,1,NN}];*)
	MonoCharge[singleTrace_,NN_] := (TraceP[CreateWord[singleTrace,NN]]//.Join[NonCommutativeMultiplyRules,GExpandRule]//Expand);

];

Stuff[];

SingleTrace[singleTraceCharge_,degree_,NN_,filename_] := Module[{sn,ans,cnt,tmp,tot,subfilename,healthy,donelist,worklist,statusTask,res},
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
				(*SetSharedVariable[donelist,worklist];
				worklist = {};
				donelist = {};
				statusTask = CreateScheduledTask[
					Print[
						DateString[{"Year","-","Month","-","Day"," ","Hour",":","Minute",":","Second"}],
							"  Done: ",Sort[donelist],
							"  Working: ",Sort[Complement[worklist,donelist]],
							"  Remaining: ",Complement[Range[Length[tmp]],worklist[[;;,1]]]
						];
						, 600
				];
				StartScheduledTask[statusTask];*)
				ans = table[
					(*AppendTo[worklist,{i,$KernelID}];*)
					res = MonoCharge[tmp[[i]],NN];
					(*AppendTo[donelist,{i,$KernelID}];*)
					res	
				,
					{i,1,Length[tmp]}
				];
				(*StopScheduledTask[statusTask];
				RemoveScheduledTask[statusTask];*)
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

(*SingleTrace[singleTraceCharge_,degree_,NN_,filename_] := Module[{sn,ans,cnt,tmp,tot,subfilename,healthy},
	sn = SingleNecklaces[singleTraceCharge,degree];
	Print["length: ", Length[sn]];
	If[Length[sn]>0,
		do[
			subfilename = filename<>"-"<>ToString[i]<>".mx";
			healthy = True;
			Check[
					Get[subfilename];
					If[!ListQ[singleTrace[singleTraceCharge,degree,NN]], healthy = False];
				,
					healthy = False;
			];
			If[!healthy,
				singleTrace[singleTraceCharge,degree,NN] = MonoCharge[tmp[[i]],NN];
				DumpSave[subfilename,singleTrace];
			];
			ClearAll[singleTrace];
		,
			{i,1,Length[sn]}
		];
		ans = {};
		Do[
			Get[filename<>"-"<>ToString[i]<>".mx"];
			ans = Join[ans,singleTrace[singleTraceCharge,degree,NN]];
			ClearAll[singleTrace];
		,
			{i,0,Length[sn]}
		];
	,
		ans = {};
	];
	DeleteCases[ans,0]
];*)


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
