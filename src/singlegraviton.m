(* ::Package:: *)

(* ::Section:: *)
(*Single Graviton*)


(*Protect[nzn,nzp,n\[Theta]1,n\[Theta]2,n\[Theta]3,z1,z2,th1,th2,th3,X];*)

TwoGroupsData[singleGravCharge_,degree_]:=Module[{lis={},x},
	Do[
		x={x1,x2,singleGravCharge[[3]]-x3,singleGravCharge[[4]]-x4,singleGravCharge[[5]]-x5};
		If[Total[x]==degree,
			AppendTo[lis,{singleGravCharge-x,x}];
		];
	,
		{x1,0,Min[singleGravCharge[[1]],1]},{x2,0,Min[singleGravCharge[[2]],1]},{x3,0,Min[singleGravCharge[[3]],1]},{x4,0,Min[singleGravCharge[[4]],1]},{x5,0,Min[singleGravCharge[[5]],1]}
	];
	lis
];

S[A_,B_] := Inner[NonCommutativeMultiply,A,B,Plus];

TraceP[Xlist_] := Module[{prod,LL,ans},
	LL=Length[Xlist];
	If[LL>=2,
		prod=S[Xlist[[1]],Xlist[[2]]];
		Do[prod=S[prod,Xlist[[m]]],{m,3,LL}];
	,
		prod=Xlist[[1]]
	];
	(*SetNonCommutativeMultiply[];*)
	ans = Tr[prod];
	(*Unprotect[NonCommutativeMultiply];
	ClearAll[NonCommutativeMultiply];
	Protect[NonCommutativeMultiply];*)
	ans
];

CreateWord[singleTrace_,NN_] := Flatten[Table[Table[Table[
	If[i==j&&specialQ,
		Which[NN==2&&i==1,
			1/Sqrt[2] X[index[Sequence@@UnitVector[5,k],1,1]],
			NN==2&&i==2,
			-(1/Sqrt[2])X[index[Sequence@@UnitVector[5,k],1,1]],
			NN==3&&i==1,
			-(1/Sqrt[2])X[index[Sequence@@UnitVector[5,k],1,1]]+1/Sqrt[6] X[index[Sequence@@UnitVector[5,k],2,2]],
			NN==3&&i==2,
			1/Sqrt[2] X[index[Sequence@@UnitVector[5,k],1,1]]+1/Sqrt[6] X[index[Sequence@@UnitVector[5,k],2,2]],
			NN==3&&i==3,
			-Sqrt[2/3]X[index[Sequence@@UnitVector[5,k],2,2]],
			NN==4&&i==1,
			-(1/Sqrt[2])X[index[Sequence@@UnitVector[5,k],1,1]]-1/Sqrt[6] X[index[Sequence@@UnitVector[5,k],2,2]]+1/(2Sqrt[3]) X[index[Sequence@@UnitVector[5,k],3,3]],
			NN==4&&i==2,
			Sqrt[2/3]X[index[Sequence@@UnitVector[5,k],2,2]]+1/(2Sqrt[3]) X[index[Sequence@@UnitVector[5,k],3,3]],
			NN==4&&i==3,
			1/Sqrt[2] X[index[Sequence@@UnitVector[5,k],1,1]]-1/Sqrt[6] X[index[Sequence@@UnitVector[5,k],2,2]]+1/(2Sqrt[3]) X[index[Sequence@@UnitVector[5,k],3,3]],
			NN==4&&i==4,
			-(Sqrt[3]/2)X[index[Sequence@@UnitVector[5,k],3,3]]
			]
		,
		X[index[Sequence@@UnitVector[5,k],i,j]]
	]
,{i,1,NN},{j,1,NN}],singleTrace[[k]]],{k,1,5}],1];

MonoCharge[singleTrace_,NN_] := (TraceP[CreateWord[singleTrace,NN]]);
PrepData[chargelist_,degree_,N_]:={#[[1]],MonoCharge[#[[2]],N]} &/@ TwoGroupsData[chargelist,degree];

Stuff[] := Module[{},
	(* index relations *)
	index[a1_,a2_,a3_,a4_,a5_,i_,j_]:=Mod[a3+a4+a5+1,2]*2^15+a1*2^11+a2*2^7+a3*2^6+a4*2^5+a5*2^4+(i-1)*2^2+(j-1);
	fp[a_]:=Quotient[a,2^15];
	nz1[a_]:=Quotient[Mod[a,2^15],2^11];
	nz2[a_]:=Quotient[Mod[a,2^11],2^7];
	n\[Theta]1[a_]:=Quotient[Mod[a,2^7],2^6];
	n\[Theta]2[a_]:=Quotient[Mod[a,2^6],2^5];
	n\[Theta]3[a_]:=Quotient[Mod[a,2^5],2^4];
	mati[a_]:=Quotient[Mod[a,2^4],2^2]+1;
	matj[a_]:=Mod[a,2^2]+1;

	Unprotect[NonCommutativeMultiply];
	ClearAll[NonCommutativeMultiply];
	SetAttributes[NonCommutativeMultiply,Flat];
	SetAttributes[NonCommutativeMultiply,OneIdentity];
	Protect[NonCommutativeMultiply];

	DD[i_][a_Plus]:=DD[i][#]&/@a;
	DD[i_][a_Times]:=Module[{alist,sign,A},
		alist=Apply[List,a];
		A=0;
		If[i>2,
			sign=1;
			Do[A=A+sign NonCommutativeMultiply@@(ReplacePart[alist,n->DD[i][alist[[n]]]]);
				sign=sign (-1)^Grading[alist[[n]]];
			,{n,alist//Length}];
		,
		Do[A=A+ NonCommutativeMultiply@@(ReplacePart[alist,n->DD[i][alist[[n]]]]);
			,{n,alist//Length}];
		];
	A
	];
	
	DD[i_][n_]:=0/;NumberQ[n];
	DD[m_][X[a_]^n_]:=n X[a]^(n-1)DD[m][X[a]]/;fp[a]==0;
(*	DD[m_][X[a_]**b_]:=DD[m][X[a]]**b + X[a]**DD[m][b]/;fp[a]==1&&m<=2;
	DD[m_][X[a_]**b_]:=DD[m][X[a]] b - X[a]**DD[m][b]/;fp[a]==1&&m>2;*)
	DD[i_][a_NonCommutativeMultiply]:=Module[{alist,sign,A},
		alist=Apply[List,a];
		A=0;
		If[i>2,
			sign=1;
			Do[A=A+sign NonCommutativeMultiply@@(ReplacePart[alist,n->DD[i][alist[[n]]]]);
				sign=sign (-1)^Grading[alist[[n]]];
			,{n,alist//Length}];
		,
		Do[A=A+ NonCommutativeMultiply@@(ReplacePart[alist,n->DD[i][alist[[n]]]]);
			,{n,alist//Length}];
		];
	A
	];

	DD[m_][X[a_]]:=X[a + Mod[m,2]*2^11 + Mod[m+1,2]*2^7 ]/;m<=2;
	DD[3][X[a_]]:=X[a + (-1)^fp[a]*2^15 + 2^6 ]/;n\[Theta]1[a]==0;
	DD[4][X[a_]]:=(-1)^(n\[Theta]1[a]) X[a + (-1)^fp[a]*2^15 + 2^5 ]/;n\[Theta]2[a]==0;
	DD[5][X[a_]]:=(-1)^(n\[Theta]1[a]+n\[Theta]2[a]) X[a + (-1)^fp[a]*2^15 + 2^4 ]/;n\[Theta]3[a]==0;
	DD[3][X[a_]]:=0/;n\[Theta]1[a]==1;
	DD[4][X[a_]]:=0/;n\[Theta]2[a]==1;
	DD[5][X[a_]]:=0/;n\[Theta]3[a]==1;

	(* matrix and product *)
	If[specialQ,
		X[a_] := -Sum[X[Quotient[a,2^4]*2^4 + 5 k],{k,0,NN-2}]/;Mod[a-(NN-1)*2^2-(NN-1),2^4]==0;
	];
	X[a_]:=0/;Quotient[a,2^5]==2^10;

	Grading[ a_Plus ] := Max @@ (Grading /@ (List @@ a));
	Grading[ a_Times ] := Plus @@ (Grading /@ (List @@ a));
	Grading[ a_NonCommutativeMultiply ] := Plus @@ (Grading /@ (List @@ a));
	Grading[ _ ] := 0;
	Grading[ a_X ] := fp[a[[1]]];

	Unprotect[NonCommutativeMultiply];
	SetAttributes[NonCommutativeMultiply, Listable];
	ClearAttributes[NonCommutativeMultiply, Flat];
	NonCommutativeMultiply[a___, b_NonCommutativeMultiply, c___] := NonCommutativeMultiply[a, Sequence@@b, c];
	GetGradeds[a___] := (*GetGradeds[a] =*) Select[{a}, Grading[#] != 0 &];
	GetFermions[a___] := (*GetFermions[a] =*) Select[{a}, OddQ[Grading[#]] &];
	NonCommutativeMultiply[a___] /; Length[GetGradeds[a]] <= 1 := Times[a];
	NonCommutativeMultiply[a___] /; !FreeQ[{a}, Times, 2] := NonCommutativeMultiply @@ ReplacePart[ {a}, Sequence, Position[{a}, Times, 2] ];
	NonCommutativeMultiply[b___, a_, c___, a_, d___] /; OddQ[Grading[a]] := 0;
	NonCommutativeMultiply[a___] /; (!OrderedQ[GetGradeds[a]] || Length[GetGradeds[a]] != Length[{a}] ) :=
		Signature[GetFermions[a]] * (Times @@ Select[{a}, !MemberQ[GetGradeds[a], #]&]) * NonCommutativeMultiply @@ Sort[GetGradeds[a]];
	Protect[NonCommutativeMultiply];
	GExpand[a_, patt___] := Expand[a //. {x_NonCommutativeMultiply :> Distribute[x]}, patt];
	ApplyDD[{zlis_,expr_}]:=Module[{tmp},tmp=expr;Do[tmp=Nest[DD[6-r][#] &,tmp,zlis[[6-r]]],{r,1,5}];tmp];

];

Stuff[];

(*SingleGraviton[singleTraceCharge_,degree_,NN_] := Module[{sn,ans},
	sn = PrepData[singleTraceCharge,degree,NN];
	Print["length: ", Length[sn]];
	If[Length[sn]>0,
		ans = table[
			ApplyDD[sn[[i]]]//GExpand
		,
			{i,1,Length[sn]}
		];
		Assert[Length[ans]==Length[sn]];
	,
		ans = {};
	];
	DeleteCases[ans,0]
];*)

SingleGraviton[singleTraceCharge_,degree_,NN_,filename_] := Module[{sn,ans,cnt,tmp,tot,subfilename,healthy},
	sn = PrepData[singleTraceCharge,degree,NN];
	Print["length: ", Length[sn]];
	If[Length[sn]>0,
		cnt = 0;
		While[chunk*cnt<Length[sn],
			subfilename = filename<>"-"<>ToString[cnt]<>".mx";
			healthy = True;
			If[FileExistsQ[subfilename],
				Check[
					Get[subfilename];
					If[!ListQ[singleGraviton[singleTraceCharge,degree,NN]], healthy = False];
				,
					healthy = False;
				];
			,
				healthy = False
			];
			If[!healthy,
				tmp = sn[[chunk*cnt+1;;Min[chunk*(cnt+1),Length[sn]]]];
				ans = table[
					ApplyDD[tmp[[i]]]//GExpand
				,
					{i,1,Length[tmp]}
				];
				singleGraviton[singleTraceCharge,degree,NN] = ans;
				DumpSave[subfilename,singleGraviton];
			];
			ClearAll[singleGraviton,ans,tmp];
			cnt+=1;
		];
		tot = cnt-1;
		ans = {};
		Do[
			Get[filename<>"-"<>ToString[cnt]<>".mx"];
			ans = Join[ans,singleGraviton[singleTraceCharge,degree,NN]];
			ClearAll[singleGraviton];
		,
			{cnt,0,tot}
		];
		Assert[Length[ans]==Length[sn]];
		(*If[Length[ans]=!=Length[sn],
			Print[ans];
			Print[Length[ans]];
			Quit[];
		,*)
			DeleteFile[#] &/@ FileNames[filename<>"-*"];
		(*];*)
	,
		ans = {};
	];
	DeleteCases[ans,0]
];


(* ::Section:: *)
(*Execute*)


Exec[] := Module[{},
	fn = singleGravitonDirectory<>ToString[level]<>"_"<>StringRiffle[ToString[#]&/@charges,"_"]<>"_"<>ToString[degree]<>"_"<>ToString[NN];
	filename = fn <> ".mx";
	If[!FileExistsQ[filename],
		ClearAll[singleGraviton];
		TimeConstrained[
			Check[
				singleGraviton[charges,degree,NN]=SingleGraviton[charges,degree,NN,fn];
			,
				Print["> terminated due to error"];
				ResetKernels[];
				Continue[];
			];
			DumpSave[filename,singleGraviton];
			tmp = singleGraviton[charges,degree,NN];
			ClearAll[singleGraviton];
			Get[filename];
			If[tmp =!= singleGraviton[charges,degree,NN],
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
