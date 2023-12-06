(* ::Package:: *)

(* ::Section:: *)
(*Perm*)


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

	MaxDeg[charges_] := Plus@@charges;
	If[schurQ,
		PermCharges[perm1_,perm2_,charges_] := Join[charges[[1;;3]],Permute[charges[[4;;5]],perm2]];
		Perms[charges_] := Flatten[Table[{perm1,perm2,PermCharges[perm1,perm2,charges]},{perm1,SymmetricGroup[1]},{perm2,SymmetricGroup[2]}],1]//DeleteDuplicates[#,#1[[3]]==#2[[3]]&]&;
	,
		PermCharges[perm1_,perm2_,charges_] := Join[Permute[charges,perm1],Permute[charges[[3;;5]],perm2]];
		Perms[charges_] := Flatten[Table[{perm1,perm2,PermCharges[perm1,perm2,charges]},{perm1,SymmetricGroup[2]},{perm2,SymmetricGroup[3]}],1]//DeleteDuplicates[#,#1[[3]]==#2[[3]]&]&;
		(*PermCharges[charges_] := Flatten[Table[Join[c[[1;;2]],Permute[c[[3;;5]],g]],{c,Permute[charges,#]&/@SymmetricGroup[2]},{g,SymmetricGroup[3]}],1]//DeleteDuplicates//DeleteCases[#,charges]&;*)
	];

	Perm[seed_,perm_] := Module[{ans,repl,repl0},
		If[Which[
				su122Q,Length[seed]>0&&perm[[2,3]]==3,
				True,Length[seed]>0
			],
			repl = {(X[c_]):>(X[ index[ Sequence@@PermCharges[perm[[1]],perm[[2]],{nz1[c],nz2[c],n\[Theta]1[c],n\[Theta]2[c],n\[Theta]3[c]}],mati[c],matj[c] ] ])};
			ans = Table[
				seed[[i]] /. repl //.NonCommutativeMultiplyRules
			,
				{i,1,Length[seed]}
			];
			Assert[Length[ans]==Length[seed]];
		,
			ans = {};
		];
		DeleteCases[ans,0]
	];

];

Stuff[];


(* ::Section:: *)
(*Execute*)


Exec[] := Module[{},
	filename = singleDirectory<>ToString[level]<>"_"<>StringRiffle[ToString[#]&/@charges,"_"]<>"_"<>ToString[degree]<>"_"<>ToString[NN]<>".mx";
	If[!FileExistsQ[filename],
		Print[filename, "does not exist!"]; Continue[];
	];
	Get[filename];
	seed = singleTrace[charges,degree,NN];
	perms = Perms[charges];
	TimeConstrained[
	do[
		(*Stuff[];*)
		newCharges = perm[[3]];
		newFilename = singleDirectory<>ToString[level]<>"_"<>StringRiffle[ToString[#]&/@newCharges,"_"]<>"_"<>ToString[degree]<>"_"<>ToString[NN]<>".mx";
		If[!FileExistsQ[newFilename],
			ClearAll[singleTrace];
			Check[
				singleTrace[newCharges,degree,NN] = Perm[seed, perm];
				(*singleTrace[newCharges,degree,NN] = seed /. {(XB[c_,i_]):>(XB@@{PermCharges[perm[[1]],perm[[2]],c],i}),(XF[c_,i_]):>(XF@@{PermCharges[perm[[1]],perm[[2]],c],i})};*)
			,
				Print["> terminated due to error"];
				ResetKernels[];
				Continue[];
			];
			DumpSave[newFilename,singleTrace];
			tmp = singleTrace[charges,degree,NN];
			ClearAll[singleTrace];
			Get[newFilename];
			If[tmp =!= singleTrace[charges,degree,NN],
				DeleteFile[newFilename];
			];
		];
		MyShare[];
	,
		{perm,perms}
	];
	,
		time
	,
		Print["> overtime"];
		ResetKernels[];
	];
];
