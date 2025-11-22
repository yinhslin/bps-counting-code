(* ::Package:: *)

(* ::Section:: *)
(*Independent Graviton*)


(* ::Subsubsection:: *)
(*Independent exact and Multi-graviton*)


IndependentGraviton[charges_,degree_,NN_] := Module[{level,filename,ans},
	level = charges . levelvector;
	filename = indGravitonDirectory<>ToString[level]<>"_"<>StringRiffle[ToString[#]&/@charges,"_"]<>"_"<>ToString[degree]<>"_"<>ToString[NN]<>".mx";
	If[FileExistsQ[filename],
		Get[filename];
	,
		Return[{{},{}}];
	];
	ans = independentGraviton[charges,degree,NN];
	Clear[independentGraviton];
	ans
];


(* ::Subsubsection:: *)
(*Q and Non-commutative multiply*)


Stuff[] := Module[{},
	(* index relations *)
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

	(* matrix and product *)
	If[specialQ&&(!spQ),
		X[a_] := -Sum[X[index[nz1[a],nz2[a],n\[Theta]1[a],n\[Theta]2[a],n\[Theta]3[a],k,k]],{k,1,NN-1}]/;mati[a]==NN&&matj[a]==NN;
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

	If[soQ,
		neg = SparseArray[BlockDiagonalMatrix[{KroneckerProduct[{{0,-1},{0,0}},IdentityMatrix[Floor[NN/2]]],{{0}}}]]["ExplicitPositions"];
		zeros =Complement[Flatten[Table[{i,j},{i,1,NN},{j,i+1,NN}],1],neg];
		AbelianizeRules = Table[X[index[a1,a2,a3,a4,a5,Sequence@@ij]]->0,{a1,0,15},{a2,0,15},{a3,0,1},{a4,0,1},{a5,0,1},{ij,zeros}]//Flatten//DeleteDuplicates;
	];
	If[spQ,
		neg = SparseArray[KroneckerProduct[{{0,0},{0,-1}},IdentityMatrix[Floor[NN/2]]]]["ExplicitPositions"];
		zeros = Complement[Join[Flatten[Table[{i,j},{i,NN/2+1,NN},{j,NN/2+1,NN}],1],Flatten[Table[{i,j},{i,1,NN/2},{j,i+NN/2,NN}],1],Flatten[Table[{i,j},{i,NN/2+1,NN},{j,i-NN/2,NN/2}],1]],neg];
		AbelianizeRules = Table[X[index[a1,a2,a3,a4,a5,Sequence@@ij]]->0,{a1,0,15},{a2,0,15},{a3,0,1},{a4,0,1},{a5,0,1},{ij,zeros}]//Flatten//DeleteDuplicates;
	];
	times[n_,a__]:=n times[a]/;NumericQ[n];
	times[a_]:=a;
];

Stuff[];


(* ::Subsubsection::Closed:: *)
(*Numerical*)


(* ::Text:: *)
(*Install Julia from https://julialang.org/*)
(*Install necessary packages by running the following commands within Julia:*)
(*import(Pkg);*)
(*Pkg.add(["LinearAlgebra", "SparseArrays", "SuiteSparse", "DelimitedFiles", "DoubleFloats", "MultiFloats", "MatrixMarket", "RowEchelon", "ZChop", "JLD2"]);*)


If[numerical,
	julia = "julia";
	(*qr = home <> "qr.jl";*)
	dotqr = GetEnvironment["HOME"][[2]]<>"/projects/bps/src/dotqrC.jl";
	dotqr = StringReplace[StringReplace[dotqr,{" "->"\ "}],{"("->"\(",")"->"\)","\ "->"\\\ "}];
	(* A must be a sparse matrix *)
	RowReduceProduct[A_,B_] := Module[{ans,id,dir,dirX},
		Print["A density: ", A["Density"]];
		Print["A dimension: ", Dimensions[A]];
		Print["B density: ", B["Density"]];
		Print["B dimension: ", Dimensions[B]];
		id = ToString[RandomInteger[10^10]];
		dir = juliaDirectory<>id<>"/";
		While[FileExistsQ[dir],
			id = ToString[RandomInteger[10^10]];
			dir = juliaDirectory<>id<>"/";
		];
		Print[dir];
		dirX = StringReplace[dir,{"("->"\(",")"->"\)","\ "->"\\\ "}];
		
		(*Print["Exporting "<>dir<>"in_A.mtx"];
		Export[dir<>"in_A.mtx",A];
		Print["Exporting "<>dir<>"in_B.mtx"];
		Export[dir<>"in_B.mtx",B];
		Print["Running Julia"];
		Print["Memory Available: ",MemoryAvailable[]/2^30//N," GB"];
		Run[julia<>" "<>dotqr<>" Float64 1e-10 "<>dirX<>"in_A.mtx"<>" "<>dirX<>"in_B.mtx"<>" "<>dirX<>"out.mtx"];
		Print["Finished Julia"];*)
		
		Print["Exporting "<>dir<>"in_A.mat"];
		Export[dir<>"in_A.mat",A];
		Print["Exporting "<>dir<>"in_B.mat"];
		Export[dir<>"in_B.mat",B];
		Print["Running Julia"];
		Print["Memory Available: ",MemoryAvailable[]/2^30//N," GB"];
		Run[julia<>" "<>dotqr<>" Float64 1e-7 "<>dirX<>"in_A.mat"<>" "<>dirX<>"in_B.mat"<>" "<>dirX<>"out.mtx"];
		Print["Finished Julia"];
		
		Print["Importing "<>dir<>"out.mtx"];
		Print["Spliting mtx file"];
		Print["Memory Available: ",MemoryAvailable[]/2^30//N," GB"];
		Run["bash ~/projects/bps/src/split.sh "<>dir<>"out.mtx "<>dir<>"chunks "<>ToString[800000000]];
		Print["Reading mtx files"];
		Print["Memory Available: ",MemoryAvailable[]/2^30//N," GB"];
		Do[
			sub[f] = Import[f,"MTX"];
			,
			{f,FileNames["*",dir<>"chunks"]}
		];
		
		Print["Summing sparse matrices"];
		Print["Memory Available: ",MemoryAvailable[]/2^30//N," GB"];
		ans = Sum[sub[f],{f,FileNames["*",dir<>"chunks"]}];
		
		Do[DeleteFile[f];,{f,FileNames["*",dir<>"chunks"]}];
		DeleteFile[dir<>"in_A.mat"];
		DeleteFile[dir<>"in_B.mat"];
		DeleteFile[dir<>"out.mtx"];
		DeleteDirectory[dir<>"chunks"];
		DeleteDirectory[dir];
		
		ans
	];
];


(* ::Subsubsection:: *)
(*Independence*)


CollectTerms[lis_]:=DeleteCases[DeleteDuplicates[Flatten[lis/.Plus->List/.{n_ a_:>a/;NumericQ[n]}/.{-a_:>a}]],0];

T2t[traces_]:=Module[{rTraces},
	rTraces = Table[t/.Times->times/.Power->power,{t,traces}];
	rTraces
];
t2T[traces_]:=Module[{rTraces},
	rTraces = Table[t/.times->Times/.power->Power,{t,traces}];
	rTraces
];

Abelianize[Allterms_] := Module[{ans},
	ans = table[
		t/.AbelianizeRules//.Join[NonCommutativeMultiplyRules,GExpandRule]//ExpandAll
	,
		{t,Allterms}
	];
	ans
];

ReducedGraviton[charges_,degree_,NN_]:=Module[{level, indgrav,AllGravTerm,chunk,batches,filename,reducedTerm,ind,AllRTerms,Rmatrix,RVector,SimpRVector},
	level = charges . levelvector;
	indgrav = IndependentGraviton[charges, degree, NN];
	Unprotect[NonCommutativeMultiply];
	SetAttributes[NonCommutativeMultiply, Listable];
	ClearAttributes[NonCommutativeMultiply, Flat];
	Protect[NonCommutativeMultiply];
	AllGravTerm = indgrav[[2]];
	
	Print["Spliting jobs"];
	chunk = 1500000;
	batches = Partition[AllGravTerm, UpTo[chunk]];
	Print["chunk = ", chunk, "  batches = ", Length@batches];
	Print["Computing Abelianization"];
	Do[
		reducedGraviton[charges,degree,NN] = Abelianize[batches[[i]]];
		filename = reducedGravitonDirectory<>ToString[level]<>"_"<>StringRiffle[ToString[#]&/@charges,"_"]<>"_"<>ToString[degree]<>"_"<>ToString[NN]<>"-"<>ToString[i]<>".mx";
		DumpSave[filename,reducedGraviton];
		Print["Saved "<>ToString[i]<>"-th temporary result"];
		ClearAll[reducedGraviton];
	,
		{i,1,Length[batches]}
	];
	reducedTerm = {};
	Do[
		filename = reducedGravitonDirectory<>ToString[level]<>"_"<>StringRiffle[ToString[#]&/@charges,"_"]<>"_"<>ToString[degree]<>"_"<>ToString[NN]<>"-"<>ToString[i]<>".mx";
		Get[filename];
		reducedTerm = Join[reducedTerm,reducedGraviton[charges,degree,NN]];
		ClearAll[reducedGraviton];
	,
		{i,1,Length[batches]}
	];
	Print["Finished Abelianization"];
	
	filename = reducedGravitonDirectory<>ToString[level]<>"_"<>StringRiffle[ToString[#]&/@charges,"_"]<>"_"<>ToString[degree]<>"_"<>ToString[NN]<>"-temp.mx";
	If[!FileExistsQ[filename],
		ind = indgrav[[1]];
		
		Print["T2t Q stuff"];
		Print["Memory Available: ",MemoryAvailable[]/2^30//N," GB"];
		reducedTerm = T2t[reducedTerm];
		
		Print["Collecting terms"];
		Print["Memory Available: ",MemoryAvailable[]/2^30//N," GB"];
		AllRTerms = CollectTerms[DeleteDuplicates[reducedTerm]];	
		
		Print["Finding R matrix"];
		Print["Memory Available: ",MemoryAvailable[]/2^30//N," GB"];
		Rmatrix = CoefficientArrays[reducedTerm,AllRTerms][[2]];
		
		Print["t2T all R terms"];
		Print["Memory Available: ",MemoryAvailable[]/2^30//N," GB"];
		AllRTerms = t2T[AllRTerms];
		
		Print["Saving temporary results"];
		reducedGravitonTemp[charges,degree,NN] = {ind, Rmatrix, AllRTerms};
		DumpSave[filename,reducedGravitonTemp];
		ClearAll[reducedGravitonTemp,AllRTerms,reducedTerm];
	,
		Print["Loading back ind and Rmatrix"];
		Print["Memory Available: ",MemoryAvailable[]/2^30//N," GB"];
		Get[filename];
		ind = reducedGravitonTemp[charges,degree,NN][[1]];
		Rmatrix = reducedGravitonTemp[charges,degree,NN][[2]];
		ClearAll[reducedGravitonTemp];
	];
	
	Print["Computing R vector and starting row reduce"];
	Print["Memory Available: ",MemoryAvailable[]/2^30//N," GB"];
	If[numerical,
		SimpRVector = RowReduceProduct[ind,Rmatrix];
		ClearAll[ind,Rmatrix];
	,
		RVector = SparseArray[ind . Rmatrix];
		ClearAll[ind,Rmatrix];
		SimpRVector = RowReduce[RVector];
		SimpRVector = DeleteCases[SimpRVector,Table[0,{l,1,Length[SimpRVector[[1]]]}]];
	];
	
	Print["Loading back AllQTerms"];
	Print["Memory Available: ",MemoryAvailable[]/2^30//N," GB"];
	Get[filename];
	AllRTerms = reducedGravitonTemp[charges,degree,NN][[3]];
	Print["Memory Available: ",MemoryAvailable[]/2^30//N," GB"];
	
	{SimpRVector,AllRTerms}
];


(* ::Section:: *)
(*Execute*)


Exec[] := Module[{},
	filename = reducedGravitonDirectory<>ToString[level]<>"_"<>StringRiffle[ToString[#]&/@charges,"_"]<>"_"<>ToString[degree]<>"_"<>ToString[NN]<>".mx";
	If[!FileExistsQ[filename],
		ClearAll[exact];
		TimeConstrained[
			Check[
				reducedGraviton[charges,degree,NN] = ReducedGraviton[charges,degree,NN];
			,
				Print["> terminated due to error"];
				ResetKernels[];
				Continue[];
			];
			DumpSave[filename,reducedGraviton];
			Print["Saved result"];
			tmp = reducedGraviton[charges,degree,NN];
			ClearAll[reducedGraviton];
			Get[filename];
			If[tmp =!= reducedGraviton[charges,degree,NN],
				DeleteFile[filename];
				,
				If[FileExistsQ[StringReplace[filename,".mx"->"-temp.mx"]],
					DeleteFile[StringReplace[filename,".mx"->"-temp.mx"]];
				];
			];
		,
			time
		,
			Print["> overtime"];
			ResetKernels[];
		];
	];
];
