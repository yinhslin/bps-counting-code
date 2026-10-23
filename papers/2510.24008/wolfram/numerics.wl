(* Portable transport for the original Float64 Gram/QR row selection.
   The absolute cutoff remains 1e-7; see docs/NUMERICS.md. *)
RunChecked[args_List] := Module[{p},
 p=RunProcess[args];
 If[p["StandardOutput"]!="",Print[p["StandardOutput"]]];
 If[p["StandardError"]!="",Print[p["StandardError"]]];
 If[p["ExitCode"]!=0,Print["External calculation failed"];Abort[]];
];
NewNumericalDirectory[] := CreateDirectory[FileNameJoin[{juliaDirectory,CreateUUID["qr-"]}]];
juliaSourceDirectory = FileNameJoin[{DirectoryName[sourceDirectory],"julia"}];
If[numerical,
 MyRowReduce[A_] := Module[{dir,indices,ans},
  If[Length[A]==0,Return[A]];
  dir=NewNumericalDirectory[];
  Check[Export[FileNameJoin[{dir,"in.mat"}],A],Abort[]];
  RunChecked[{cfg["julia"],"--startup-file=no","--project="<>juliaSourceDirectory,
   FileNameJoin[{juliaSourceDirectory,"qrC.jl"}],"Float64","1e-7",
   FileNameJoin[{dir,"in.mat"}],FileNameJoin[{dir,"out.txt"}]}];
  indices=If[FileByteCount[FileNameJoin[{dir,"out.txt"}]]==0,{},Flatten[Import[FileNameJoin[{dir,"out.txt"}],"Table"]]];
  If[!VectorQ[indices,IntegerQ] || !And@@(1<=#<=Length[A]&/@indices),Abort[]];
  ans=If[indices==={},SparseArray[{},{0,Dimensions[A][[2]]}],A[[Sort[indices]]]];
  DeleteDirectory[dir,DeleteContents->True];ans
 ];
 RowReduceProduct[A_,B_] := Module[{dir,files,ans},
  If[Length[A]==0,Return[SparseArray[{},{0,Dimensions[B][[2]]}]]];
  dir=NewNumericalDirectory[];
  Check[Export[FileNameJoin[{dir,"in_A.mat"}],A];Export[FileNameJoin[{dir,"in_B.mat"}],B],Abort[]];
  RunChecked[{cfg["julia"],"--startup-file=no","--project="<>juliaSourceDirectory,
   FileNameJoin[{juliaSourceDirectory,"dotqrC.jl"}],"Float64","1e-7",
   FileNameJoin[{dir,"in_A.mat"}],FileNameJoin[{dir,"in_B.mat"}],FileNameJoin[{dir,"out.mtx"}]}];
  RunChecked[{cfg["python"],FileNameJoin[{DirectoryName[sourceDirectory],"tools","split_mtx.py"}],
   FileNameJoin[{dir,"out.mtx"}],FileNameJoin[{dir,"chunks"}],"800000000"}];
  files=Sort[FileNames["*.mtx",FileNameJoin[{dir,"chunks"}]]];
  If[files==={},Abort[]];
  ans=Total[Import[#,"MTX"]&/@files];
  DeleteDirectory[dir,DeleteContents->True];ans
 ];
,
 MyRowReduce[A_] := RowReduce[A];
 RowReduceProduct[A_,B_] := RowReduce[SparseArray[A.B]];
];
