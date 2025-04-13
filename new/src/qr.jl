using LinearAlgebra
using SparseArrays, SuiteSparse
using DelimitedFiles
using DoubleFloats
using MultiFloats
using MatrixMarket
using RowEchelon
using ZChop
using JLD2

MyFloat = eval(Symbol(ARGS[1]))
cutoff = parse(Float64, ARGS[2])
inPath = ARGS[3]
outPath = ARGS[4]

# MyFloat = Float64
# cutoff = 1e-5
# inPath = "/Users/yinhslin/Dropbox (Harvard University)/1:16 BPS revisited/math/ying/in.mtx"
# outPath = "/Users/yinhslin/Dropbox (Harvard University)/1:16 BPS revisited/math/ying/out.mtx"

A = MatrixMarket.mmread(inPath)
A = MyFloat.(A)

if MyFloat == Float64 || MyFloat == Float32 || MyFloat == Float16
    @time AQR = qr(A)
    diagR = abs.(diag(AQR.R))
    # @show sort(diagR)
    dep = findall(x -> abs(x)>cutoff, diagR)
    @show length(dep)
    ind = filter(x -> x ∉ dep, 1:size(A)[2])
    varIdx = vcat(dep,ind)
    p = sortperm(AQR.cpiv)
    sol = zchop(AQR.R[dep,p], 1e-10)
else
    A = Matrix(A)
    @time AQR = qr(A, Val(true))
    diagR = abs.(diag(AQR.R))
    # @show sort(diagR)
    dep = findall(x -> abs(x)>cutoff, diagR)
    # @show size(dep)
    ind = filter(x -> x ∉ dep, 1:size(A)[2])
    varIdx = vcat(dep,ind)
    p = AQR.p[varIdx]
    sol = zchop(AQR.R[dep,sortperm(p)], 1e-10)
    sol = sparse(sol)
end

dropzeros!(sol)
MatrixMarket.mmwrite(outPath,sol)

# println(maximum(abs.(sol)))

# println(maximum(abs.(vec(A[:,p] * vcat(sol,-Matrix(1I,630,630))))))