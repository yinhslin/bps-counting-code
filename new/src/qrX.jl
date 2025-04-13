using LinearAlgebra
using SparseArrays, SuiteSparse
using MatrixMarket
using DelimitedFiles
using DoubleFloats
using MultiFloats
using RowEchelon
using ZChop
using JLD2

MyFloat = eval(Symbol(ARGS[1]))
cutoff = parse(Float64, ARGS[2])
inPath = ARGS[3]
outPath = ARGS[4]
rPath = ARGS[5]

# MyFloat = Float64
# cutoff = 1e-5
# inPath = "/Users/yinhslin/Dropbox (Harvard University)/1:16 BPS revisited/math/ying/in.mtx"
# outPath = "/Users/yinhslin/Dropbox (Harvard University)/1:16 BPS revisited/math/ying/out.mtx"

A = MatrixMarket.mmread(inPath)
A = MyFloat.(A)

if MyFloat == Float64 || MyFloat == Float32 || MyFloat == Float16
    # @time rk = rank(Matrix(A))
    # @time rk = rank(A, tol=cutoff)
    @time AQR = qr(A)
    diagR = abs.(diag(AQR.R))
    diagR = sort(diagR)
    diagR = diagR / maximum(diagR)
    dep = findall(x -> abs(x)>cutoff, diagR)
    @show length(dep)
    @show diagR[max(1,dep[1]-10):min(length(diagR),dep[1]+10)]
    # @show rk
else
    A = Matrix(A)
    @time AQR = qr(A, Val(true))
    diagR = abs.(diag(AQR.R))
    # @show sort(diagR)
    dep = findall(x -> abs(x)>cutoff, diagR)
    @show length(dep)
end

open(outPath, "w") do file
    writedlm(file, length(dep))
end

open(rPath, "w") do file
    writedlm(file, diagR)
end

# println(maximum(abs.(sol)))

# println(maximum(abs.(vec(A[:,p] * vcat(sol,-Matrix(1I,630,630))))))