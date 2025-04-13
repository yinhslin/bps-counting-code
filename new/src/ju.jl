using LinearAlgebra
using SparseArrays, SuiteSparse
using MatrixMarket
using DelimitedFiles

path = ARGS[1]

@time A = MatrixMarket.mmread("/n/holyscratch01/yin_lab/Users/yhlin/bps/all/julia/" * path * "/in.mtx")
A = Float64.(A)

@time AQR = qr(A)
diagR = abs.(diag(AQR.R))
diagR = sort(diagR)
diagR = diagR / maximum(diagR)
dep = findall(x -> abs(x)>1e-5, diagR)
@show length(dep)
@show diagR[max(1,dep[1]-10):min(length(diagR),dep[1]+10)]

open("/n/holyscratch01/yin_lab/Users/yhlin/bps/all/julia/" * path * "/R.csv", "w") do file
    writedlm(file, diagR)
end