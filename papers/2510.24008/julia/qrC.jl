using LinearAlgebra, SparseArrays, MAT, MatrixMarket


length(ARGS) == 4 || error("Wrong argument count")
ARGS[1] == "Float64" || error("This release supports the original Float64 path only")
MyFloat = Float64
cutoff = parse(Float64, ARGS[2])
isfinite(cutoff) && cutoff >= 0 || error("Invalid cutoff")
inPath = ARGS[3]
outPath = ARGS[4]


data = matread(inPath)
length(data) == 1 || error("Expected one matrix per MAT file")
name = first(keys(data))
A = data[name]
data = nothing; GC.gc()

A = MyFloat.(A)
@time Gs = A * transpose(A)
A = nothing; GC.gc()

if MyFloat == Float64 || MyFloat == Float32 || MyFloat == Float16
    @time G  = Matrix{MyFloat}(Gs)
    Gs = nothing; GC.gc()
    @time F = qr(G, Val(true))
    diagR = abs.(diag(F.R))
    scaleG = isempty(diagR) ? 0.0 : maximum(diagR)
    rank_tol = max(cutoff, 10*eps(Float64)*scaleG)
    r = count(>(rank_tol), diagR)
    println("[INFO] rank_tol = $(rank_tol) (cutoff=$(cutoff), scaleG=$(scaleG))")
    println("[INFO] estimated rank r = $(r)")
    s  = sort(diagR; rev=true)
    lo = max(1, r-3); hi = min(length(s), r+3)
    println("[INFO] diagR (desc) around r=$r:")
    for k in lo:hi
        println("  ", k, ": ", s[k], k==r ? "  <-- r" : "")
    end
    p = F.jpvt
    row_basis_idx = p[1:r]
else
    @time G  = Matrix(Gs)
    Gs = nothing; GC.gc()
    @time F = qr(G, Val(true))
    diagR = abs.(diag(F.R))
    @show sort(diagR)
    scaleG = isempty(diagR) ? 0.0 : maximum(diagR)
    rank_tol = max(cutoff, 10*eps(Float64)*scaleG)
    r = count(>(rank_tol), diagR)
    println("[INFO] rank_tol = $(rank_tol) (cutoff=$(cutoff), scaleG=$(scaleG))")
    println("[INFO] estimated rank r = $(r)")
    p = F.jpvt
    row_basis_idx = p[1:r]
end

open(outPath, "w") do io
    for index in row_basis_idx
        println(io, index)
    end
end
