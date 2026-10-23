using LinearAlgebra, SparseArrays, MAT, MatrixMarket


length(ARGS) == 5 || error("Wrong argument count")
ARGS[1] == "Float64" || error("This release supports the original Float64 path only")
MyFloat = Float64
cutoff = parse(Float64, ARGS[2])
isfinite(cutoff) && cutoff >= 0 || error("Invalid cutoff")
inPathA = ARGS[3]
inPathB = ARGS[4]
outPath = ARGS[5]


data = matread(inPathA)
length(data) == 1 || error("Expected one matrix per MAT file")
name = first(keys(data))
A = data[name]
data = nothing; GC.gc()

data = matread(inPathB)
length(data) == 1 || error("Expected one matrix per MAT file")
name = first(keys(data))
B = data[name]
data = nothing; GC.gc()

if eltype(A) <: Integer && eltype(B) <: Integer
    @time C = A * B
    println("[INFO] A*B path = integer (eltypes: $(eltype(A)), $(eltype(B)))"); flush(stdout)
else
    A = MyFloat.(A)
    B = MyFloat.(B)
    @time C = A * B
    println("[INFO] A*B path = floating ($(MyFloat))"); flush(stdout)
end

A = nothing
B = nothing
GC.gc()
dropzeros!(C)

C64 = eltype(C) <: Float64 ? C :
       SparseMatrixCSC(size(C,1), size(C,2), C.colptr, C.rowval, Float64.(C.nzval))

@time Gs = C64 * transpose(C64)
C64 = nothing; GC.gc()
@time G  = Matrix{Float64}(Gs)
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

G = nothing
F = nothing
GC.gc()

row_basis_idx_sorted = sort(row_basis_idx)
@time C_basis = C[row_basis_idx_sorted, :]


@time MatrixMarket.mmwrite(outPath, C_basis)
