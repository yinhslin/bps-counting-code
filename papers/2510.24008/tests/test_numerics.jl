using Test, LinearAlgebra, SparseArrays, MAT, MatrixMarket
project = normpath(joinpath(@__DIR__, "..", "julia"))
qr_script = joinpath(project,"qrC.jl")
dot_script = joinpath(project,"dotqrC.jl")
@testset "Gram/QR transport" begin
    mktempdir() do dir
        A=sparse([1.0 2 0; 2 4 0; 0 0 3])
        input=joinpath(dir,"input with spaces.mat");output=joinpath(dir,"indices.txt")
        matwrite(input,Dict("A"=>A))
        run(`$(Base.julia_cmd()) --startup-file=no --project=$project $qr_script Float64 1e-7 $input $output`)
        inds=parse.(Int,readlines(output))
        @test length(inds)==2
        @test rank(Matrix(A[inds,:]))==rank(Matrix(A))==2
        Z=spzeros(3,4);matwrite(input,Dict("A"=>Z))
        run(`$(Base.julia_cmd()) --startup-file=no --project=$project $qr_script Float64 1e-7 $input $output`)
        @test isempty(readlines(output))
        B=sparse([1.0 0;0 1;0 2]);right=joinpath(dir,"right.mat");out=joinpath(dir,"basis.mtx")
        matwrite(input,Dict("A"=>A));matwrite(right,Dict("B"=>B))
        run(`$(Base.julia_cmd()) --startup-file=no --project=$project $dot_script Float64 1e-7 $input $right $out`)
        basis=Matrix(MatrixMarket.mmread(out));product=Matrix(A*B)
        @test size(basis,1)==2
        @test rank(basis)==2
        @test rank(vcat(product,basis))==2
    end
end
