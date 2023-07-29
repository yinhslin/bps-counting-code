LoadPackage( "ctbllib" );;
SnChar := function(n, NN)
	local ct, irr, cp, part, N, short, sq, ans;
	ct := CharacterTable("Symmetric", n);;
	irr := Irr(ct);;
	cp := ClassParameters(ct);;
	part := List(cp, x -> x[2]);;
	for N in [1..NN] do
		short := Filtered([1..Length(cp)], x->Length(cp[x][2]) <= N);;
		sq := Sum(short, x -> irr[x] * irr[x]);;
		ans := List([1..Length(part)], x -> [part[x], sq[x]]);;
		ans := String(ans);;
		ans := ReplacedString(ans, "[", "{");;
		ans := ReplacedString(ans, "]", "}");;
		PrintTo(JoinStringsWithSeparator(["~/bps/index/sn/", n, "_", N, ".m"], ""), ans);;
	od;
end;;
for n in [46..50] do
	SnChar(n, 10);;
od;
