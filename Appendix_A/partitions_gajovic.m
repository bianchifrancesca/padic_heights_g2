/* Code by Stevan Gajović to verify [Bia23, Lemma A.3].

The main function is PrintAllAdmissiblePartitions(i)
which prints all the partitions of {1,..,i} into 4 subsets
S_1, S_2, S_3, S_4, each satisfying the conditions (i) and (ii)
in the proof of loc. cit. 

In particular,
> PrintAllAdmissiblePartitions(41);
TOTAL NUMBER 0
true

REFERENCES:
- [Bia23] F. Bianchi, "p-Adic sigma functions and heights on Jacobians of
  genus 2 curves", 2023.
*/

function Conditions(L)
	if IsEmpty(L) then
		return {0};
	end if;
	T1 := { s : s in L };
	T2 := { s1+s2 : s1, s2 in L };
	T3 := { s1+s2+s3 : s1, s2, s3 in L };
	T := ((T1 join T2) join T3);
	s:=L[#L];
	if (s-1 in L) and (s-2 in L) then
		T := T join {s+1};
	end if;
	return T;
end function;

function AllAdmissiblePartitions(i)
	if i eq 4 then
		b := [];
		b[1] := [1, 2, 3, 1];
		b[2] := [1, 2, 3, 3];
		b[3] := [1, 2, 3, 4];
		b[4] := [1, 2, 2, 1];
		b[5] := [1, 2, 2, 3];		
		return b;
	end if;
	b := AllAdmissiblePartitions(i-1);
	c := [];
	d := 1;
	for j in [1..(#b)] do
		S := [];
		S[1] := [];
		S[2] := [];
		S[3] := [];
		S[4] := [];
		for k in [1..(i-1)] do
			S[b[j][k]] := Append(S[b[j][k]], k);
		end for;
		for l in [1..4] do
			if (i notin Conditions(S[l])) then
				c[d] := b[j];
				c[d][i] := l;
				d := d+1;
			end if;
		end for;
	end for;
	return c;
end function;

function PrintAllAdmissiblePartitions(i)
	b := AllAdmissiblePartitions(i);
	for j in [1..(#b)] do
		print "ONE SOLUTION";
		S := [];
		S[1] := [];
		S[2] := [];
		S[3] := [];
		S[4] := [];
		for k in [1..i] do
			S[b[j][k]] := Append(S[b[j][k]], k);
		end for;
		for l in [1..4] do
			print S[l];
		end for;
	end for;
	print "TOTAL NUMBER", #b;
	return true;
end function; 
