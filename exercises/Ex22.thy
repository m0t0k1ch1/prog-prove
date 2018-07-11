theory Ex22
imports Main
begin

fun add :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"add 0 y = y" |
"add (Suc x) y = Suc (add x y)"

lemma [simp]: "add x 0 = x"
apply(induction x)
apply(auto)
done

lemma [simp]: "add x (Suc y) = Suc (add x y)"
apply(induction x)
apply(auto)
done

(* add is associative *)
lemma [simp]: "add (add x y) z = add x (add y z)"
apply(induction x)
apply(auto)
done

(* add is commutative *)
lemma [simp]: "add x y = add y x"
apply(induction x)
apply(auto)
done

fun double :: "nat \<Rightarrow> nat" where
"double 0 = 0" |
"double (Suc x) = Suc (Suc (double x))"

lemma [simp]: "double x = add x x"
apply(induction x)
apply(auto)
done

end