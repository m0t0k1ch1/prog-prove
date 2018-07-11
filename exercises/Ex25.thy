theory Ex25
imports Main
begin

fun sum_upto :: "nat \<Rightarrow> nat" where
"sum_upto 0 = 0" |
"sum_upto (Suc x) = (sum_upto x) + (Suc x)"

lemma [simp]: "sum_upto x = x * (x + 1) div 2"
apply(induction x)
apply(auto)
done

end