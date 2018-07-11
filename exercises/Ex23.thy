theory Ex23
imports Main
begin

fun count :: "'a \<Rightarrow> 'a list \<Rightarrow> nat" where
"count x Nil = 0" |
"count x (Cons y ys) = (if (x = y) then Suc (count x ys) else count x ys)"

lemma [simp]: "count x xs \<le> length xs"
apply(induction xs)
apply(auto)
done

end