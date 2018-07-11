theory Ex24
imports Main
begin

fun snoc :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a list" where
"snoc Nil y = Cons y Nil" |
"snoc (Cons x xs) y = Cons x (snoc xs y)"

fun reverse :: "'a list \<Rightarrow> 'a list" where
"reverse Nil = Nil" |
"reverse (Cons x xs) = snoc (reverse xs) x"

lemma [simp]: "reverse (snoc xs y) = Cons y (reverse xs)"
apply(induction xs)
apply(auto)
done

lemma [simp]: "reverse (reverse xs) = xs"
apply(induction xs)
apply(auto)
done

end