theory Chapter3
imports Main
begin

type_synonym vname = string
type_synonym val = int
type_synonym state = "vname \<Rightarrow> val"

datatype aexp = N int | V vname | Plus aexp aexp

fun aval :: "aexp \<Rightarrow> state \<Rightarrow> val" where
  "aval (N n) s = n" |
  "aval (V v) s = s v" |
  "aval (Plus l r) s = aval l s + aval r s"
value "aval (Plus (N 3) (V ''x'')) ((\<lambda>x. 0) (''x'' := 7))"
value "aval (Plus (V ''y'') (V ''x'')) ((\<lambda>x. 0) (''x'' := 7, ''y'' := 30))"

fun asimp_const :: "aexp \<Rightarrow> aexp" where
  "asimp_const (N n) = N n" |
  "asimp_const (V v) = V v" |
  "asimp_const (Plus l r) = (case (asimp_const l, asimp_const r) of
    (N a, N b) \<Rightarrow> N (a + b) |
    (a, b) \<Rightarrow> Plus a b)"
value "aval (Plus (N 40) (N 2)) (\<lambda>x. 0)"

lemma "aval (asimp_const e) s = aval e s"
  apply (induction e)
  apply (auto split: aexp.split)
  done

fun plus :: "aexp \<Rightarrow> aexp \<Rightarrow> aexp" where
  "plus (N a) (N b) = N (a + b)" |
  "plus (N a) r = (if a = 0 then r else Plus (N a) r)" |
  "plus l (N b) = (if b = 0 then l else Plus l (N b))" |
  "plus l r = Plus l r"

lemma aval_plus [simp]: "aval (plus l r) s = aval l s + aval r s"
  apply (induction l rule: plus.induct)
  apply auto
  done

fun asimp :: "aexp \<Rightarrow> aexp" where
  "asimp (N n) = N n" |
  "asimp (V v) = V v" |
  "asimp (Plus l r) = plus (asimp l) (asimp r)"

lemma "aval (asimp e) s = aval e s"
  apply (induction e)
  apply (auto split: aexp.split)
  done

(* Ex. 3.1 *)
(* Determines if the specified expression has no foldable expressions. *)
fun optimal :: "aexp \<Rightarrow> bool" where
  "optimal (N n) = True" |
  "optimal (V v) = True" |
  "optimal (Plus (N a) (N b)) = False" |
  "optimal (Plus l r) = ((optimal l) & (optimal r))"
value "optimal (N 4) = True"
value "optimal (Plus (N 4) (V ''x'')) = True"
value "optimal (Plus (N 4) (N 3)) = False"

lemma "optimal (asimp_const e) = True"
  apply (induction e)
  apply (auto split: aexp.split)
  done

(* Ex. 3.2 *)
(* Returns the sum of all numerals in the specified expression. *)
fun sumN :: "aexp \<Rightarrow> int" where
  "sumN (N n) = n" |
  "sumN (V v) = 0" |
  "sumN (Plus l r) = (sumN l) + (sumN r)"
value "sumN (Plus (N (-1)) (V [])) = -1"

(* Returns the specified expression with numerals replaced by 0. *)
fun zeroN :: "aexp \<Rightarrow> aexp" where
  "zeroN (N n) = N 0" |
  "zeroN (V v) = V v" |
  "zeroN (Plus l r) = Plus (zeroN l) (zeroN r)"
value "zeroN (Plus (N (- 1)) (V [])) = zeroN (Plus (N 0) (V []))"

(* Returns 'sumN e + zeroN e' *)
fun sepN :: "aexp \<Rightarrow> aexp" where 
  "sepN e = Plus (N (sumN e)) (zeroN e)"
value "sepN (Plus (N (- 1)) (V []))"

lemma aval_sepN: "aval (sepN e) s = aval e s"
  apply (induction e)
  apply auto
  done

(* Simplifies the specified expression. *)
fun full_asimp :: "aexp \<Rightarrow> aexp" where
  "full_asimp e = asimp (sepN e)"
value "full_asimp (Plus (Plus ((Plus (V ''x'') (N 7))) (V ''x'')) (N 5))"

lemma aval_full_asimp: "aval (full_asimp e) s = aval e s"
  apply (induction e)
  apply (auto split: aexp.split)
  done

(* Ex. 3.3 *)
(* Substitutes the variable in the expression by the specified expression. *)
fun subst :: "vname \<Rightarrow> aexp \<Rightarrow> aexp \<Rightarrow> aexp" where
  "subst x a (N n) = N n" |
  "subst x a (V v) = (if x = v then a else (V v))" |
  "subst x a (Plus l r) = Plus (subst x a l) (subst x a r)"

lemma subst_lemma: "aval (subst x a b) s = aval b (s(x := aval a s))"
  apply (induction b)
  apply (auto split: aexp.split)
  done

lemma "aval a1 s = aval a2 s \<Longrightarrow> aval (subst x a1 b) s = aval (subst x a2 b) s"
  apply (induction b)
  apply auto
  done

(* Ex. 3.4 *)
(* `aexp` equipped with times operation. *)
datatype aexpt = N int | V vname | Plus aexpt aexpt | Times aexpt aexpt

(* Evaluates the specified `aexpt`-expression. *)
fun avalt :: "aexpt \<Rightarrow> state \<Rightarrow> val" where
  "avalt (N n) s = n" |
  "avalt (V x) s = s x" |
  "avalt (Plus l r) s = avalt l s + avalt r s" |
  "avalt (Times l r) s = avalt l s * avalt r s"
value "avalt (Times (N 3) (V ''x'')) ((\<lambda>x.0) (''x'':=7))"
value "avalt (Times (V ''y'') (V ''x'')) ((\<lambda>x.0)(''x'':=7, ''y'':=30))"

(* Folds numeral constants in Plus-expression. *)
fun plust :: "aexpt \<Rightarrow> aexpt \<Rightarrow> aexpt" where
  "plust (N l) (N r) = N (l + r)" |
  "plust (N l) r = (if l = 0 then r else Plus (N l) r)" |
  "plust l (N r) = (if r = 0 then l else Plus l (N r))" |
  "plust l r = Plus l r"

(* Folds numeral constants in Times-expression. *)
fun timest :: "aexpt \<Rightarrow> aexpt \<Rightarrow> aexpt" where
  "timest (N l) (N r) = N (l * r)" |
  "timest (N l) r = (if l = 0 then (N 0) else if l = 1 then r else Times (N l) r)" |
  "timest l (N r) = (if r = 0 then (N 0) else if r = 1 then l else Times l (N r))" |
  "timest l r = Times l r"

(* Simplifies the `aexpt`-expression. *)
fun asimpt :: "aexpt \<Rightarrow> aexpt" where
  "asimpt (N n) = N n" |
  "asimpt (V x) = V x" |
  "asimpt (Plus l r) = plust (asimpt l) (asimpt r)" | 
  "asimpt (Times l r) = timest (asimpt l) (asimpt r)"

lemma avalt_plus [simp]: "avalt (plust l r) s = avalt l s + avalt r s"
  apply (induction rule: plust.induct)
  apply auto
  done

lemma avalt_times [simp]: "avalt (timest l r) s = avalt l s * avalt r s"
  apply (induction rule: timest.induct)
  apply auto
  done

lemma "avalt (asimpt a) s = avalt a s"
  apply (induction a)
  apply auto
  done

(* Ex. 3.5 *)
(* Expression equipped with post-increment and division operations. *)
datatype aexp2 = N int | V vname | Incr vname 
  | Plus aexp2 aexp2 | Times aexp2 aexp2 | Div aexp2 aexp2

(* Evaluates the specified `aexp2`-expression. *)
fun aval2 :: "aexp2 \<Rightarrow> state \<Rightarrow> (val \<times> state) option" where
  "aval2 (N n) s = Some (n, s)" |
  "aval2 (V x) s = Some (s x, s)" |
  "aval2 (Incr x) s = Some (s x, s(x := 1 + s x))" |
  "aval2 (Plus l r) s = (case (aval2 l s) of
    None \<Rightarrow> None |
    Some a \<Rightarrow> (case (aval2 r (snd a)) of
      None \<Rightarrow> None |
      Some b \<Rightarrow> Some ((fst a + fst b), snd b)))" |
  "aval2 (Times l r) s = (case (aval2 l s) of
    None \<Rightarrow> None |
    Some a \<Rightarrow> (case (aval2 r (snd a)) of
      None \<Rightarrow> None |
      Some b \<Rightarrow> Some ((fst a + fst b), snd b)))" |
  "aval2 (Div l r) s = (case (aval2 l s) of
    None \<Rightarrow> None |
    Some a \<Rightarrow> (case (aval2 r (snd a)) of
      None \<Rightarrow> None |
      Some b \<Rightarrow> if (fst b) = 0 then None else Some ((fst a div fst b), snd b)))"
value "aval2 (Incr ''a'') ((\<lambda>x. 0) (''a'':=1))"
value "aval2 (Plus (Incr ''a'') (V ''a'')) ((\<lambda>x.0) (''a'':=1))"
value "aval2 (Div (N 4) (N 2)) (\<lambda>x. 0)"
value "aval2 (Div (N 4) (V ''x'')) ((\<lambda>x. 0) (''x'':=0)) = None"




  



end