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

lemma subst_lemma [simp]: "aval (subst x a b) s = aval b (s(x := aval a s))"
  apply (induction b)
  apply (auto split: aexp.split)
  done

lemma "aval a1 s = aval a2 s \<Longrightarrow> aval (subst x a1 b) s = aval (subst x a2 b) s"
  apply (induction b)
  apply auto
  done

(* Ex. 3.4 *)
(* `aexp` equipped with times operation. *)
datatype aexpt = Nt int | Vt vname | Plust aexpt aexpt | Timest aexpt aexpt

(* Evaluates the specified `aexpt`-expression. *)
fun avalt :: "aexpt \<Rightarrow> state \<Rightarrow> val" where
  "avalt (Nt n) s = n" |
  "avalt (Vt x) s = s x" |
  "avalt (Plust l r) s = avalt l s + avalt r s" |
  "avalt (Timest l r) s = avalt l s * avalt r s"
value "avalt (Timest (Nt 3) (Vt ''x'')) ((\<lambda>x.0) (''x'':=7))"
value "avalt (Timest (Vt ''y'') (Vt ''x'')) ((\<lambda>x.0)(''x'':=7, ''y'':=30))"

(* Folds numeral constants in Plus-expression. *)
fun plust :: "aexpt \<Rightarrow> aexpt \<Rightarrow> aexpt" where
  "plust (Nt l) (Nt r) = Nt (l + r)" |
  "plust (Nt l) r = (if l = 0 then r else Plust (Nt l) r)" |
  "plust l (Nt r) = (if r = 0 then l else Plust l (Nt r))" |
  "plust l r = Plust l r"

(* Folds numeral constants in Times-expression. *)
fun timest :: "aexpt \<Rightarrow> aexpt \<Rightarrow> aexpt" where
  "timest (Nt l) (Nt r) = Nt (l * r)" |
  "timest (Nt l) r = (if l = 0 then (Nt 0) else if l = 1 then r else Timest (Nt l) r)" |
  "timest l (Nt r) = (if r = 0 then (Nt 0) else if r = 1 then l else Timest l (Nt r))" |
  "timest l r = Timest l r"

(* Simplifies the `aexpt`-expression. *)
fun asimpt :: "aexpt \<Rightarrow> aexpt" where
  "asimpt (Nt n) = Nt n" |
  "asimpt (Vt x) = Vt x" |
  "asimpt (Plust l r) = plust (asimpt l) (asimpt r)" | 
  "asimpt (Timest l r) = timest (asimpt l) (asimpt r)"

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
datatype aexp2 = N2 int | V2 vname | Incr2 vname 
  | Plus2 aexp2 aexp2 | Times2 aexp2 aexp2 | Div2 aexp2 aexp2

(* Evaluates the specified `aexp2`-expression. *)
fun aval2 :: "aexp2 \<Rightarrow> state \<Rightarrow> (val \<times> state) option" where
  "aval2 (N2 n) s = Some (n, s)" |
  "aval2 (V2 x) s = Some (s x, s)" |
  "aval2 (Incr2 x) s = Some (s x, s(x := 1 + s x))" |
  "aval2 (Plus2 l r) s = (case (aval2 l s) of
    None \<Rightarrow> None |
    Some a \<Rightarrow> (case (aval2 r (snd a)) of
      None \<Rightarrow> None |
      Some b \<Rightarrow> Some ((fst a + fst b), snd b)))" |
  "aval2 (Times2 l r) s = (case (aval2 l s) of
    None \<Rightarrow> None |
    Some a \<Rightarrow> (case (aval2 r (snd a)) of
      None \<Rightarrow> None |
      Some b \<Rightarrow> Some ((fst a + fst b), snd b)))" |
  "aval2 (Div2 l r) s = (case (aval2 l s) of
    None \<Rightarrow> None |
    Some a \<Rightarrow> (case (aval2 r (snd a)) of
      None \<Rightarrow> None |
      Some b \<Rightarrow> if (fst b) = 0 then None else Some ((fst a div fst b), snd b)))"
value "aval2 (Incr2 ''a'') ((\<lambda>x. 0) (''a'':=1))"
value "aval2 (Plus2 (Incr2 ''a'') (V2 ''a'')) ((\<lambda>x.0) (''a'':=1))"
value "aval2 (Div2 (N2 4) (N2 2)) (\<lambda>x. 0)"
value "aval2 (Div2 (N2 4) (V2 ''x'')) ((\<lambda>x. 0) (''x'':=0)) = None"

(* Ex. 3.6 *)
(* let x = e_1 in e_2 *)
datatype lexp = Nl int | Vl vname | Plusl lexp lexp | Let vname lexp lexp

(* Evaluates the specified `lexp`-expression. *)
fun lval :: "lexp \<Rightarrow> state \<Rightarrow> int" where
  "lval (Nl n) s = n" |
  "lval (Vl x) s = s x" |
  "lval (Plusl l r) s = lval l s + lval r s" |
  "lval (Let x a b) s = lval b (s(x:=lval a s))"
value "lval (Let ''x'' (Nl 19) (Plusl (Nl 1) (Vl ''x''))) (\<lambda>x. 0)"

(* Inlines `lexp` into `aexp`. *)
fun inline :: "lexp \<Rightarrow> aexp" where
  "inline (Nl n) = (aexp.N n)" |
  "inline (Vl x) = (aexp.V x)" |
  "inline (Plusl l r) = aexp.Plus (inline l) (inline r)" |
  "inline (Let x a b) = subst x (inline a) (inline b)"

lemma "aval (inline a) s = lval a s"
  apply (induction a arbitrary:s)
  apply (auto)
  done

(* 3.2 Boolean Expressions *)
(* Defines boolean expression. *)
datatype bexp = Bc bool | Not bexp | And bexp bexp | Less aexp aexp

(* Evaluates boolean expression. *)
fun bval :: "bexp \<Rightarrow> state \<Rightarrow> bool" where
  "bval (Bc v) s = v" |
  "bval (Not a) s = (\<not> bval a s)" |
  "bval (And a b) s = (bval a s \<and> bval b s)" |
  "bval (Less a b) s = (aval a s < aval b s)"

fun not :: "bexp \<Rightarrow> bexp" where
  "not (Bc True) = Bc False" |
  "not (Bc False) = Bc True" |
  "not a = Not a"

fun "and" :: "bexp \<Rightarrow> bexp \<Rightarrow> bexp" where
  "and (Bc True) b = b" |
  "and a (Bc True) = a" |
  "and (Bc False) b = Bc False" |
  "and a (Bc False) = Bc False" |
  "and a b = And a b"

fun less :: "aexp \<Rightarrow> aexp \<Rightarrow> bexp" where
  "less (N a) (N b) = Bc (a < b)" |
  "less a b = Less a b"

fun bsimp :: "bexp \<Rightarrow> bexp" where
  "bsimp (Bc v) = Bc v" |
  "bsimp (Not b) = not (bsimp b)" |
  "bsimp (And a b) = and (bsimp a) (bsimp b)" |
  "bsimp (Less a b) = less (asimp a) (asimp b)"

(* Ex. 3.7 *)
fun Eq :: "aexp \<Rightarrow> aexp \<Rightarrow> bexp" where
  "Eq a b = And (Not (Less a b)) (Not (Less b a))"
value "bval (Eq (N 4) (Plus (N 1) (N 3))) (\<lambda>x. 0)"

fun Le :: "aexp \<Rightarrow> aexp \<Rightarrow> bexp" where
  "Le a b = Not (Less b a)"

lemma "bval (Eq a b) s = (aval a s = aval b s)"
  apply (induction a)
  apply auto
  done

lemma "bval (Le a b) s = (aval a s \<le> aval b s)"
  apply (induction a)
  apply auto
  done

(* Ex. 3.8 *)
datatype ifexp = Bc2 bool | If ifexp ifexp ifexp | Less2 aexp aexp

fun ifval :: "ifexp \<Rightarrow> state \<Rightarrow> bool" where
  "ifval (Bc2 v) s = v" |
  "ifval (If a b c) s = (if (ifval a s) then (ifval b s) else (ifval c s))" |
  "ifval (Less2 a b) s = (aval a s < aval b s)"

fun b2ifexp :: "bexp \<Rightarrow> ifexp" where
  "b2ifexp (Bc v) = Bc2 v" |
  "b2ifexp (Not b) = If (b2ifexp b) (Bc2 False) (Bc2 True)" |
  "b2ifexp (And a b) = If (b2ifexp a) (b2ifexp b) (Bc2 False)" |
  "b2ifexp (Less a b) = (Less2 a b)"

fun nand :: "bexp \<Rightarrow> bexp \<Rightarrow> bexp" where
  "nand a b = Not (And a b)"

fun or :: "bexp \<Rightarrow> bexp \<Rightarrow> bexp" where
  "or a b = nand (Not a) (Not b)"

fun mux :: "bexp \<Rightarrow> bexp \<Rightarrow> bexp \<Rightarrow> bexp" where
  "mux a b c = or (And a b) (And (Not a) c)"

fun if2bexp :: "ifexp \<Rightarrow> bexp" where
  "if2bexp (Bc2 v) = Bc v" |
  "if2bexp (Less2 a b) = Less a b" |
  "if2bexp (If a b c) = (mux (if2bexp a) (if2bexp b) (if2bexp c))"

lemma "ifval (b2ifexp a) s = bval a s"
  apply (induction a)
  apply auto
  done

lemma "bval (if2bexp a) s = ifval a s"
  apply (induction a)
  apply (auto)
  done

(* Ex. 3.9 *)
(* Purely boolean expression. *)
datatype pbexp = VAR vname | NOT pbexp | AND pbexp pbexp | OR pbexp pbexp

fun pbval :: "pbexp \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> bool" where
  "pbval (VAR x) s = s x" |
  "pbval (NOT a) s = (\<not>pbval a s)" |
  "pbval (AND l r) s = (pbval l s \<and> pbval r s)" |
  "pbval (OR l r) s = (pbval l s \<or> pbval r s)"

fun is_nnf :: "pbexp \<Rightarrow> bool" where
  "is_nnf (VAR x) = True" |
  "is_nnf (NOT (VAR x)) = True" |
  "is_nnf (NOT a) = False" |
  "is_nnf (AND l r) = (is_nnf l \<and> is_nnf r)" |
  "is_nnf (OR l r) = (is_nnf l \<and> is_nnf r)"

fun nnf :: "pbexp \<Rightarrow> pbexp" where
  "nnf (VAR x) = (VAR x)" |
  "nnf (NOT (VAR x)) = NOT (VAR x)" |
  "nnf (NOT (NOT a)) = nnf a" |
  "nnf (NOT (AND l r)) = OR (nnf (NOT l)) (nnf (NOT r))" |
  "nnf (NOT (OR l r)) = AND (nnf (NOT l)) (nnf (NOT r))" |
  "nnf (AND l r) = AND (nnf l) (nnf r)" |
  "nnf (OR l r) = OR (nnf l) (nnf r)"

lemma not_nnf [simp]: "pbval (nnf (NOT a)) s = (\<not>pbval (nnf a) s)"
  apply (induction a)
  apply auto
  done

lemma "pbval (nnf a) s = pbval a s" 
  apply (induction a)
  apply auto
  done

lemma "is_nnf (nnf a)"
  apply (induction a rule:nnf.induct)
  apply auto
  done

fun dnf_and :: "pbexp \<Rightarrow> pbexp \<Rightarrow> pbexp" where
  "dnf_and l (OR l2 r2) = OR (dnf_and l l2) (dnf_and l r2)" |
  "dnf_and (OR l2 r2) r = OR (dnf_and l2 r) (dnf_and r2 r)" |
  "dnf_and l r = AND l r"

lemma pbval_dnf_and [simp]: "pbval (dnf_and l r) s = pbval (AND l r) s"
  apply (induction l r rule: dnf_and.induct)
  apply auto
  done

fun dnf_of_nnf :: "pbexp \<Rightarrow> pbexp" where
  "dnf_of_nnf (VAR x) = VAR x" |
  (* See NNF. *)
  "dnf_of_nnf (NOT a) = NOT a" |
  "dnf_of_nnf (OR l r) = OR (dnf_of_nnf l) (dnf_of_nnf r)" |
  "dnf_of_nnf (AND l r) = dnf_and (dnf_of_nnf l) (dnf_of_nnf r)"

lemma "pbval (dnf_of_nnf a) s = pbval a s" 
  apply (induction a)
  apply auto
  done

fun is_dnf_sub :: "pbexp \<Rightarrow> bool" where
  "is_dnf_sub (VAR x) = True" |
  "is_dnf_sub (NOT a) = True" |
  "is_dnf_sub (AND l r) = (is_dnf_sub l \<and> is_dnf_sub r)" |
  "is_dnf_sub (OR l r) = False"

fun is_dnf :: "pbexp \<Rightarrow> bool" where
  "is_dnf (VAR x) = True" |
  (* See NNF. *)
  "is_dnf (NOT a) = True" |
  "is_dnf (AND l r) = (is_dnf_sub l \<and> is_dnf_sub r)" |
  "is_dnf (OR l r) = (is_dnf l \<and> is_dnf r)"
 
lemma is_dnf_and [simp]: "is_dnf l \<Longrightarrow> is_dnf r \<Longrightarrow> is_dnf (dnf_and l r)" 
  apply (induction l r rule:dnf_and.induct)
  apply auto
  done

value "dnf_and (VAR []) (AND (VAR []) (OR (VAR []) (VAR [])))"

lemma "is_nnf a \<Longrightarrow> is_dnf (dnf_of_nnf a)"
  apply (induction a)
  apply (auto)
  done


end