theory RequirementLemmas
  imports VCTheoryLemmas  "HOL-Eisbach.Eisbach" "HOL-Eisbach.Eisbach_Tools"
begin

definition always_imp where "always_imp s A A' \<equiv> \<forall> s1. toEnvP s1 \<and> s1 \<le> s \<and> A s1 \<longrightarrow> A' s1"

named_theorems patternintro
named_theorems invsaving
named_theorems inv_req
named_theorems add_rules
named_theorems pastinv
named_theorems einvs
named_theorems elims

lemma always_disj_rule[patternintro]: "toEnvP s \<Longrightarrow> always_imp s A A' \<and> always_imp s B B' \<Longrightarrow>
always_imp s (\<lambda> s1. A s1 \<or> B s1) (\<lambda> s1. A' s1 \<or> B' s1)"
  apply(unfold always_imp_def)
  by auto

lemma always_conj_rule[patternintro]: "toEnvP s \<Longrightarrow> always_imp s A A' \<and> always_imp s B B' \<Longrightarrow>
always_imp s (\<lambda> s1. A s1 \<and> B s1) (\<lambda> s1. A' s1 \<and> B' s1)"
  apply(unfold always_imp_def)
  by auto

lemma always_imp_refl: " always_imp s A A"
  apply(unfold always_imp_def)
  by auto

method prove declares add_rules einvs =
(*formula without requirement and extra invariant patterns*)
assumption |
(*conjunction*)
match conclusion in "?P \<and> ?Q" \<Rightarrow>
\<open>erule conjE;
match premises in e[thin]: _ (cut) \<Rightarrow>
\<open>match premises in p1[thin]: _ (cut) \<Rightarrow> 
\<open>match premises in p2[thin]: _ (cut) \<Rightarrow> \<open>rule conjI,(insert e p1)[1],prove,(insert e p2)[1],prove\<close>\<close>\<close>\<close> |
(*disjunction*)
match conclusion in "?P \<or> ?Q" \<Rightarrow> \<open>erule disjE,rule disjI1,prove,rule disjI2,prove\<close> |
(*implication*)
match conclusion in "?b \<longrightarrow> ?P" \<Rightarrow>
\<open>rule impI,rule impE,assumption,
match premises in e[thin]: _ (cut) \<Rightarrow>
\<open>match premises in b[thin]: _ (cut) \<Rightarrow>
\<open>match premises in p[thin]: _ (cut) \<Rightarrow>
 \<open>(insert e p)[1];prove\<close>\<close>\<close>\<close> |
(*\<forall> s1. e(s1) \<and> s1 \<le> s \<and> A(s1) \<longrightarrow> A'(s1)*)
match conclusion in "always_imp ?s ?A ?A" \<Rightarrow> \<open>rule always_imp_refl\<close> |
(*pattern*)
rule patternintro add_rules,(assumption | simp),prove |
(*past extra invariant pattern*)
rotate_tac;match premises in p[thin]: b (cut) for b \<Rightarrow> \<open>match einvs in i: "b \<longrightarrow> ?P" \<Rightarrow> \<open>rule mp[OF i p]\<close>\<close>

method proveOuter declares add_rules einvs =
(*conjunction*)
match conclusion in "?P \<and> ?Q" \<Rightarrow>
\<open>erule conjE;erule conjE;
match premises in e[thin]: _ (cut) \<Rightarrow>
\<open>match premises in i1[thin]: _ (cut) \<Rightarrow>
\<open>match premises in i2[thin, einvs]: _ (cut) \<Rightarrow>
\<open>match premises in p1[thin]: _ (cut) \<Rightarrow>
\<open>match premises in p2[thin]: _ (cut) \<Rightarrow>
\<open>rule conjI,(insert e i1 p1)[1],proveOuter,(insert e i2 p2)[1],proveOuter\<close>\<close>\<close>\<close>\<close>\<close> |
(*disjunction*)
match conclusion in "?P \<or> ?Q" \<Rightarrow>
\<open>erule conjE;
match premises in p1[thin]: _ (cut) \<Rightarrow>
\<open>match premises in p2[thin]: _ (cut) \<Rightarrow>
\<open>match premises in p3[thin]: _ (cut) \<Rightarrow>
\<open>match premises in p4[thin]: _ (cut) \<Rightarrow>
\<open>(insert p1 p2)[1],erule disjE,(insert p3)[1],rule disjI1,proveOuter,(insert p4)[1],rule disjI2,proveOuter\<close>\<close>\<close>\<close>\<close> |
(*implication: additional conjunct*)
match conclusion in "?b \<longrightarrow> ?P" \<Rightarrow>
\<open>match premises in e[thin]: _ (cut) \<Rightarrow>
\<open>match premises in i[thin]: _ (cut) \<Rightarrow>
\<open>match premises in p[thin]: _ (cut) \<Rightarrow>
\<open>(insert e p)[1],rule impI,erule impE,assumption,
match premises in e[thin]: _ (cut) \<Rightarrow>
\<open>match premises in b[thin]: _ (cut) \<Rightarrow>
\<open>match premises in p[thin]: _ (cut) \<Rightarrow>
\<open>(insert e p)[1],rule pastinv,assumption,prove\<close>\<close>\<close>\<close>\<close>\<close>\<close> |
(*pattern*)
match premises in p1[thin]: _ (cut) \<Rightarrow>
\<open>match premises in p2[thin]: _ (cut) \<Rightarrow>
\<open>match premises in p3[thin]: _ (cut) \<Rightarrow>
\<open>(insert p1 p2)[1];(simp only: conj_assoc)?;
(erule conjE;rotate_tac -1;match premises in ac[thin]: _ (cut) \<Rightarrow> \<open>succeed\<close>)?;
erule elims,assumption,(insert p3)[1],prove\<close>\<close>\<close>

end