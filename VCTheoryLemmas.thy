theory VCTheoryLemmas
  imports VCTheory
begin

lemma substate_refl[simp]: "substate s s"
  apply(cases s)
           apply(auto)
  done

lemma substate_trans:
"substate s1 s2 \<Longrightarrow> substate s2 s3 \<Longrightarrow> substate s1 s3"
  apply((induction s3); (simp split: if_splits))
  done

lemma substate_antisym:
 "substate s1 s2 \<Longrightarrow> substate s2 s1 \<Longrightarrow> s1=s2"
  apply((induction s2 arbitrary: s1); (metis substate.simps substate_refl substate_trans))
  done

lemma substate_linear: 
"substate s1 s \<and> substate s2 s \<Longrightarrow>
 substate s1 s2 \<or> substate s2 s1"
  apply((induction s);(simp split: if_splits))
  done

lemma toEnvNum_id[simp]: "toEnvNum s s = 0"
  apply(cases s)
         apply(auto)
  done

lemma substate_toEnvNum_id:
"substate s1 s2 \<and> toEnvNum s1 s2 = 0 \<and> toEnvP s1 \<and>
toEnvP s2 \<Longrightarrow> s1=s2"
  apply((cases s2);(simp split: if_splits))
  done

lemma toEnvNum3: "substate s1 s2 \<and> substate s2 s3
 \<Longrightarrow> toEnvNum s1 s3 = toEnvNum s1 s2 + toEnvNum s2 s3"
  apply((induction s3); (simp split: if_splits); (meson substate.simps substate_antisym))
  done

lemma external_ltime[simp]: "toEnvP s \<Longrightarrow> ltime s p > 0"
  apply(cases s)
  by auto

lemma toEnvNum_eq_imp_eq2: "substate s1 s3 \<and> substate s2 s3 \<and> toEnvP s1 \<and> toEnvP s2 \<and> toEnvNum s1 s3 = toEnvNum s2 s3 \<Longrightarrow>
s1=s2"
  using substate_linear toEnvNum3 substate_toEnvNum_id
  by (metis add_cancel_left_left)

lemma  substate_noteq_imp_substate_of_pred: "toEnvP s1 \<and> toEnvP s0 \<and> toEnvP s \<and> substate s0 s \<and> toEnvNum s0 s = 1 \<and> substate s1 s \<and>  s1 \<noteq> s \<longrightarrow> substate s1 s0"
  by (metis (full_types) One_nat_def add_is_1 substate_linear substate_toEnvNum_id toEnvNum3) 

lemma toEnvP_imp_toEnvNum_geq_1: "toEnvP s \<Longrightarrow> toEnvNum emptyState s \<ge> 1"
  apply(cases s)
           apply auto
  done

instantiation state :: order
begin

fun less_eq_state where "s1 \<le> s2 = substate s1 s2"
fun less_state where "s1 < s2 = (substate s1 s2 \<and> s1 \<noteq> s2)"

instance
  apply intro_classes
  apply simp
  using substate_antisym apply blast
    apply simp
   apply simp
  using substate_trans apply blast
  apply simp
  by (simp add: substate_antisym)

end

end
