theory EDTL_Low_Steady
  imports VCTheoryLemmas
begin

fun low_steady_time :: "state \<Rightarrow> (state \<Rightarrow> bool) \<Rightarrow> nat" where
"low_steady_time emptyState A = 0" |
"low_steady_time (toEnv s) A = (if \<not> A (toEnv s) then if prev (toEnv s) = emptyState \<or> A (prev (toEnv s)) then 0 else Suc (low_steady_time s A) else low_steady_time s A)" |
"low_steady_time (setVarBool s x u) A = low_steady_time s A" |
"low_steady_time (setVarInt s x u) A = low_steady_time s A" |
"low_steady_time (setVarReal s x u) A = low_steady_time s A" |
"low_steady_time (setVarArrayBool s x i u) A = low_steady_time s A" |
"low_steady_time (setVarArrayInt s x i u) A = low_steady_time s A" |
"low_steady_time (setVarArrayReal s x i u) A = low_steady_time s A" |
"low_steady_time (setPstate s p q) A = low_steady_time s A" |
"low_steady_time (reset s p) A = low_steady_time s A"

definition low_steady_upper_time_limit where "low_steady_upper_time_limit t A s s1 \<equiv>
\<not> A s1 \<and> 
  ((\<exists> s2. toEnvP s2 \<and> s2 \<le> s1 \<and> toEnvNum s2 s1 \<le> t + 1 \<and> A s2) \<or> toEnvNum emptyState s1 \<le> t + 1 \<and> (\<forall> s2. toEnvP s2 \<and> s2 \<le> s1 \<longrightarrow> \<not> A s2)) \<or>
A s1 \<and>
  (\<forall> s3. toEnvP s3 \<and> s3 \<le> s1 \<and> \<not> A s3 \<and> (\<forall> s4. toEnvP s4 \<and> s3 < s4 \<and> s4 \<le> s1 \<longrightarrow> A s4) \<longrightarrow> 
    ((\<exists> s2. toEnvP s2 \<and> s2 \<le> s3 \<and> toEnvNum s2 s3 \<le> t + 1 \<and> A s2) \<or> toEnvNum emptyState s3 \<le> t + 1 \<and> (\<forall> s2. toEnvP s2 \<and> s2 \<le> s3 \<longrightarrow> \<not> A s2)))"

definition low_steady_upper_time_limit_if_false where "low_steady_upper_time_limit_if_false t A s s1 \<equiv>
\<not> A s1 \<and> 
  ((\<exists> s2. toEnvP s2 \<and> s2 \<le> s1 \<and> toEnvNum s2 s1 \<le> t + 1 \<and> A s2) \<or> toEnvNum emptyState s1 \<le> t + 1 \<and> (\<forall> s2. toEnvP s2 \<and> s2 \<le> s1 \<longrightarrow> \<not> A s2))"

definition low_steady_upper_time_limit_if_true where "low_steady_upper_time_limit_if_true t A s s1 \<equiv>
A s1 \<and>
  (\<forall> s3. toEnvP s3 \<and> s3 \<le> s1 \<and> \<not> A s3 \<and> (\<forall> s4. toEnvP s4 \<and> s3 < s4 \<and> s4 \<le> s1 \<longrightarrow> A s4) \<longrightarrow> 
    ((\<exists> s2. toEnvP s2 \<and> s2 \<le> s3 \<and> toEnvNum s2 s3 \<le> t + 1 \<and> A s2) \<or> toEnvNum emptyState s3 \<le> t + 1 \<and> (\<forall> s2. toEnvP s2 \<and> s2 \<le> s3 \<longrightarrow> \<not> A s2)))"

definition low_steady_lower_time_limit where "low_steady_lower_time_limit t A s s1 \<equiv>
\<not> A s1 \<and> toEnvNum emptyState s1 \<ge> t+1 \<and> (\<forall> s2. toEnvP s2 \<and> s2 \<le> s1 \<and> toEnvNum s2 s1 \<le> t \<longrightarrow> \<not> A s2) \<or>
A s1 \<and> 
  (\<exists> s3. toEnvP s3 \<and> s3 \<le> s1 \<and> (\<forall> s4. toEnvP s4 \<and> s3 < s4 \<and> s4 \<le> s1 \<longrightarrow> A s4) \<and>
    toEnvNum emptyState s3 \<ge> t+1 \<and> (\<forall> s2. toEnvP s2 \<and> s2 \<le> s3 \<and> toEnvNum s2 s3 \<le> t \<longrightarrow> \<not> A s2))"

definition low_steady_lower_time_limit_if_false where "low_steady_lower_time_limit_if_false t A s s1 \<equiv>
\<not> A s1 \<and> toEnvNum emptyState s1 \<ge> t+1 \<and> (\<forall> s2. toEnvP s2 \<and> s2 \<le> s1 \<and> toEnvNum s2 s1 \<le> t \<longrightarrow> \<not> A s2)"

definition low_steady_lower_time_limit_if_true where "low_steady_lower_time_limit_if_true t A s s1 \<equiv>
A s1 \<and> 
  (\<exists> s3. toEnvP s3 \<and> s3 \<le> s1 \<and> (\<forall> s4. toEnvP s4 \<and> s3 < s4 \<and> s4 \<le> s1 \<longrightarrow> A s4) \<and>
    toEnvNum emptyState s3 \<ge> t+1 \<and> (\<forall> s2. toEnvP s2 \<and> s2 \<le> s3 \<and> toEnvNum s2 s3 \<le> t \<longrightarrow> \<not> A s2))"

definition low_steady_bounded_above2 where "low_steady_bounded_above2 t A s s1 \<equiv>
\<not> A s1 \<and> 
  ((\<exists> s2. toEnvP s2 \<and> s2 \<le> s1 \<and> toEnvNum s2 s1 \<le> t + 1 \<and> A s2) \<or> toEnvNum emptyState s1 \<le> t + 1 \<and> (\<forall> s2. toEnvP s2 \<and> s2 \<le> s1 \<longrightarrow> \<not> A s2)) \<or>
A s1 \<and>
  ((\<exists> s3. toEnvP s3 \<and> s3 \<le> s1 \<and> \<not> A s3 \<and> (\<forall> s4. toEnvP s4 \<and> s3 < s4 \<and> s4 \<le> s1 \<longrightarrow> A s4) \<and> 
    ((\<exists> s2. toEnvP s2 \<and> s2 \<le> s3 \<and> toEnvNum s2 s3 \<le> t + 1 \<and> A s2) \<or> toEnvNum emptyState s3 \<le> t + 1 \<and> (\<forall> s2. toEnvP s2 \<and> s2 \<le> s3 \<longrightarrow> \<not> A s2))) \<or>
  (\<forall> s3. toEnvP s3 \<and> s3 \<le> s1 \<longrightarrow> A s3)
)"

end
  