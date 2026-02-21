theory EDTL_High_Steady
  imports VCTheoryLemmas
begin

fun high_steady_time :: "state \<Rightarrow> (state \<Rightarrow> bool) \<Rightarrow> nat" where
"high_steady_time emptyState A = 0" |
"high_steady_time (toEnv s) A = (if  A (toEnv s) then if prev (toEnv s) = emptyState \<or> \<not> A (prev (toEnv s)) then 0 else Suc (high_steady_time s A) else high_steady_time s A)" |
"high_steady_time (setVarBool s x u) A = high_steady_time s A" |
"high_steady_time (setVarInt s x u) A = high_steady_time s A" |
"high_steady_time (setVarReal s x u) A = high_steady_time s A" |
"high_steady_time (setVarArrayBool s x i u) A = high_steady_time s A" |
"high_steady_time (setVarArrayInt s x i u) A = high_steady_time s A" |
"high_steady_time (setVarArrayReal s x i u) A = high_steady_time s A" |
"high_steady_time (setPstate s p q) A = high_steady_time s A" |
"high_steady_time (reset s p) A = high_steady_time s A"

definition high_steady_upper_time_limit where "high_steady_upper_time_limit t A s s1 \<equiv>
 A s1 \<and> 
  ((\<exists> s2. toEnvP s2 \<and> s2 \<le> s1 \<and> toEnvNum s2 s1 \<le> t + 1 \<and> \<not> A s2) \<or> toEnvNum emptyState s1 \<le> t + 1 \<and> (\<forall> s2. toEnvP s2 \<and> s2 \<le> s1 \<longrightarrow> A s2)) \<or>
\<not> A s1 \<and>
  (\<forall> s3. toEnvP s3 \<and> s3 \<le> s1 \<and> A s3 \<and> (\<forall> s4. toEnvP s4 \<and> s3 < s4 \<and> s4 \<le> s1 \<longrightarrow> \<not> A s4) \<longrightarrow> 
    ((\<exists> s2. toEnvP s2 \<and> s2 \<le> s3 \<and> toEnvNum s2 s3 \<le> t + 1 \<and> \<not> A s2) \<or> toEnvNum emptyState s3 \<le> t + 1 \<and> (\<forall> s2. toEnvP s2 \<and> s2 \<le> s3 \<longrightarrow> A s2)))"

definition high_steady_upper_time_limit_if_true where "high_steady_upper_time_limit_if_true t A s s1 \<equiv>
 A s1 \<and> 
  ((\<exists> s2. toEnvP s2 \<and> s2 \<le> s1 \<and> toEnvNum s2 s1 \<le> t + 1 \<and> \<not> A s2) \<or> toEnvNum emptyState s1 \<le> t + 1 \<and> (\<forall> s2. toEnvP s2 \<and> s2 \<le> s1 \<longrightarrow> A s2))"

definition high_steady_upper_time_limit_if_false where "high_steady_upper_time_limit_if_false t A s s1 \<equiv>
\<not> A s1 \<and>
  (\<forall> s3. toEnvP s3 \<and> s3 \<le> s1 \<and> A s3 \<and> (\<forall> s4. toEnvP s4 \<and> s3 < s4 \<and> s4 \<le> s1 \<longrightarrow> \<not> A s4) \<longrightarrow> 
    ((\<exists> s2. toEnvP s2 \<and> s2 \<le> s3 \<and> toEnvNum s2 s3 \<le> t + 1 \<and> \<not> A s2) \<or> toEnvNum emptyState s3 \<le> t + 1 \<and> (\<forall> s2. toEnvP s2 \<and> s2 \<le> s3 \<longrightarrow> A s2)))"

definition high_steady_lower_time_limit where "high_steady_lower_time_limit t A s s1 \<equiv>
A s1 \<and> toEnvNum emptyState s1 \<ge> t+1 \<and> (\<forall> s2. toEnvP s2 \<and> s2 \<le> s1 \<and> toEnvNum s2 s1 \<le> t \<longrightarrow> A s2) \<or>
\<not> A s1 \<and> 
  (\<exists> s3. toEnvP s3 \<and> s3 \<le> s1 \<and> (\<forall> s4. toEnvP s4 \<and> s3 < s4 \<and> s4 \<le> s1 \<longrightarrow> \<not> A s4) \<and>
    toEnvNum emptyState s3 \<ge> t+1 \<and> (\<forall> s2. toEnvP s2 \<and> s2 \<le> s3 \<and> toEnvNum s2 s3 \<le> t \<longrightarrow> A s2))"

definition high_steady_lower_time_limit_if_true where "high_steady_lower_time_limit_if_true t A s s1 \<equiv>
A s1 \<and> toEnvNum emptyState s1 \<ge> t+1 \<and> (\<forall> s2. toEnvP s2 \<and> s2 \<le> s1 \<and> toEnvNum s2 s1 \<le> t \<longrightarrow> A s2) "

definition high_steady_lower_time_limit_if_false where "high_steady_lower_time_limit_if_false t A s s1 \<equiv>
\<not> A s1 \<and> 
  (\<exists> s3. toEnvP s3 \<and> s3 \<le> s1 \<and> (\<forall> s4. toEnvP s4 \<and> s3 < s4 \<and> s4 \<le> s1 \<longrightarrow> \<not> A s4) \<and>
    toEnvNum emptyState s3 \<ge> t+1 \<and> (\<forall> s2. toEnvP s2 \<and> s2 \<le> s3 \<and> toEnvNum s2 s3 \<le> t \<longrightarrow> A s2))"



end