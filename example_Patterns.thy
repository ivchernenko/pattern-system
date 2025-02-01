theory example_Patterns imports Patterns
 begin
definition P1_inv where "P1_inv t t1_0 A1 A2' A3' s \<equiv> (always_inv (\<lambda> r2 r1 . ((\<not> (A1 r1)) \<or> (constrained_until_inv t t1_0 A2' A3' r2 r1))) s)"


lemma P1_inv_saving : "
P1_inv t t1_0 A1 A2' A3' s0 \<Longrightarrow>
consecutive s0 s
((True \<or> ((A2' s0) \<and> ((A3' s0) \<and> ((t1_0 s0) \<or> (((A3' s s) \<and> ((t1_0 s0) <= t)) \<or> ((A2' s s) \<and> ((t1_0 s0) < (t1_0 s)))))))) \<and> ((\<not> (A1 s)) \<or> (constrained_until_inv t t1_0 A2' A3' s s)))
P1_inv t t1_0 A1 A2' A3' s"

lemma P1_inv_saving : "
P1_inv t t1_0 A1 A2' A3' s0 \<Longrightarrow>
toEnvP s0
(True \<or> ((A2' s) \<and> ((A3' s) \<and> ((t1_0 s) <= t))))
P1 t A1 A2 A3 s0"

lemmas P1_inv_used_patterns = always_inv constrained_until_inv 

end
