variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227658609503066592540709895498 : ((False ∧ (p1 → True)) ∨ (((((((p4 → p5) ∨ (p3 ∨ p3)) → (p3 ∨ (p3 ∨ False))) → False) → (p4 ∨ p3)) ∧ ((p3 ∨ p1) ∧ p2)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_15233711002230773704964328702 : (((p3 → (((True ∧ p2) ∨ ((((p3 ∨ (p4 ∨ (p3 ∨ p1))) ∨ (True ∨ True)) ∧ p2) → ((True ∧ p4) → False))) ∨ p3)) ∨ (p1 ∧ p5)) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112131811440826213326862972365 : (((False ∧ (((p3 ∧ ((p4 ∨ p3) ∧ ((p3 → (False ∧ (p4 → p5))) → ((p1 → p3) ∨ p3)))) → False) ∧ (p3 ∨ p5))) ∨ p4) ∨ (p5 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133751785570495773824850557180 : ((((((p3 ∧ p5) ∨ False) → ((p2 ∨ p2) ∨ p5)) → (((p4 ∨ (((False → p5) ∧ p3) ∨ True)) → p4) → False)) ∧ p5) ∨ (p3 ∨ (False → False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114610689941044943859149741637 : (((p5 ∨ ((p4 → p2) ∧ (((p1 → (p3 ∨ p3)) ∧ (p5 ∧ (p5 ∨ p2))) ∨ p2))) ∧ (p4 ∨ (((p1 → p2) ∧ p4) → p2))) ∨ (p2 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303821527431849058826472674207 : (p1 ∨ (((p4 → (((p4 → p1) → p1) → ((True → p1) ∧ (((p5 ∨ (p5 ∧ p2)) ∨ p4) ∧ (True → ((p2 ∧ p4) ∧ p5)))))) → p1) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118521306914298856440334537589 : ((p3 ∨ ((False ∧ p4) ∨ (((p2 → (p4 ∨ (p1 → p4))) ∨ (p1 ∧ (((p3 ∧ False) ∨ p3) ∧ (p3 ∧ (p5 ∨ p3))))) → p3))) ∨ (True ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177872856452404883100214933401 : (((((True ∧ (((p2 → True) ∨ (p1 ∨ p1)) ∧ p5)) ∧ True) → p2) ∨ p5) ∨ ((p4 → p2) ∨ ((False ∨ p1) ∨ (p4 → (p4 → (p4 ∨ p1)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185236284010909515997717701664 : ((False ∧ (True ∧ ((p5 ∨ p5) ∨ (p4 ∧ ((p5 → p3) → p4))))) ∨ (p3 → (True → ((False ∨ (((True → True) → p3) ∧ (p2 ∨ False))) → p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h9 =>
      -- False on the left can always be used.
      apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117926969027339787321348150025 : ((p5 ∧ ((False ∨ (True ∨ False)) → (False ∨ ((p1 ∧ p4) ∧ ((((False ∧ (p2 ∧ (p3 ∧ p2))) ∧ p1) ∨ True) → (p1 → True)))))) ∨ (p1 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138020372385714863116623828403 : ((True → ((((((p4 ∧ p2) ∧ (p1 ∧ ((p1 → (True ∧ (p1 ∧ (False ∨ True)))) ∨ False))) ∨ p4) ∨ p2) → p5) → p4)) ∨ ((False ∧ p4) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_603933128011616133393911666838 : ((((p5 ∨ ((p2 ∨ (p2 ∧ (((p2 ∨ p2) ∨ (p1 ∧ p4)) ∨ (((False ∨ p4) → p2) ∧ ((p4 → (p2 ∧ p1)) ∨ p2))))) ∧ False)) ∧ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167089040748477425542986991119 : ((((p5 → ((((False ∧ ((p4 ∧ (False → p3)) → p3)) ∧ p4) ∧ p2) ∨ True)) → p1) ∨ False) → ((((p2 ∨ False) → False) ∧ p1) ∨ (p2 → p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- False on the left can always be used.
    apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134790740273444714394227588960 : (((p2 ∧ ((p5 ∨ p5) ∨ ((p1 → ((p5 → (((p5 → p4) ∧ (p1 ∨ p2)) ∧ False)) → p1)) ∧ (p5 ∧ p4)))) → p1) ∨ (False ∨ (True ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54035438752898757837584204158 : ((((p5 → (p2 ∧ ((p3 ∨ False) → p4))) ∨ (p3 ∧ False)) → ((((p1 → (((False ∧ True) ∧ (p1 ∧ p4)) ∨ p3)) → False) → p3) ∨ True)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_330234053359270980913868891234 : (True → (False ∨ (((((p4 → ((((True → (((p4 → p4) ∧ True) → (p3 ∧ p3))) ∧ p3) → (p3 ∧ p1)) ∨ False)) ∧ False) ∨ p3) ∨ True) ∨ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354615106291749109033079971366 : (p5 → (((((p1 → (p4 → ((p3 → p4) → (p3 → p3)))) ∨ (p3 ∧ (p2 ∧ True))) → (((p5 → (True ∨ p3)) ∨ p3) → p2)) ∨ True) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47497480305446928918812464624 : (((p1 ∨ ((p5 ∧ (True → ((((True ∧ True) ∨ p4) ∨ ((p1 → p2) ∧ (p3 ∨ (True ∨ p1)))) ∧ False))) ∧ (p1 ∧ p3))) ∨ (p1 → p1)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205080287731020504063744870996 : (((p5 → (p3 ∧ (False → p5))) → p3) ∨ (p1 ∨ (((True ∧ p5) ∧ p2) → (((p3 ∧ ((p5 ∧ (p1 ∨ p4)) ∧ p1)) ∧ (True → p2)) ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116408170093101335159943324828 : (((True ∨ (p3 → p5)) → ((p5 ∧ (p5 ∧ ((((p2 ∨ ((p1 ∧ (p4 → True)) ∨ p2)) ∨ p5) ∨ False) ∧ False))) ∨ (p1 ∨ True))) ∨ (p5 ∨ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38132470724424137840802334024 : (((((p1 → p4) ∧ ((p2 ∨ p3) ∨ ((False ∧ ((p5 ∨ ((False ∨ True) ∨ p3)) ∨ False)) ∨ (p4 ∨ p5)))) ∧ (True ∧ (False → False))) ∧ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190336952510240101354162765755 : (((((False ∧ p4) ∨ False) ∧ (p5 → (p5 ∧ False))) ∨ p1) ∨ ((((True ∨ ((False ∨ True) → (((p1 ∧ p3) → False) ∨ p3))) ∨ p1) ∨ p3) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_615849409589784220305015767682 : (((((((p5 → p3) → ((p5 ∨ False) ∨ False)) ∧ (True ∧ ((True ∧ p1) → p4))) ∨ (True → (p1 → ((p1 ∨ p1) ∨ (p4 → p4))))) ∨ p5) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49330608661205022428911891910 : (((p5 ∨ ((True ∨ (p1 → ((True ∧ p3) → ((p1 ∧ p3) ∨ ((p5 ∨ (p2 → (p2 ∧ p5))) ∨ False))))) → p2)) ∨ ((False ∧ False) → p5)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48996369650377125498393183407 : ((((p1 ∨ ((p1 → False) ∨ (p1 ∧ (p2 ∧ (p1 ∧ ((p5 → p3) ∨ ((p2 ∧ True) → (p1 ∧ p1)))))))) ∨ p5) ∨ (p4 ∨ (False → p2))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_4073947614340396365793160131 : (p2 ∨ (p1 → (False ∨ ((p2 ∨ (((p2 ∧ True) ∨ p5) ∨ True)) ∨ ((((p2 → p4) ∧ True) ∧ True) ∧ ((p5 → p4) ∨ (p5 ∨ p1))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56476336102172785726064001188 : ((((p1 → p4) → (p5 ∨ p3)) → ((p2 ∧ (((p3 → ((p5 ∧ ((False ∧ True) ∧ p5)) → (True ∧ p4))) → (p2 ∧ p5)) → p1)) ∨ True)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44603651954238812198205674995 : ((((((True ∧ True) ∧ p4) ∨ ((False ∨ p2) ∨ p4)) → (((((p2 ∧ False) ∨ (p1 → p2)) → ((False ∧ p5) ∨ p4)) ∧ p5) ∧ False)) → p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_320010812131159444092669173965 : (p4 ∨ (((p1 ∧ p3) ∧ p4) ∨ ((False ∨ ((p5 → ((p2 ∨ p2) ∨ ((False ∧ ((False ∧ p2) → (p4 → p1))) → p2))) ∧ (p5 ∨ True))) ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_251987061031029262966920842642 : ((p4 → False) ∨ ((((p5 ∧ p3) ∧ ((p1 ∨ False) ∧ p2)) ∨ False) ∨ (((False → p5) ∨ ((True ∧ p4) → (p2 ∨ ((False ∨ p5) ∧ p4)))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60727295597858146121575236400 : ((True ∧ (((p2 ∧ (p4 ∧ p2)) ∨ False) ∨ (p2 ∧ ((p1 ∧ (((True ∧ False) ∨ p2) ∨ (False → p3))) ∧ (((False ∨ p2) → p5) ∧ p3))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_327073852773679934084691613840 : (True → (((p3 ∨ ((p5 ∧ False) → p2)) → (((p1 ∧ p1) ∨ p4) → ((((False ∧ p5) ∨ p4) → ((p1 ∧ True) ∨ (p5 ∧ p5))) ∧ p5))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42884109491836817731595751487 : (((p3 → (((((True → (p4 ∨ (p1 ∨ p1))) → p2) → (((((False ∨ p1) ∨ p4) ∧ p4) ∨ p4) ∨ p2)) ∧ (p4 ∨ p1)) ∨ p3)) ∨ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46163312445551478560996941405 : ((((((True ∧ (p5 ∧ (((True ∨ p3) ∧ (p1 ∧ True)) → p4))) ∧ p5) → (False ∨ (p4 ∧ (p2 ∨ (p3 ∧ p1))))) → p2) ∧ (p3 ∨ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_613480951311591079370626311941 : (((((False → ((p5 ∨ (((True ∧ True) ∧ ((p3 → (p4 ∧ (p3 → p3))) ∧ True)) ∧ p3)) → ((True ∧ p1) → p4))) → (p4 → p4)) ∨ p2) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_622811357677146871166135874518 : ((((p4 ∧ (p5 → ((p3 → p2) ∨ (((p1 → (p5 → (p1 ∧ p4))) ∨ True) ∧ ((True ∨ ((p3 ∨ (p4 → False)) ∧ True)) → p1))))) ∨ True) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51752455013313265071070217882 : ((((p5 ∨ p4) ∧ (p2 → (((True ∨ p5) ∨ (p4 ∧ (p3 ∧ (True ∨ p5)))) → p5))) ∧ (((p4 → (p5 ∨ False)) ∧ (True ∨ p2)) ∧ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218855019701312371301796643555 : ((p2 ∧ (True ∧ (False → p5))) → ((p2 → ((((p1 ∧ (True ∨ ((p5 → p3) ∨ (p2 ∨ p1)))) ∨ (True ∧ p3)) ∧ p1) ∧ True)) ∨ (True ∧ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219572370436514286948289248126 : ((True → ((p3 ∧ True) → p4)) → (((((p4 ∧ (p4 → p3)) ∨ p5) ∧ (p2 ∧ p1)) → (True → p3)) → (((p2 ∧ (p3 → p3)) ∧ p4) → p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_786477607935810252903036112699 : (((p4 ∨ ((p3 → ((p1 ∧ True) → (p1 ∨ (p3 ∨ (p1 ∧ (True → True)))))) ∧ ((p3 ∨ (p3 ∧ ((p2 → (p3 ∧ False)) ∨ p2))) ∨ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48841302342506187614299745049 : (((p1 ∨ (((((((False → p4) ∧ p2) ∨ p4) ∧ p1) ∨ (True → ((p2 → True) → True))) ∧ (True ∧ p5)) ∧ False)) ∧ ((False → False) ∧ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157019622458938363431923341432 : ((((False ∨ False) ∧ (((False → p5) ∧ (False → ((p1 ∧ (True ∧ True)) → (False ∧ p4)))) → False)) ∨ p1) ∨ ((p5 ∨ (True ∨ p4)) ∨ (p2 ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321704235225587265475231514279 : (p4 ∨ (p4 → (p5 ∨ ((p4 → ((p4 → (p3 ∨ (p3 ∧ p3))) → ((((((p5 → True) ∨ True) → p1) ∨ p2) ∨ p4) ∧ (True ∨ p2)))) ∨ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41993096395552700660363791183 : ((((True → p3) ∧ ((((False ∧ (p5 ∧ ((p1 → p1) → ((p2 ∨ (False ∨ (p3 ∧ p2))) ∧ False)))) ∨ p3) → p4) → (p2 ∧ p1))) ∨ True) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_721862555734603479276703505288 : ((((p4 ∨ ((p2 ∨ p3) ∨ p5)) → (((p2 ∨ ((p4 ∨ False) → (p2 → p5))) → p5) ∧ (p5 → (((False → True) ∨ p5) ∨ (p5 ∨ p5))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118869669119478352958704389988 : ((True → ((p2 ∧ (p3 ∨ False)) ∨ (((True ∨ (p1 → ((p1 ∧ (((p4 → True) ∨ p1) ∨ (p1 → p2))) → p4))) ∧ p5) ∧ True))) ∨ (True ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_711174317534649159775728283482 : ((((p2 ∧ (p4 ∧ ((False ∨ p2) ∨ True))) ∧ (p5 → ((p2 ∨ p1) → (p2 → ((p4 → ((p2 ∧ (p3 ∨ p4)) ∧ False)) ∧ (False → p4)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204377373509678157665231866287 : (((p4 ∨ (p3 ∨ (p4 ∨ False))) ∧ p5) ∨ ((p3 ∧ ((p5 → p3) ∧ p3)) → ((((True ∧ p3) → p3) ∧ (False ∧ (p1 ∨ p4))) ∨ (False ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_26034604399616903288520965216 : (((p2 ∨ True) ∧ ((((False → (p4 ∧ (((p2 ∨ p1) ∧ (p1 ∨ (p2 → p3))) ∧ p5))) ∨ (p1 ∨ p2)) → p1) ∨ (True → (True ∨ True)))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_598091004037654741141485799429 : (((((p4 → (p5 → p3)) ∧ ((((False ∨ p3) → (p1 ∧ (False → ((p4 → ((True ∧ False) → (False ∧ p2))) ∧ p3)))) ∨ p5) → p3)) ∧ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299472344464353993650798644908 : (False ∨ ((True → (p4 → (((p5 → (((p2 ∧ p4) ∨ p4) → p1)) → (False ∧ ((((p5 ∧ p3) ∨ (False ∨ p3)) ∧ p5) ∨ False))) ∨ True))) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_582696892899232129326781167282 : (((p5 → (((((p4 → (p1 ∨ True)) → (False → (p4 → (((True ∨ False) ∨ p5) ∨ p3)))) → p3) ∧ (p4 ∨ (p4 → (p4 ∨ p4)))) ∨ p5)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_810689199554532227456853831624 : (((p5 → (((p1 → p1) → p4) ∨ (((p4 → ((p2 ∨ ((p4 → p2) ∨ p1)) ∧ (p5 ∧ ((p5 → p4) → p2)))) ∧ (True → True)) ∨ p5))) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159472187888083418362586341678 : ((((True → ((p2 ∧ False) → (True → p5))) ∧ (True ∧ (p1 → (((p3 ∧ p2) → p3) ∧ p3)))) ∧ p1) → ((p4 ∨ (p3 ∨ p4)) ∨ (p5 ∧ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
  have h8 : p1 := by
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h7, we can now drive its conclusion.
  let h9 := h7 h8
  -- We need to get the right conjuct of h9 based on <expert-advice>.
  let h10 := h9.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51199390329871013066550634197 : ((((((False ∨ ((True → p5) ∧ p3)) ∨ (p3 ∨ False)) ∧ p1) ∨ (p4 → (p2 → (p4 ∧ p4)))) ∨ ((False ∧ False) ∧ ((False ∨ p2) ∧ p4))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160284140827020655328954356585 : (((((((p1 → (p4 ∨ False)) → ((p2 ∧ (True → False)) ∧ p3)) → p5) → p4) ∨ p3) → (True ∨ True)) → (p3 ∨ (p5 → (True ∨ (False ∧ p4))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165479736434607982251875074584 : ((((p1 ∨ (((p3 → (p1 ∧ p2)) ∧ p4) → p2)) ∨ False) ∨ ((p1 ∨ (p4 ∨ False)) ∨ True)) ∨ (p3 ∧ ((p5 ∨ p5) ∨ (False ∨ (p4 ∨ p1))))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_550807944418554687312049558208 : (((p1 ∨ (((p1 ∧ (((p3 ∧ (True ∧ p4)) → ((p3 ∧ False) ∧ p2)) ∨ True)) ∧ ((True ∧ p3) ∨ False)) ∨ ((p4 → True) ∨ (True ∧ p3)))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134164239052088936740893890096 : (((((False → ((p3 ∧ (p2 → (p4 ∧ ((p5 → p5) ∧ p5)))) ∧ p4)) → p2) ∧ (p4 ∨ (p2 ∧ (p2 ∨ p3)))) ∨ p4) ∨ (p4 → (False → False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213721536736996643373013273992 : ((((p1 ∨ p5) → p5) ∨ p2) ∨ (p4 → ((p5 → ((p4 ∧ p1) ∨ (p2 → p3))) ∨ (((p2 ∨ p5) ∧ (True ∨ p5)) ∨ (p3 → (p5 → True)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_683681343638104217931892583650 : (((((True ∧ (False ∨ (p5 ∧ (p2 → (((p1 ∧ False) → (p2 ∧ p2)) ∧ (p2 → False)))))) ∧ p3) ∨ ((False ∨ (p1 ∨ p2)) ∨ (False → p2))) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218038431008321840544590151217 : (((p2 ∨ True) ∧ (p1 ∧ p1)) → (p5 ∨ ((False ∨ (((False → True) → p5) ∨ (p4 ∨ ((p4 → p5) ∨ (p2 ∧ (False → (True ∨ p4))))))) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h3.left
    let h6 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h3.left
    let h9 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55959497985661616708123731676 : (((((p5 ∧ True) ∧ True) ∧ p3) ∨ ((True ∧ (p5 → (p5 ∧ p3))) ∨ (((p3 ∨ (p5 → (p1 ∧ p3))) ∨ False) ∨ ((False ∧ p4) → False)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_211696846913005995790750602122 : ((True ∧ ((p5 ∨ True) ∨ p3)) ∧ ((p4 → False) → (((p3 → (p5 ∧ p2)) → ((p1 ∧ True) → (((p3 ∨ p5) → (True ∧ p3)) ∨ p2))) ∨ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342755666311827367266694975343 : (p2 → (((True ∨ (p5 ∨ (p2 ∨ p2))) → (False ∧ p5)) ∨ ((((((p2 ∨ True) → p2) ∨ (p1 → p1)) → p5) → True) → ((p5 → p1) ∨ p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112571708253977527266179905599 : ((((p4 ∨ (((p2 ∧ (False ∧ True)) ∨ (p2 → False)) → (False ∨ ((((p1 ∨ (p3 → False)) ∧ p3) ∧ p2) → False)))) → p2) → p1) ∨ (True ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248027460873863528464445504900 : ((p1 ∨ p5) ∨ ((p5 → ((p2 ∧ p3) ∨ ((p4 ∨ (p2 ∧ False)) → (False ∧ (((((p5 → p1) → p3) ∨ False) ∧ p5) ∨ p3))))) ∨ (True ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45306278325028126536425979642 : (((p3 ∧ ((((False ∧ p1) → p2) ∨ (p1 ∧ ((False → (((True → (((p5 ∨ p3) ∧ p1) ∨ p4)) → p2) ∨ p1)) → p4))) ∧ p2)) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_664356899706075207258110516816 : ((((p2 ∨ (False → ((p1 ∧ (p5 → ((p3 → (((p2 ∧ p3) ∨ ((p2 → True) → p4)) ∨ p3)) ∨ (p1 ∧ p5)))) → p1))) → (p1 ∨ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200121756607855148036689746249 : (((p2 ∨ (p5 → True)) ∧ ((p1 ∧ True) ∨ p2)) → (p4 ∨ (p2 → ((True → (((True ∧ (p2 ∨ (p4 ∨ False))) ∧ p4) ∧ (p5 ∧ p2))) → p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- Implications on the right can always be decomposed.
      intro h9
      -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
      have h10 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h9, we can now drive its conclusion.
      let h11 := h9 h10
      -- We need to get the left conjuct of h11 based on <expert-advice>.
      let h12 := h11.left
      -- We need to get the right conjuct of h12 based on <expert-advice>.
      let h13 := h12.right
      -- One of the premise coincides with the conclusion.
      exact h13
    case inr h14 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h15
      -- Implications on the right can always be decomposed.
      intro h16
      -- We want to use the implication h16 based on <expert-advice>. So we show its premise.
      have h17 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h16, we can now drive its conclusion.
      let h18 := h16 h17
      -- We need to get the left conjuct of h18 based on <expert-advice>.
      let h19 := h18.left
      -- We need to get the right conjuct of h19 based on <expert-advice>.
      let h20 := h19.right
      -- One of the premise coincides with the conclusion.
      exact h20
  case inr h21 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h22 =>
      -- Conjunctions on the left can always be decomposed.
      let h23 := h22.left
      let h24 := h22.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h25
      -- Implications on the right can always be decomposed.
      intro h26
      -- We want to use the implication h26 based on <expert-advice>. So we show its premise.
      have h27 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h26, we can now drive its conclusion.
      let h28 := h26 h27
      -- We need to get the left conjuct of h28 based on <expert-advice>.
      let h29 := h28.left
      -- We need to get the right conjuct of h29 based on <expert-advice>.
      let h30 := h29.right
      -- One of the premise coincides with the conclusion.
      exact h30
    case inr h31 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h32
      -- Implications on the right can always be decomposed.
      intro h33
      -- We want to use the implication h33 based on <expert-advice>. So we show its premise.
      have h34 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h33, we can now drive its conclusion.
      let h35 := h33 h34
      -- We need to get the left conjuct of h35 based on <expert-advice>.
      let h36 := h35.left
      -- We need to get the right conjuct of h36 based on <expert-advice>.
      let h37 := h36.right
      -- One of the premise coincides with the conclusion.
      exact h37



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112307607574400744230182003770 : (((p2 → ((((True ∨ True) ∧ (p4 ∧ p5)) ∧ (((p5 ∧ (p1 ∨ (False ∧ True))) ∨ (True ∧ (p2 ∧ p3))) → True)) → p3)) ∨ p3) ∨ (True ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308712296938351341967758061179 : (p2 ∨ ((p5 ∨ (p4 ∨ ((((True ∨ ((((False ∧ p5) → ((p2 → p5) ∨ p3)) ∧ p1) ∨ p4)) ∨ p2) ∨ ((p4 ∨ False) ∨ p4)) → p1))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64592523322793927435708077349 : ((p1 ∨ ((p2 ∧ True) ∨ ((((False ∨ ((True ∨ p5) ∧ (p5 ∧ (False ∧ p5)))) ∧ p2) ∧ (p2 → (p5 → ((p2 ∧ p5) → p1)))) ∨ True))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_140559068096406065786886072454 : (((((p1 ∧ p2) ∧ (p3 ∨ p1)) → (((False ∧ p4) ∧ True) ∧ (p1 ∨ (p5 ∧ p4)))) ∨ (p3 ∧ ((p2 → p1) ∨ True))) → ((p4 ∨ True) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_782415253995990929502944409297 : (((p3 ∨ (((p5 ∧ (p1 ∨ ((p3 ∨ ((p4 ∨ ((((True → p5) ∨ p3) ∨ (p2 → p4)) → p1)) → False)) → p5))) ∧ (p2 ∧ p5)) ∨ True)) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53273617415845429592989847972 : (((p1 ∧ ((p4 → (p2 → False)) ∨ (p4 ∧ ((p2 ∨ p1) ∨ p4)))) ∨ ((((p2 ∨ p2) ∨ False) ∧ (p3 → (p1 ∧ p4))) ∨ (False → p1))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204132768749200645310494356101 : ((((p1 ∨ (False ∧ False)) ∧ p3) ∧ p5) ∨ (p5 → (((p1 → False) ∨ ((p2 ∧ True) → p5)) ∨ ((((False ∧ (p1 ∨ p4)) ∨ p4) → p2) → p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56278827398155156255013896697 : (((p5 → ((p4 ∨ True) ∧ False)) ∨ (((p5 ∨ p2) ∨ ((((False → (p5 ∧ p4)) → True) → (p5 ∧ p4)) ∨ ((False → p5) ∨ True))) ∨ p2)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_608740937090308277109578067953 : (((((((((p1 ∨ True) ∨ (False → True)) ∨ (((p1 ∧ (p2 ∨ True)) → p1) ∨ (p1 → True))) ∨ p1) ∧ (p4 ∨ (p2 ∨ p3))) ∨ p4) ∨ True) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205199563012590738766344077006 : (((p1 → (p2 ∨ p5)) ∧ (p3 ∨ p2)) ∨ (((False ∧ p2) → (p1 ∧ (p2 → True))) ∧ (((p1 ∧ p5) ∨ p4) ∨ ((False → p5) ∧ (False → False))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h2
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h5
  -- False on the left can always be used.
  apply False.elim h5
  -- Implications on the right can always be decomposed.
  intro h6
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346614869374881121251151953752 : (p3 → ((((p1 → (p3 ∧ ((p5 ∧ p2) → p5))) ∧ (p3 → True)) → (True ∧ ((False ∧ p1) ∨ ((p4 ∧ p5) ∧ p1)))) ∨ (p5 ∨ (p2 ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172122922450288416533342361471 : ((((False ∨ (True ∧ (False → ((False ∧ True) ∧ False)))) → p2) ∧ (p1 ∨ (p5 ∨ p2))) ∨ ((p3 ∨ (p1 ∧ ((p1 → p2) ∨ p5))) ∨ (True ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_4525684255275955305341129924 : (p3 → ((p5 ∨ ((p3 → (p3 → (p3 → (p4 ∨ p5)))) → ((p1 ∨ p1) ∧ (((p2 → True) ∨ True) ∨ p1)))) ∨ (p2 ∨ (p3 ∧ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_625695119582196539290422107 : (((p5 ∨ ((True ∧ p1) → ((p3 ∧ ((((p3 ∨ (p4 ∨ (False ∧ p2))) ∨ p5) → p2) ∧ False)) ∨ (p4 ∧ p3)))) ∨ (p3 ∨ True)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135615255222988259434413953401 : (((p2 ∨ ((((p5 ∧ (p4 → p5)) ∧ ((False ∧ p3) → False)) → (p2 ∧ p1)) ∧ p2)) ∨ ((p1 → (p5 ∨ True)) ∧ p3)) ∨ (p1 ∨ (False → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_608790550626136675740588482411 : ((((((p2 ∨ ((((True → p2) ∧ (False → False)) → False) → (p1 → (((p5 ∧ p1) ∧ p4) ∨ p2)))) ∨ ((True ∨ p2) ∨ False)) ∨ p2) ∨ p2) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_749656358757419546961960035884 : (((True ∧ (((((p4 ∧ (((False → (False ∧ (p3 → p4))) → p1) ∧ False)) ∨ (p4 ∧ ((p1 ∨ (p5 → p2)) ∧ p4))) → False) → False) ∨ True)) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245637296187364406420602832451 : ((p3 ∧ False) ∨ (p3 → (p4 ∨ ((p5 ∧ p2) ∨ ((((p3 ∧ p3) ∧ p4) ∧ p5) ∨ ((((p4 ∨ p1) ∨ (p4 → p2)) ∨ p4) → (False ∨ True))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h5 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h6 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138404199271549759843261506180 : ((p5 → ((((((True → ((p3 → p1) → p1)) → (p4 ∧ (p1 ∨ p2))) → (True → False)) ∧ (p1 ∧ p3)) ∨ p1) ∧ True)) ∨ (True → (True ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_78697503580461241429815863137 : ((((((p5 ∨ (p2 → (((p4 ∨ p5) ∨ p5) ∨ (True → p2)))) → p3) → p2) ∧ (p3 ∨ ((p1 ∨ p5) → (False ∧ False)))) ∧ (True ∧ p5)) → p2) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h3.left
    let h8 := h3.right
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h9 : ((p5 ∨ (p2 → (((p4 ∨ p5) ∨ p5) ∨ (True → p2)))) → p3) := by
      -- Implications on the right can always be decomposed.
      intro h10
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- One of the premise coincides with the conclusion.
        exact h6
      case inr h12 =>
        -- One of the premise coincides with the conclusion.
        exact h6
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h13 := h4 h9
    -- One of the premise coincides with the conclusion.
    exact h13
  case inr h14 =>
    -- Conjunctions on the left can always be decomposed.
    let h15 := h3.left
    let h16 := h3.right
    -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
    have h17 : (p1 ∨ p5) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h16
    -- We have shown the premise of h14, we can now drive its conclusion.
    let h18 := h14 h17
    -- We need to get the left conjuct of h18 based on <expert-advice>.
    let h19 := h18.left
    -- False on the left can always be used.
    apply False.elim h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44352942647736848336259867833 : ((((p5 ∨ (p1 ∨ (p2 → (True ∨ ((p2 ∧ p2) ∨ ((p4 → p5) ∨ (p3 → p1))))))) → ((p2 → (p4 ∨ (p5 → p4))) ∧ p3)) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_607298501805341037524484238461 : (((((((p1 ∧ False) ∨ p3) ∨ (False ∧ (p2 ∨ ((p5 ∧ (((p4 ∨ (p1 ∨ p3)) ∧ p1) ∧ (False ∨ (p5 → p5)))) ∨ True)))) ∧ True) ∨ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_123112234785111967926757760523 : (((((p5 ∨ (p5 → (False → ((True ∨ True) ∧ p2)))) ∨ (p2 ∨ (p3 ∨ True))) → ((p1 ∨ False) ∨ p1)) → (True ∧ (False ∧ p4))) → (p2 → p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115643666120428997651327153535 : (((((p2 ∨ (p4 → p4)) ∧ p5) → False) ∨ (p3 → (False ∧ (p1 ∨ ((False → p1) ∨ (p1 → (p4 → (False ∧ (False ∧ p4))))))))) ∨ (True → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347329821093165854003532306467 : (p3 → ((p1 → ((p2 ∧ ((p3 ∨ False) ∨ p3)) → (p1 → p5))) → ((p5 ∧ p4) → (((p4 ∧ ((False → p2) → False)) ∧ (p4 ∨ p3)) → p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h3.left
    let h11 := h3.right
    -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
    have h12 : (False → p2) := by
      -- Implications on the right can always be decomposed.
      intro h13
      -- False on the left can always be used.
      apply False.elim h13
    -- We have shown the premise of h8, we can now drive its conclusion.
    let h14 := h8 h12
    -- False on the left can always be used.
    apply False.elim h14
  case inr h15 =>
    -- Conjunctions on the left can always be decomposed.
    let h16 := h3.left
    let h17 := h3.right
    -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
    have h18 : (False → p2) := by
      -- Implications on the right can always be decomposed.
      intro h19
      -- False on the left can always be used.
      apply False.elim h19
    -- We have shown the premise of h8, we can now drive its conclusion.
    let h20 := h8 h18
    -- False on the left can always be used.
    apply False.elim h20



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39086232233613384373191282491 : ((((p4 ∨ p1) ∨ (((p1 ∧ True) ∧ p5) ∨ (((((p2 ∧ ((True ∧ ((p5 ∨ False) → p2)) ∨ p3)) → p4) → p2) ∨ p1) ∧ p1))) ∧ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_320101694068129113000375695742 : (p4 ∨ (((True ∨ p4) → p5) → ((((p5 ∨ p1) ∨ (False → (p4 ∧ p4))) → (p2 ∧ (p2 ∨ (((p5 ∧ p4) → p5) ∧ p5)))) ∨ (False → p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_974280685352653598836282457630 : ((((False → p1) → (((True ∧ p1) ∨ ((p3 ∨ (p3 ∧ (((p5 → (False → (p1 ∨ p4))) ∨ False) ∧ p2))) ∨ (True → (True ∨ True)))) ∧ p5)) → p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (False → p1) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- One of the premise coincides with the conclusion.
  exact h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305418915894938411497408279381 : (p1 ∨ ((p1 ∨ ((((p3 ∨ p3) → True) → (p1 ∧ (True → (p2 ∧ False)))) ∧ (p1 → False))) ∨ (((p3 ∨ p1) ∧ False) → (p1 → (p5 ∨ p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- False on the left can always be used.
    apply False.elim h4
  case inr h6 =>
    -- False on the left can always be used.
    apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149865183796226152080744248233 : ((p2 ∨ (((((True ∨ (p1 → p5)) ∨ p2) ∨ (p5 → p5)) ∧ (((p4 ∧ True) ∨ (p3 ∨ p1)) ∨ p1)) ∨ False)) ∨ (p3 → ((p3 → True) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



