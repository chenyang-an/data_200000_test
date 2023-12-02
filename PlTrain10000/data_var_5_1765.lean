variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_726907372407559930003924252669 : (((((p5 ∨ p1) → p1) ∨ ((((p5 → (p2 ∨ p2)) ∨ p3) → (p2 ∧ p3)) ∨ ((p4 ∨ (((False ∧ p3) → (p3 ∨ True)) ∨ False)) ∨ p1))) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54280957473369329547689145672 : ((((p5 → (p2 ∨ p3)) ∨ ((p4 → False) ∨ True)) ∧ (p3 ∧ ((p3 ∧ p5) → (((p5 → False) ∨ p3) ∧ (((False → False) ∧ p3) ∧ True))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324113428543149273489329074908 : (p5 ∨ (((False → (True → p2)) ∧ (p2 → (False ∨ (p5 ∧ (p5 → p5))))) → ((p4 ∧ p1) → ((p2 ∨ p4) ∨ (False ∧ ((p3 → p5) ∨ p1)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h1.left
  let h6 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_616886406707509093145239528888 : ((((((p1 → (p2 → ((p2 → p2) ∧ False))) → (True ∨ p4)) → (((p2 ∨ ((p2 → p1) ∨ (p2 ∨ p5))) ∧ (True ∨ False)) ∨ True)) ∨ p4) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42642172645292764831147899332 : (((p3 ∨ (p4 → ((p3 → (p4 ∧ ((False ∨ p1) ∧ (((p5 → (p3 ∧ p5)) ∧ False) ∨ (p4 → (p2 ∧ (p2 → False))))))) ∧ False))) ∨ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_216232523613196029621657379992 : ((p1 → ((p2 ∧ p1) → p3)) ∨ (((p4 → (False ∧ p1)) → ((((p1 → (p5 ∧ (p1 ∨ p5))) ∧ True) ∨ (True ∨ (p4 → p4))) → p1)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147618129640310979456709664076 : ((((((((((p4 ∧ ((p1 ∨ p4) ∧ p3)) ∧ p3) ∧ p5) ∧ p1) ∧ p5) ∧ (p2 ∧ False)) ∧ p3) → p1) → False) ∨ ((p2 ∧ (p5 ∧ p1)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50406514345598191899624873809 : (((True ∧ (p1 → (True → (((p1 → (p5 → True)) → (p3 ∨ p4)) ∨ (False ∨ ((p1 ∨ True) ∧ True)))))) ∨ (((p2 ∧ True) ∨ False) ∨ p1)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174587334749261173186455429820 : ((((True → (p1 → p4)) ∨ p3) ∨ (((p2 ∨ p2) ∧ True) ∧ (p1 → (p3 → p4)))) → ((((p1 ∨ False) ∧ True) ∨ (p1 ∧ p2)) ∨ (p4 ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h3 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h6.left
    let h9 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137845890093409639182285594383 : ((p3 ∨ ((((p1 ∧ False) ∨ p5) ∨ p4) ∨ (False → (((p2 ∧ (((p5 ∧ (p4 → p4)) ∧ p5) ∧ p5)) → True) ∨ False)))) ∨ (p2 ∧ (p5 → p4))) := by
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
theorem thm_5_vars_158317113532031460374408572319 : (((p4 ∨ (p1 ∧ p2)) → (p2 ∧ (p2 → (((p5 → (False ∨ (False ∧ p2))) ∨ (p4 → p5)) ∧ p5)))) ∨ (p2 → ((p2 → p4) ∨ (p3 → p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258933283761917173633201059638 : ((True → p2) → (True → (((((p3 ∨ ((p4 ∧ p5) → False)) → p2) → p1) → (p2 → (p4 ∧ (p3 → ((p3 → (True ∧ False)) ∨ p5))))) ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165326087931192612617595268391 : ((((p1 ∨ (False ∨ (p4 ∨ (p5 ∨ ((p2 → p1) ∧ p1))))) ∧ True) ∧ (p4 → (False → p3))) ∨ (((p2 → (p4 ∧ p4)) ∧ (False → False)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_129307395040662970156227617880 : ((((p2 → (p5 ∨ p4)) → (((((((False ∧ p1) ∨ p4) ∧ p2) ∨ (True ∧ p2)) → False) → p3) ∨ (True ∧ p2))) ∨ True) ∧ (False → (p3 ∨ p2))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322204056017513236800775052756 : (p5 ∨ ((((((((False ∧ (p1 ∧ ((True ∨ (p2 → p2)) ∧ True))) ∧ (p2 ∨ (p1 ∧ p2))) → (False ∧ p4)) ∧ p3) ∨ False) → p4) ∧ True) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158526673402817235203504008559 : (((p5 ∨ p2) → (((p1 → p3) → (((p1 → p5) ∧ p5) ∨ p4)) ∨ ((p2 ∧ (False ∨ p2)) ∨ p5))) ∨ (((p2 ∨ (p3 ∨ p4)) → p5) ∨ p2)) := by
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
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233467985519354460691453242494 : ((False ∨ (p5 → True)) → (p5 → ((False ∨ ((((((p1 → (p4 ∨ p1)) ∨ p4) → p1) → False) → p3) ∨ (p2 → p2))) ∨ ((True ∨ p2) → True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44421299192294426571529450566 : ((((p2 → (p3 ∨ ((False ∧ (True → ((p5 ∧ False) ∧ (True ∨ True)))) ∧ p4))) → (False → (False → ((False ∨ (p4 ∨ p1)) ∧ p5)))) → p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_98918357070206893355935968559 : ((True → (((p1 ∨ False) ∨ ((p2 → ((((False → (False ∧ True)) → (p5 ∧ p2)) ∧ p4) ∨ ((p3 → p2) → p1))) → p2)) ∧ (p4 ∨ False))) → p4) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- False on the left can always be used.
    apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_727961365124875298670826371855 : ((((p3 ∨ (p1 ∧ False)) ∨ (p4 ∧ (((((p2 ∨ p2) ∨ ((p5 ∨ False) ∧ (p2 → p3))) ∧ True) ∧ (p3 ∨ (False → p3))) → (p4 ∨ p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178136738276512442867151300448 : (((((p5 ∧ False) → (p3 ∧ False)) ∨ (((True → p5) ∨ p4) → p5)) → False) ∨ (((False → ((p2 ∧ (p1 → p5)) ∧ p4)) ∨ p5) ∨ (p1 ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_585638202873651822273604217405 : ((((((p3 → (((p4 → (p4 ∨ ((p1 → p2) ∨ (((True → (True ∧ (False → p4))) ∧ True) ∧ p1)))) ∨ True) → p5)) ∨ p5) ∧ True) ∧ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_264817806276601859762967361127 : (True ∧ ((p5 ∧ False) ∨ ((((p2 → (((((False ∧ p3) ∨ p1) ∨ p3) ∨ (True → (False → ((False ∧ True) ∨ True)))) ∨ p3)) ∧ p2) ∨ p1) ∨ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_10570177121129551943618454455 : (((p4 → (((p5 → p3) → (((p5 → ((False → True) ∧ p4)) ∧ ((True ∨ p4) ∧ ((False → p1) ∨ p2))) → p3)) ∨ (True ∨ p2))) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301883499563942671249390765970 : (False ∨ ((p5 → p3) ∨ ((p3 ∨ (((((p5 ∨ (p3 ∨ ((p5 ∨ p1) ∧ p2))) → p4) ∨ p3) ∧ (p5 ∨ (p2 ∧ True))) → p4)) ∨ (p2 ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231934257255161151110940084561 : (((False ∨ p5) → p1) → ((p1 → True) → ((((((p1 ∨ p2) ∨ p1) ∨ (p2 ∨ p1)) ∧ p2) ∨ ((p1 ∧ False) ∨ p1)) ∨ (p5 → (p2 → p2))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47338282721715450818474015244 : ((((False ∨ p2) ∧ (((p2 ∨ (False ∨ (((p2 ∨ False) → p4) → (p4 ∧ p2)))) ∧ (True → (p5 → (False ∧ p1)))) ∧ p3)) ∨ (False ∨ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_634776651956394094410626690971 : (((((((((False ∧ p4) ∨ p2) ∧ (p5 ∧ (False ∨ True))) → ((p5 ∧ p5) → False)) ∨ ((True ∨ True) ∧ p5)) ∨ ((p5 ∧ p5) → p2)) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147540046867969739627097772758 : (((p2 → ((p3 → p2) ∧ ((((p1 → p2) → True) → (p1 → p2)) → (p2 → (p5 ∧ (p4 → p3)))))) ∨ p4) ∨ (True ∨ ((False → p1) ∧ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42620729668340148070940286925 : (((p3 ∨ ((((p2 ∨ (p4 ∨ ((p2 → (p3 ∨ p3)) ∨ (True → p1)))) → p1) ∨ (True ∨ p3)) → (p1 ∧ (p2 ∨ (p3 → p4))))) ∨ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301016680109482715642119137505 : (False ∨ ((((False → False) → (p4 → (p3 ∨ (False ∨ p2)))) ∨ True) ∧ ((False → (True ∨ True)) ∨ ((True → ((p1 ∧ False) ∨ (p3 → True))) ∧ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336250592048238077744553308247 : (p1 → ((((p5 ∧ ((p3 → False) ∧ p3)) ∧ ((p4 ∨ (True → ((False → p4) ∧ p2))) → False)) ∧ ((((True ∧ False) ∧ True) → True) → p3)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68722806706627086124474241366 : ((p4 → (((((False ∧ ((True → p5) ∨ ((True ∧ p4) ∨ ((p1 ∨ p3) ∨ False)))) → p4) → p4) → (p1 ∨ p4)) → ((p5 → p3) ∨ p4))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_689817390257718174102857572884 : (((((p4 ∨ False) ∧ (((p4 ∧ (True → p1)) ∧ (p5 → (False ∨ (p4 → False)))) ∨ False)) ∨ ((p3 ∧ (((True ∨ p4) ∨ p5) ∨ p5)) ∧ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171698401455161969830856867411 : (((p1 → ((((p2 ∨ (False ∨ p5)) → p2) → (False ∨ p3)) ∨ (p3 → p3))) ∨ p2) ∨ (((p1 → p2) ∧ (True ∨ (False ∧ p3))) ∧ (p4 → True))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198538837756825462738472575646 : ((False ∨ (False ∧ (p2 ∧ ((p1 ∧ p4) ∨ p5)))) ∨ (False → (p1 → (False ∧ ((True → ((p2 ∧ False) ∧ (p3 → p1))) → (p2 ∨ (p2 → p1))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177932378446907277913428901519 : ((((p2 ∧ ((p1 ∧ p2) ∧ p2)) ∨ (p2 → (p5 ∧ (True ∧ p1)))) ∨ True) ∨ ((p5 → True) ∨ ((True ∨ p4) ∧ ((p2 ∧ (p3 ∨ p1)) ∧ p4)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214137173473821106382057079318 : ((((p3 → True) ∨ p5) → False) ∨ (True ∧ ((((p3 → p3) → p4) ∨ ((p5 ∨ (((True → (p1 ∧ (p4 ∧ p3))) ∧ p5) → p3)) ∨ False)) ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64804619229377621955422549296 : ((p2 ∨ ((p3 ∨ ((((p4 ∧ (True ∨ p3)) ∧ p1) ∨ (True ∧ (((p4 → p5) → ((p5 → p1) → (p1 ∧ p1))) ∨ p5))) ∨ False)) ∨ True)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66080409192441471921313479917 : ((p5 ∨ ((p4 ∨ (((False ∨ ((((p5 → ((p3 ∧ p3) ∨ False)) → (p1 ∨ p5)) → p4) → True)) ∧ ((p2 ∨ p4) ∨ False)) ∧ p1)) ∨ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_676886721426910808726481526587 : ((((p4 ∨ (False ∧ (((p3 → (((p4 → p5) ∨ False) → p3)) ∨ ((p1 → p3) ∨ (False → p4))) ∧ p3))) ∧ (p2 → ((p3 → False) ∧ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234300969085020297179467396013 : ((p1 → (True ∧ False)) → (p1 → (((p3 ∧ p4) ∨ ((True ∨ p5) ∨ True)) ∧ (p1 → (False ∨ (p1 → (p4 ∨ ((False ∨ (p5 → p3)) ∨ False)))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h4 : p1 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h4
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55604954035481171385867025475 : (((False → (((p4 → p5) ∧ False) → p3)) → (((p5 → p3) ∨ (((p5 → (p1 → p4)) ∧ p3) ∧ (False ∨ (True ∧ p5)))) → (p5 ∨ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_788321030483323365965457488079 : (((p5 ∨ ((((((False ∧ False) ∨ p2) ∨ (p2 ∨ ((p4 ∧ (p5 ∧ p3)) → p5))) ∧ (((p3 ∧ True) → p1) ∧ (True ∧ p3))) ∨ p5) ∨ True)) ∨ False) ∧ True) := by
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
theorem thm_5_vars_48589793607740971939531992142 : ((((((((p2 ∧ False) ∨ p4) → p5) ∨ (p2 ∨ p1)) ∨ (p3 ∧ ((p1 ∨ (p4 ∨ True)) ∨ True))) ∧ (p2 → p2)) ∧ (p5 ∧ (p4 ∨ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_645185562732311493600851430154 : ((((p3 ∨ (((False ∨ p5) ∨ p5) ∧ ((((p2 ∨ False) ∨ p5) → p2) ∧ (((p5 ∧ ((True ∧ p4) ∧ p1)) ∧ (p3 ∨ p5)) → p1)))) → p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40956570777077410411596389065 : ((((((True ∧ (p3 ∧ p3)) ∨ (((True ∨ p1) ∧ p5) ∨ (((p5 ∨ p1) ∧ p1) ∧ True))) → ((False ∨ p3) ∨ False)) ∨ (False → p5)) ∨ p4) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50625244007697304784853053760 : (((((p3 → p1) → (p5 → (False ∧ (p1 ∨ (True ∧ (False → (p5 ∧ p3))))))) ∨ ((p2 → False) ∧ p3)) → (((p5 ∨ p2) ∧ p5) ∨ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171885980849926369156230312609 : (((False ∨ (p4 ∨ ((((p1 ∧ p4) → (True ∧ p5)) ∧ p2) ∧ (p4 → p3)))) → p5) ∨ (p2 ∨ (True ∨ (((False ∨ False) ∧ p3) → (p5 ∧ p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157965799320080225279199705961 : (((((False ∧ p3) → p4) → ((True ∨ p4) → p4)) ∨ (p1 ∨ ((False → p3) → (False → (p1 ∨ p1))))) ∨ ((((p4 → p4) ∨ p1) ∨ False) ∨ p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207779004054084181570750535731 : (((p4 ∨ (p5 ∨ (p5 → p5))) → False) → ((p1 ∨ p2) ∧ ((p4 ∨ (p4 ∨ (((((False → False) ∨ p1) → True) → p3) ∨ p3))) → (p5 ∧ p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p4 ∨ (p5 ∨ (p5 → p5))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- False on the left can always be used.
  apply False.elim h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h7 : (p4 ∨ (p5 ∨ (p5 → p5))) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h6
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h8 := h1 h7
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h11 : (p4 ∨ (p5 ∨ (p5 → p5))) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h10
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h12 := h1 h11
      -- False on the left can always be used.
      apply False.elim h12
    case inr h13 =>
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h14 =>
        -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
        have h15 : (p4 ∨ (p5 ∨ (p5 → p5))) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h16
          -- One of the premise coincides with the conclusion.
          exact h16
        -- We have shown the premise of h1, we can now drive its conclusion.
        let h17 := h1 h15
        -- False on the left can always be used.
        apply False.elim h17
      case inr h18 =>
        -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
        have h19 : (p4 ∨ (p5 ∨ (p5 → p5))) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h20
          -- One of the premise coincides with the conclusion.
          exact h20
        -- We have shown the premise of h1, we can now drive its conclusion.
        let h21 := h1 h19
        -- False on the left can always be used.
        apply False.elim h21
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h22 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h23 : (p4 ∨ (p5 ∨ (p5 → p5))) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h22
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h24 := h1 h23
    -- False on the left can always be used.
    apply False.elim h24
  case inr h25 =>
    -- Disjunctions on the left can always be decomposed.
    cases h25
    case inl h26 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h27 : (p4 ∨ (p5 ∨ (p5 → p5))) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h26
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h28 := h1 h27
      -- False on the left can always be used.
      apply False.elim h28
    case inr h29 =>
      -- Disjunctions on the left can always be decomposed.
      cases h29
      case inl h30 =>
        -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
        have h31 : (p4 ∨ (p5 ∨ (p5 → p5))) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h32
          -- One of the premise coincides with the conclusion.
          exact h32
        -- We have shown the premise of h1, we can now drive its conclusion.
        let h33 := h1 h31
        -- False on the left can always be used.
        apply False.elim h33
      case inr h34 =>
        -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
        have h35 : (p4 ∨ (p5 ∨ (p5 → p5))) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h36
          -- One of the premise coincides with the conclusion.
          exact h36
        -- We have shown the premise of h1, we can now drive its conclusion.
        let h37 := h1 h35
        -- False on the left can always be used.
        apply False.elim h37



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166417101970661421739002459098 : ((p1 ∨ ((p3 ∨ (((True → (p3 ∧ p5)) ∨ (p1 ∧ (p4 ∨ p5))) ∧ p2)) ∨ (p4 → p3))) ∨ ((((p3 ∧ p2) ∧ (p2 ∧ False)) ∧ p2) → p5)) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h5.left
  let h9 := h5.right
  -- False on the left can always be used.
  apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64571178621706249179955084567 : ((p1 ∨ ((p3 ∧ (False ∧ p4)) ∨ ((((True → (((((True → False) ∧ True) → p1) ∨ p2) ∨ (p1 ∧ p4))) ∨ p2) ∨ (p3 → p3)) ∨ p2))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301195249933689120023156587541 : (False ∨ ((True → ((p3 → ((p3 ∨ p4) → True)) ∧ p2)) → (p2 → (((((True ∨ p4) ∧ ((p3 → True) → p5)) ∧ p4) ∨ True) ∨ (False ∨ p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40882450766018811813568517904 : (((((p3 ∨ (True → (((p3 → True) ∨ False) ∨ (p2 ∨ (False → (p4 → True)))))) → (p2 ∧ (p4 → (False ∧ p2)))) ∧ (p4 ∧ p5)) ∨ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48194681509251677228114693722 : ((((p1 → True) ∨ (p3 → (((((True → True) ∨ ((((p5 ∨ p1) → (True → p4)) → p5) ∧ p4)) ∨ p5) ∨ p2) ∨ p2))) → (False ∨ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42531705462550883663710207214 : (((p1 ∨ ((p5 ∧ (((p3 ∧ ((False → p2) ∧ (p4 → (((p5 → p3) → p4) ∨ (p3 → (p4 ∧ False)))))) → False) → p4)) ∨ True)) ∨ p3) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_663021529289755088514451637373 : (((((p3 ∧ (p3 ∧ p4)) → (p4 ∧ (((((p5 ∧ (((p1 ∨ p3) → False) ∨ False)) → (p4 ∨ p1)) → p2) ∨ p3) ∨ p3))) → (p5 → p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_757962098231007188077753534634 : (((p1 ∧ (p5 ∨ ((False ∧ False) ∨ ((False → (p3 ∨ (p1 ∧ p3))) → (((p3 ∨ p4) → (((p5 ∧ (False ∧ False)) → p4) ∧ p3)) ∨ p4))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147741454214236887491781035479 : ((((p3 → (True → (p2 ∨ p2))) ∨ (p3 → ((((False ∨ (p3 ∧ p5)) ∨ p5) ∧ (p2 ∧ p3)) → p1))) → p5) ∨ ((True ∨ (p1 ∨ p2)) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_452060785941689765916766051564 : (((((p5 → (False → True)) → (((True ∧ True) ∨ (p4 → ((False → (False ∧ True)) → p5))) → (p3 → p4))) ∨ (False ∨ (p5 → (p5 ∧ True)))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305001709960324491056799969800 : (p1 ∨ (((p1 ∨ (((p2 ∧ True) → (p2 → ((True → ((p4 → p3) ∨ p4)) ∨ p1))) ∨ p1)) → (p3 → (p5 → False))) ∨ ((p1 ∨ p1) → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59952805640861069598174744917 : (((True ∨ p3) → (((p1 ∨ p1) ∧ ((p2 → ((False ∨ ((p4 ∨ (p1 ∧ (True ∧ p2))) → p5)) ∧ (True ∨ (p1 ∧ True)))) ∨ False)) → p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158970969371127204118193034042 : ((p3 ∨ (((True ∨ p2) → (((p3 ∨ (False → p2)) → (((p4 ∧ True) ∨ p4) ∨ True)) ∨ False)) ∨ p5)) ∨ (p2 ∧ (((p5 ∧ p1) → p2) → p2))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h6 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h7
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_797461818368653285445017194495 : (((p1 → ((True → ((p3 ∨ (((p4 → ((False → (((p1 ∨ p5) ∨ True) → p3)) ∧ False)) ∨ ((False ∧ p1) → p1)) ∨ p2)) → p3)) ∨ p1)) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_667241473208297388368683910537 : (((((p2 ∨ p3) ∧ (((p2 ∨ (p1 → False)) ∨ p4) ∧ (True ∧ ((False ∨ ((p5 ∨ p3) → (p2 → p4))) ∨ False)))) ∧ (p5 ∨ (p2 → p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167578649945469205807025879341 : (((((p2 ∨ (p4 ∧ p4)) → p3) ∨ ((p1 ∧ True) ∧ (p4 ∨ (p2 ∧ p3)))) ∨ (p5 ∧ True)) → ((p3 → False) ∨ (False → (p3 ∧ (p4 → p4))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h3 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h4
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- False on the left can always be used.
      apply False.elim h4
      -- Implications on the right can always be decomposed.
      intro h5
      -- False on the left can always be used.
      apply False.elim h4
    case inr h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Conjunctions on the left can always be decomposed.
      let h9 := h7.left
      let h10 := h7.right
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h12
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- False on the left can always be used.
        apply False.elim h12
        -- Implications on the right can always be decomposed.
        intro h13
        -- False on the left can always be used.
        apply False.elim h12
      case inr h14 =>
        -- Conjunctions on the left can always be decomposed.
        let h15 := h14.left
        let h16 := h14.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h17
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- False on the left can always be used.
        apply False.elim h17
        -- Implications on the right can always be decomposed.
        intro h18
        -- False on the left can always be used.
        apply False.elim h17
  case inr h19 =>
    -- Conjunctions on the left can always be decomposed.
    let h20 := h19.left
    let h21 := h19.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h22
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- False on the left can always be used.
    apply False.elim h22
    -- Implications on the right can always be decomposed.
    intro h23
    -- False on the left can always be used.
    apply False.elim h22



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50862179119223957241196759494 : (((((True ∨ (p4 ∨ (p5 → p3))) → ((((p4 → p1) ∨ p2) ∧ p3) → (p1 ∧ True))) ∨ p1) ∧ (p3 ∧ (p1 ∨ ((p5 → False) → p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137479754902725012663385047239 : ((p5 ∧ (((p3 → ((p2 ∨ (p3 ∨ (False ∨ (p1 → p1)))) → ((p1 → p5) ∨ (p5 → p2)))) ∨ (p3 ∨ p1)) ∧ p3)) ∨ (False → (p4 → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230444859157356615413300612169 : (((p5 ∨ True) ∧ p2) → ((p5 ∧ (p1 ∨ p1)) ∨ ((False ∧ ((((p1 ∨ (True → p5)) ∧ p3) ∧ p5) ∧ (True ∧ (True ∧ False)))) → (p3 ∨ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- False on the left can always be used.
    apply False.elim h6
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- False on the left can always be used.
    apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_353582913550068356469834580486 : (p4 → (p3 ∨ (p2 → ((((True ∨ p5) ∧ p3) ∨ (True ∧ ((((((False → (False → p5)) ∨ p3) ∧ p1) → False) ∧ p5) ∨ (False ∧ p2)))) ∨ p4)))) := by
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
theorem thm_5_vars_2015505239006599510746789394 : (((True ∨ p3) → (True → ((p4 ∧ p2) ∧ (((p1 ∧ (p2 → p1)) ∧ p3) ∨ ((p1 ∨ False) ∨ p3))))) → ((p1 ∨ (p5 → p3)) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (True ∨ p3) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h8.left
    let h11 := h8.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h10
  case inr h12 =>
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h13 =>
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h14 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h14
      case inr h15 =>
        -- False on the left can always be used.
        apply False.elim h15
    case inr h16 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h17
      -- One of the premise coincides with the conclusion.
      exact h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_726120631090633273288051077204 : (((((p2 ∧ p4) ∨ False) ∨ ((((p2 → ((True → (p1 ∧ p3)) ∨ p4)) ∨ (p5 ∨ p4)) → p2) ∨ ((p2 → (True ∨ p4)) ∧ (True ∧ True)))) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_728412950428227577862053291090 : ((((p1 → (p5 → False)) ∨ (((p5 ∧ ((p2 → (p1 ∨ p3)) ∨ p4)) → (((True → p5) → ((p3 → True) → p5)) → (p4 ∧ p3))) → p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213553166429641831794496906460 : ((((p5 ∧ False) ∧ True) ∨ p5) ∨ (((p5 → p1) → (((((p5 → (False ∨ (p1 ∧ (True → p4)))) → p2) ∨ (p5 ∧ p4)) → p5) → p1)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341050314877267285992533182984 : (p2 → ((p1 ∨ (False ∧ (((p2 ∧ (p4 ∧ ((((p3 → p3) → (p2 → p4)) ∨ (True ∨ p2)) ∨ (p4 ∧ p4)))) ∧ p5) ∧ (p4 ∧ p3)))) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197694079867715079471159625354 : (((p3 ∨ (p4 → (p5 ∨ True))) → (p4 ∨ False)) ∨ ((False → ((p3 ∧ (p1 ∧ p5)) ∧ p5)) ∨ ((((True ∨ (p5 ∧ p5)) → True) ∨ True) ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_343441979373378618544843003088 : (p2 → ((p3 ∨ p5) ∨ (((p5 → p4) ∧ (p2 ∧ ((p3 → p1) ∧ ((((True ∨ p3) ∨ (p1 ∨ False)) ∨ False) ∨ True)))) → (p4 → (p4 ∨ p3))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h7.left
  let h9 := h7.right
  -- Disjunctions on the left can always be decomposed.
  cases h9
  case inl h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- Disjunctions on the left can always be decomposed.
        cases h12
        case inl h13 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h3
        case inr h14 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h14
      case inr h15 =>
        -- Disjunctions on the left can always be decomposed.
        cases h15
        case inl h16 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h3
        case inr h17 =>
          -- False on the left can always be used.
          apply False.elim h17
    case inr h18 =>
      -- False on the left can always be used.
      apply False.elim h18
  case inr h19 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44184026957834230594290390960 : ((((p2 → ((p1 ∨ ((((p1 ∧ p3) ∧ (p1 ∨ (True → p5))) ∨ (p1 ∨ (False → True))) ∨ False)) ∨ True)) → (False ∧ (p2 ∧ True))) → p5) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p2 → ((p1 ∨ ((((p1 ∧ p3) ∧ (p1 ∨ (True → p5))) ∨ (p1 ∨ (False → True))) ∨ False)) ∨ True)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118206870670423944835925999805 : ((p1 ∨ (((p2 ∧ (((p5 → p5) → ((((p2 → p4) ∨ ((p1 ∨ (p2 → True)) ∧ True)) ∧ p2) → p4)) ∨ p5)) ∧ p3) ∧ p3)) ∨ (True ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111210787531463001936299242134 : ((((p5 ∨ (p1 ∧ False)) ∨ (((p2 ∧ p2) ∨ ((p3 ∧ p4) → ((p1 → p5) ∧ (p4 ∧ (p2 ∨ p3))))) → (p4 ∨ p5))) ∧ p5) ∨ (True ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148914872109847343341936213721 : (((((p4 ∨ p2) ∧ p3) ∨ True) → ((((p1 ∨ (p1 ∨ p5)) ∨ (p1 ∧ (p1 → (True ∨ p3)))) → p3) → p4)) ∨ (((p5 → p4) ∧ p2) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45619651100822737322135580115 : (((p4 ∨ ((((True → (((p4 ∧ True) → p5) → (p5 → ((((p2 → p5) ∨ p1) ∧ p5) ∧ (False ∧ False))))) ∧ p3) → p4) ∧ p4)) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41026036933317837082402941676 : (((((p5 ∧ ((False ∧ (p2 ∨ ((False ∨ False) → (p2 ∧ p4)))) → (((p2 → p4) ∨ p1) ∧ False))) ∧ (p3 → p3)) → (p4 ∨ p1)) ∨ True) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148352321359713990257698743525 : ((((p3 → p3) → ((p2 → (True → (p2 ∨ p1))) ∧ (p1 ∧ (p4 ∧ p4)))) ∧ (True → ((p4 ∧ p5) ∨ p1))) ∨ (((p4 ∧ p1) ∧ False) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218190884160321331672037215626 : (((p1 ∧ p4) ∨ (p4 → p4)) → ((p4 ∧ (p2 → p4)) ∨ (((False ∧ (((p4 ∨ (p1 → p4)) ∧ p3) ∨ p3)) ∧ ((p3 ∧ False) ∧ True)) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42921114067198261386832140647 : (((p4 → (((True → p2) ∧ ((((p1 ∧ ((p2 ∨ (p1 ∧ p1)) ∧ (p1 ∨ False))) ∨ (p5 ∧ (p1 → p4))) ∧ p3) ∨ False)) ∧ False)) ∨ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187080002935114563502047418466 : (((True → p4) ∧ (True ∨ (((False → True) ∧ (p4 → p1)) → p1))) → (True ∧ ((p4 → ((((p1 ∨ p3) ∧ False) → p1) → p5)) ∨ (p4 → True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197932633104821389363371190721 : (((p4 → (p5 → p5)) → (False ∨ (p3 ∨ False))) ∨ (((p3 → ((True → p5) ∨ False)) ∨ (True ∧ (p1 → True))) ∨ ((p3 → True) ∧ (p4 ∧ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173780134200136300928050003566 : ((((p3 ∧ p4) ∨ ((((p2 → ((p3 ∨ p3) → True)) → False) ∧ p3) ∨ p2)) ∨ p5) → ((p2 ∨ ((p4 ∨ (p1 ∧ (p5 ∨ True))) ∨ p5)) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h3 =>
      -- Conjunctions on the left can always be decomposed.
      let h4 := h3.left
      let h5 := h3.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Conjunctions on the left can always be decomposed.
        let h8 := h7.left
        let h9 := h7.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h9
      case inr h10 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h10
  case inr h11 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328286469649045023955530077456 : (True → (((((((p4 ∨ (p2 → True)) ∨ True) → p3) ∨ (p2 ∨ p3)) → (True → p4)) ∧ (True ∨ (p3 ∨ p3))) ∨ (((p5 ∨ p1) → p3) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158049930158315800971459412129 : ((((True ∨ False) ∧ (p2 ∧ (True ∧ False))) ∨ ((((p1 ∧ p3) ∨ p4) ∨ p2) → ((p1 ∨ False) ∨ p1))) ∨ (p1 → ((p5 ∧ (p1 → p4)) → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136837459370785971429985491953 : (((p1 ∧ p5) ∨ ((((p4 ∧ p1) → True) ∧ (p3 ∧ ((p2 → p4) → True))) → (p4 ∨ (((p5 ∧ False) ∧ p1) ∧ False)))) ∨ (True ∨ (p3 ∧ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_656172226465816899303431399216 : ((((((p2 ∨ (p3 → p1)) ∧ ((True → (p2 ∨ p3)) ∨ ((p1 → True) → p1))) ∨ (p4 ∨ (True ∨ ((p4 ∨ False) ∨ p1)))) ∨ (False ∧ p2)) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166473016537337129311334592845 : ((p3 ∨ ((False ∧ (True → ((p5 ∧ (p1 → (True → True))) → ((p5 ∧ p1) → p1)))) ∧ False)) ∨ (((p2 ∧ ((p5 ∧ p3) ∨ p4)) ∨ False) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246544393278904031318607168730 : ((p5 ∧ p1) ∨ (True → (((((True ∨ True) → p5) ∧ ((p1 ∧ (p4 ∨ p1)) ∨ (p4 ∨ (((True ∧ (p1 ∧ p2)) ∨ p2) → True)))) ∧ p3) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_621805564224033588163722765731 : ((((p1 ∧ (((p2 ∧ (((p3 ∨ (p4 ∨ p1)) ∨ False) ∧ (False ∧ p4))) → ((((p3 ∨ p4) ∧ p3) → p2) ∧ p2)) → (p3 → p1))) ∨ True) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_174552010713529608072998560983 : ((((p3 ∨ (True ∧ p4)) ∧ p1) ∧ (((((p2 → p2) → p3) ∧ p4) ∨ p5) ∨ p5)) → (((False ∨ p3) → p4) → (((p5 ∨ p2) ∨ p3) ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Conjunctions on the left can always be decomposed.
        let h10 := h9.left
        let h11 := h9.right
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h7
      case inr h12 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h7
    case inr h13 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h7
  case inr h14 =>
    -- Conjunctions on the left can always be decomposed.
    let h15 := h14.left
    let h16 := h14.right
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h17 =>
      -- Disjunctions on the left can always be decomposed.
      cases h17
      case inl h18 =>
        -- Conjunctions on the left can always be decomposed.
        let h19 := h18.left
        let h20 := h18.right
        -- We want to use the implication h19 based on <expert-advice>. So we show its premise.
        have h21 : (p2 → p2) := by
          -- Implications on the right can always be decomposed.
          intro h22
          -- One of the premise coincides with the conclusion.
          exact h22
        -- We have shown the premise of h19, we can now drive its conclusion.
        let h23 := h19 h21
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h23
      case inr h24 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h24
    case inr h25 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h25



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_613141479759939888069480578984 : ((((((((True ∨ True) ∨ ((p4 → False) ∨ p2)) ∧ ((True → p5) ∧ (True ∨ ((p5 ∧ p4) → p3)))) ∧ (p4 → False)) → (False ∨ True)) ∨ True) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_199872780961043526713127950224 : (((p3 → ((False ∨ p2) ∧ True)) ∧ (p4 → p4)) → ((p1 ∨ ((p3 ∨ ((p3 → p2) ∧ (p2 → (p4 → (p2 → p2))))) ∨ True)) ∨ (p2 → p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



