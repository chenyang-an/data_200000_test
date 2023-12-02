variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184995864942680094377045196602 : (((p2 ∧ p1) ∧ (p4 ∧ (False ∨ (p2 ∨ ((p3 ∨ p1) ∧ p5))))) ∨ ((p5 ∧ (p3 → p5)) ∨ (p1 ∨ ((False → p3) ∨ (p5 ∨ (p3 ∧ p5)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40192881345769543052722881324 : (((((False ∨ (p5 ∨ p1)) ∨ (((p4 → p4) ∨ ((((p5 → p1) ∨ True) ∧ True) ∨ p2)) ∧ (((p4 ∨ p5) → p2) ∧ False))) ∧ p5) ∨ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_253627037637244634162257329737 : ((p1 ∧ True) → ((p5 ∧ (p4 ∧ ((True ∨ (False ∧ p3)) ∨ p1))) ∨ (p1 → ((p5 ∧ p3) ∨ ((p4 → ((p4 ∧ p5) ∨ (p1 ∧ True))) ∨ p4))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h5
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116085325463571052179519746549 : ((((p5 ∧ p4) ∨ False) ∧ ((p4 ∨ (p1 → p5)) ∧ ((((False ∨ (((False ∨ (p4 ∨ p5)) ∨ p3) → p5)) ∨ False) ∧ False) → False))) ∨ (False → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114876372801815772449719508847 : (((((p3 ∧ p5) ∨ p5) → (((p3 ∧ p4) ∨ p1) → (False ∧ (True ∧ p3)))) ∨ (((((False ∨ p4) ∨ False) ∨ p3) ∧ True) ∨ p5)) ∨ (True → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67881944423336310412344814029 : ((p2 → (((p2 → ((p4 → (((p1 ∧ (p3 ∨ (p1 ∨ p3))) ∨ p5) ∧ (p2 ∨ p3))) ∨ True)) ∨ p1) ∨ (p5 ∧ (p3 → (p5 ∨ p1))))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_654502509542149684655746884972 : (((((False ∧ (p5 ∧ (((True ∧ ((False ∧ ((p1 ∨ (False → (p5 ∨ p3))) ∨ (p5 ∧ p3))) → p4)) ∧ p1) → False))) ∨ p5) ∨ (p1 → p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301206029977918256682354778651 : (False ∨ (((False ∧ ((p5 → False) ∨ p4)) ∨ True) ∧ (((((p2 ∨ p4) → False) ∧ p3) ∨ (p3 ∧ (True ∨ True))) ∨ (True ∨ ((True ∨ True) ∧ p1))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190886127307585352386282685114 : ((((p5 ∨ p1) → ((p4 ∧ p4) ∨ p3)) → (p1 ∧ p4)) ∨ ((p1 → p1) → (((True ∨ p2) ∨ (p3 ∨ ((p2 ∧ True) → p4))) ∨ (False ∧ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356031900911163079407967368206 : (p5 → (((((False → p1) → (p4 ∧ False)) ∨ p4) ∨ ((True ∧ (p1 ∨ p5)) ∧ (p2 ∨ ((p4 → False) ∨ p5)))) ∨ (((p2 ∨ p1) → False) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307799358061659190757954135527 : (p1 ∨ (p4 → (((p1 ∨ (((p5 → (p4 → ((p2 ∧ (False ∧ False)) ∨ (False ∨ p3)))) ∧ (False → (p1 ∧ p1))) ∧ p1)) ∨ p3) ∨ (True ∧ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_789413367757226356381969906118 : (((p5 ∨ (((((((p2 ∨ False) ∧ p1) → p1) ∨ (p4 ∨ (p3 ∨ False))) ∨ p3) ∨ False) → (p5 ∨ (True ∧ ((p1 → (p5 → p3)) ∨ False))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308697374705790939329440322189 : (p2 ∨ ((p3 ∨ ((((((p4 → (p3 ∧ (p4 ∧ p4))) ∨ p2) → (p2 ∨ p2)) → p5) ∨ ((True ∧ ((p5 ∧ p2) ∨ p3)) ∧ p1)) → p3)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50764287865116102597920100364 : (((True ∨ (p2 ∨ ((p3 ∧ ((((p4 ∧ (False ∨ (p1 ∧ p2))) ∨ p4) ∨ p5) → (True ∧ p1))) ∧ True))) → (((False ∨ p5) ∨ True) ∨ p3)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_714816477104815292786317347350 : ((((p2 ∧ (((p2 ∨ p3) ∨ p3) ∧ p1)) → (((((p3 ∧ (((p5 ∨ (True ∧ p5)) ∨ (p2 → False)) ∨ False)) ∧ p1) ∧ p2) ∨ p1) ∨ p4)) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h8 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5
  case inr h9 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_344745294644852907386827961047 : (p2 → (p3 → ((p2 ∧ p5) ∨ (((((p2 ∧ (p2 ∨ p3)) → p3) ∧ ((p4 ∨ p5) ∨ p1)) ∨ ((p3 ∨ p3) → p5)) ∨ (p1 → (p1 ∧ p3)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h3
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_472774531175430218796568512446 : (((((((p5 ∨ (p2 → (False → p2))) ∨ (p1 → p4)) → False) ∧ True) → (p5 ∧ (((p2 → p1) → (p2 ∧ ((False ∧ p4) → False))) ∨ p5))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : ((p5 ∨ (p2 → (False → p2))) ∨ (p1 → p4)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Implications on the right can always be decomposed.
    intro h6
    -- False on the left can always be used.
    apply False.elim h6
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h7 := h2 h4
  -- False on the left can always be used.
  apply False.elim h7
  -- Conjunctions on the left can always be decomposed.
  let h8 := h1.left
  let h9 := h1.right
  -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
  have h10 : ((p5 ∨ (p2 → (False → p2))) ∨ (p1 → p4)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h11
    -- Implications on the right can always be decomposed.
    intro h12
    -- False on the left can always be used.
    apply False.elim h12
  -- We have shown the premise of h8, we can now drive its conclusion.
  let h13 := h8 h10
  -- False on the left can always be used.
  apply False.elim h13
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_780384157594654929316252468944 : (((p2 ∨ ((False ∨ (False ∧ ((((p1 → p5) → ((p4 ∨ p4) ∧ (p4 ∧ p5))) ∨ True) ∧ p2))) ∧ (((p4 ∧ p3) ∧ (False ∨ p4)) ∨ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_92566131132211191294791101208 : (((True → True) → (((False → p2) ∧ ((False → ((((((p1 ∧ p4) ∨ p5) ∧ ((False ∨ p4) ∨ False)) → p5) → True) ∧ p5)) ∧ p3)) ∧ p1)) → p1) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (True → True) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45731283245935904084579365268 : (((True → (p2 ∨ ((p1 ∨ (p1 ∨ (((p3 ∧ (p4 → p2)) → ((p5 ∧ p3) ∨ ((p4 ∨ p5) ∧ (False → True)))) ∨ True))) ∧ p3))) → p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356433874194969057711329340143 : (p5 → ((((p5 ∧ (p1 ∧ (p1 ∧ False))) ∨ ((p4 → True) → p1)) ∨ p1) ∨ ((p1 ∨ ((((True ∨ (p4 ∨ p2)) → p3) → p3) ∧ p1)) ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138216918891416119977887012998 : ((p2 → ((True → (((((p3 ∨ (p2 ∨ p1)) ∧ (p4 ∧ ((p3 ∧ (p2 → p4)) → p3))) ∧ p1) ∨ p3) ∨ False)) ∨ True)) ∨ (p4 → (True ∧ p5))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62000981619703136953428139129 : ((p2 ∧ ((p4 ∨ (p1 ∨ (p1 ∨ True))) ∧ (((((((False ∧ p1) ∧ (False → p3)) → (p1 ∨ False)) ∧ True) ∨ p1) ∨ (p3 → p5)) → p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157186700836367704477779008490 : ((((p2 ∨ (((False ∨ ((False → p4) ∧ False)) ∧ (p5 ∨ (p1 → p3))) ∧ (p1 ∨ p1))) → p3) → p1) ∨ ((((False ∧ p4) ∧ p3) ∨ p4) → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- Conjunctions on the left can always be decomposed.
    let h5 := h3.left
    let h6 := h3.right
    -- False on the left can always be used.
    apply False.elim h5
  case inr h7 =>
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_702820120837264736030103929907 : (((((p4 ∧ (p3 → (False → True))) ∧ (p3 ∨ (False → False))) ∨ ((p3 ∨ ((p1 ∧ False) ∨ (p4 ∨ (((p1 ∧ False) ∧ p3) ∧ p5)))) ∨ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137057914665234719577952730647 : (((p2 → p1) → (((((True → p3) → (p1 ∨ p4)) → (p3 ∨ (p5 ∧ ((p4 → True) → (p5 ∧ p1))))) ∨ p1) → False)) ∨ (p5 → (p3 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_609415948166086348314697825162 : ((((((True → True) → (p4 ∧ ((True ∧ (p4 ∨ p2)) → (p3 ∧ ((p2 ∧ (((p4 ∧ (p2 ∨ False)) ∧ p3) → True)) ∧ p1))))) ∨ True) ∨ False) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_659630114432349693712665346327 : ((((((((p3 ∨ p4) ∧ p5) ∨ ((p2 ∨ False) ∨ p2)) → (True ∧ ((p1 → ((p5 → (True ∧ p1)) ∨ False)) → p3))) ∧ p4) → (p3 → p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_69157790367983550903800369904 : ((p5 → (((((p2 ∨ p4) → p1) ∧ ((False → p5) → ((p2 ∧ p3) ∧ (p2 ∨ p2)))) ∧ (p5 ∧ True)) ∨ ((p5 ∨ p5) → (p2 ∨ False)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_664876411071575393659970776292 : ((((p2 → ((False → p3) ∧ ((p5 ∧ ((((p5 → (p3 ∧ ((p4 → p1) ∧ True))) ∨ False) ∨ p4) ∨ (True ∧ p4))) ∨ p5))) → (p3 ∨ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_750799258423674046567446230947 : (((True ∧ (((((True ∧ (p1 ∨ p3)) ∧ True) ∧ p2) ∨ ((p2 ∨ p2) → p5)) → ((p2 ∨ (((False ∨ p5) ∧ False) ∨ (p5 ∧ p5))) ∧ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178811320782609231618859786462 : (((p1 ∧ (p4 ∨ p1)) ∨ (((((p4 → p3) ∨ p5) ∧ p1) ∨ p2) → p3)) ∨ ((p2 → ((p4 ∧ p2) → ((False ∨ (p2 ∧ p1)) ∨ True))) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59735114934658256107612871693 : (((p1 ∧ True) → ((p2 ∧ ((p1 → (p5 ∧ (True ∨ p1))) ∧ p4)) → ((p5 → ((True ∨ False) ∨ p1)) → (True ∧ ((p3 ∧ p1) → False))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300121032626411665749909343074 : (False ∨ (((p1 ∨ (p2 ∧ p5)) ∧ (((p3 → p5) ∧ ((False ∧ True) ∨ p5)) ∨ ((True → p2) ∧ ((p1 → (True ∨ p2)) ∧ p3)))) ∨ (p2 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116696843214562362007542694629 : (((False ∧ p2) ∨ ((p1 ∨ (((((True ∧ p4) ∧ True) ∧ (p2 ∨ p4)) → (p4 ∧ p1)) → p5)) ∨ (p1 → (p5 ∨ (p4 → p1))))) ∨ (p4 → p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_644215902571146572802870326207 : ((((False ∨ ((p2 ∨ ((((False ∨ ((p3 → p1) → True)) → ((p4 → (True ∨ p1)) ∧ True)) ∧ p5) → ((True → True) → p4))) ∧ True)) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_144807515064377913994246434933 : (((((p1 ∧ p4) ∨ ((p5 ∨ False) ∨ (p4 ∨ ((p4 ∧ p1) ∨ (p2 → p4))))) ∨ True) → (p3 ∨ (p1 → True))) ∧ (p2 ∨ ((False → p5) ∨ p1))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
      -- Implications on the right can always be decomposed.
      intro h6
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Disjunctions on the left can always be decomposed.
        cases h8
        case inl h9 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h10
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h11 =>
          -- False on the left can always be used.
          apply False.elim h11
      case inr h12 =>
        -- Disjunctions on the left can always be decomposed.
        cases h12
        case inl h13 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h14
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h15 =>
          -- Disjunctions on the left can always be decomposed.
          cases h15
          case inl h16 =>
            -- Conjunctions on the left can always be decomposed.
            let h17 := h16.left
            let h18 := h16.right
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h19
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h20 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h21
            -- True on the right can always be proven directly.
            apply True.intro
  case inr h22 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h23
    -- True on the right can always be proven directly.
    apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h24
  -- False on the left can always be used.
  apply False.elim h24



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_698217996316905233359189430914 : ((((((p3 ∧ p5) ∨ (p5 → (p5 ∧ (False → (p1 ∨ False))))) → p3) ∨ ((p2 ∨ (True ∧ p1)) ∨ ((False → p4) ∨ ((p1 ∨ False) ∨ True)))) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150796485178645750312521269876 : (((((False → ((((p2 ∨ (False → False)) → (p4 → True)) ∨ False) ∧ p2)) → (False ∧ p4)) ∧ (True ∨ p3)) ∨ p4) → ((p4 ∨ (p2 ∧ p3)) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h6 : (False → ((((p2 ∨ (False → False)) → (p4 → True)) ∨ False) ∧ p2)) := by
        -- Implications on the right can always be decomposed.
        intro h7
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- False on the left can always be used.
        apply False.elim h7
        -- False on the left can always be used.
        apply False.elim h7
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h8 := h3 h6
      -- We need to get the left conjuct of h8 based on <expert-advice>.
      let h9 := h8.left
      -- False on the left can always be used.
      apply False.elim h9
    case inr h10 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h11 : (False → ((((p2 ∨ (False → False)) → (p4 → True)) ∨ False) ∧ p2)) := by
        -- Implications on the right can always be decomposed.
        intro h12
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- False on the left can always be used.
        apply False.elim h12
        -- False on the left can always be used.
        apply False.elim h12
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h13 := h3 h11
      -- We need to get the left conjuct of h13 based on <expert-advice>.
      let h14 := h13.left
      -- False on the left can always be used.
      apply False.elim h14
  case inr h15 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h15
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328291347851160766168826054952 : (True → ((((True ∨ (((p1 ∨ False) → True) → False)) → (p4 ∧ p1)) → ((p3 → p5) ∨ ((p2 ∨ p2) → p4))) ∨ (p4 ∧ ((p1 → p2) ∧ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h5 : (True ∨ (((p1 ∨ False) → True) → False)) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h6 := h2 h5
    -- We need to get the left conjuct of h6 based on <expert-advice>.
    let h7 := h6.left
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h8 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h9 : (True ∨ (((p1 ∨ False) → True) → False)) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h10 := h2 h9
    -- We need to get the left conjuct of h10 based on <expert-advice>.
    let h11 := h10.left
    -- One of the premise coincides with the conclusion.
    exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45102123461099758210387550180 : ((((False ∨ p5) → ((p3 → (((p3 ∨ False) → (p5 → (p1 ∨ p1))) ∧ (((False ∨ p5) → True) ∨ (p2 ∨ (p2 → False))))) → True)) → p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313964133001472614407157356340 : (p3 ∨ (((p4 ∧ ((((p3 → ((p2 ∧ (p3 → False)) ∨ (p5 → p5))) ∧ (p1 → p3)) → p1) ∧ True)) ∨ ((p2 → p3) ∨ True)) ∨ (p3 → p2))) := by
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
theorem thm_5_vars_342801514850764037811310874143 : (p2 → ((p3 ∨ (p4 ∨ (p4 ∨ (p5 ∨ (p3 ∨ p4))))) → (False ∨ (p2 ∨ ((p4 → ((p3 ∧ (p1 ∧ (p3 ∧ (p1 ∨ p3)))) → p2)) ∨ p4))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h1
      case inr h8 =>
        -- Disjunctions on the left can always be decomposed.
        cases h8
        case inl h9 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h1
        case inr h10 =>
          -- Disjunctions on the left can always be decomposed.
          cases h10
          case inl h11 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h1
          case inr h12 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40658462871548197369844977091 : ((((((p4 ∨ (((p5 → p2) ∨ True) ∨ ((p5 → p2) → (((False → True) ∨ (p5 ∧ p3)) ∨ p4)))) ∨ p3) ∨ (p4 → p2)) → p5) ∨ True) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207350354652278969005677700357 : ((((True ∧ True) → (p5 → False)) ∨ p2) → ((p4 ∧ True) → (p5 ∨ ((p2 ∧ ((((True ∨ (False ∨ p2)) → (p4 ∧ p5)) → p3) ∧ False)) ∨ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55164468701494437726708898825 : ((((p4 ∨ (False ∨ (False ∨ False))) ∨ p5) ∨ ((p2 ∧ ((((p1 → p4) ∧ (False ∨ False)) ∧ (((p2 ∧ p2) → True) → p3)) ∧ p2)) → p5)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- Disjunctions on the left can always be decomposed.
  cases h9
  case inl h10 =>
    -- False on the left can always be used.
    apply False.elim h10
  case inr h11 =>
    -- False on the left can always be used.
    apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_126317146711473425409141124850 : ((p1 ∧ ((p1 → (p4 ∧ (True ∧ ((True → (False ∧ (p1 ∨ p1))) → (True ∨ (((p1 → False) ∧ p2) ∨ (p2 → p3))))))) ∧ p2)) → (p3 → p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67600538222805707985024064213 : ((p1 → (p1 ∧ ((((p1 ∧ p5) ∧ ((p2 → (False ∧ (((p2 ∨ ((p3 ∨ (p5 ∧ p2)) ∧ p4)) ∨ True) ∨ p5))) → False)) ∧ True) ∨ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114310783558664459060992516424 : (((((p3 ∨ (True ∧ p4)) → (p1 ∨ False)) ∨ ((p2 → ((True → p4) ∧ p1)) ∨ (p3 → p2))) ∧ ((p4 → (p1 ∧ p1)) ∨ p4)) ∨ (False → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58472177823618406707848054493 : (((p3 ∨ p5) ∧ (p1 → ((((p4 → False) → (False → ((p3 ∨ p4) → (p5 ∨ False)))) ∧ (p3 ∨ (True ∨ (p3 ∧ (p1 ∧ p3))))) → p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68609909950906373104623068317 : ((p4 → ((((p1 ∨ (p1 ∨ (((p5 → (p4 → p2)) → p2) ∧ ((p5 → p1) ∧ p1)))) ∨ ((p3 ∨ p3) ∨ True)) → (p1 ∧ p5)) ∨ p4)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_779174510464751783770931367181 : (((p2 ∨ (((((p5 → p4) → (((False ∨ ((p3 ∧ False) ∨ True)) ∨ (p4 ∧ (p4 ∨ (p4 ∨ p4)))) ∨ p5)) → True) → (True ∧ p5)) ∧ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337522181921265681445851398161 : (p1 → (((((p3 ∨ p4) → False) ∨ (False ∧ ((((p4 ∨ (p4 ∨ (p1 ∧ p4))) ∨ p4) ∨ True) → p3))) ∨ True) ∨ (True ∨ (False ∨ (False ∧ p4))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_14494071209572668864306297183 : ((((True ∧ ((p1 ∧ (True ∨ (True ∧ (((((True ∨ p5) → False) ∧ (p3 ∨ p2)) → (False → p4)) ∧ p2)))) → False)) ∧ p3) ∨ (True → True)) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118662714183677815111147911185 : ((p4 ∨ (p3 ∨ ((((((p3 → p5) ∧ (p4 → p4)) → ((True → (p4 → (True → False))) ∨ p5)) ∧ (True → p1)) → False) ∧ p5))) ∨ (p2 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_708999644968676203300445412188 : (((((p3 ∨ (p3 ∨ (p3 ∧ False))) → (p2 ∧ p5)) → (p4 → ((p2 ∧ True) ∨ (True ∧ (((True ∧ True) ∧ True) ∧ ((p1 → p4) ∨ p5)))))) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173360653253883715571659333376 : ((p3 → (((p2 → (True → p2)) ∨ p1) → ((p3 ∧ p5) ∨ (p2 ∧ (True ∨ p3))))) ∨ (p1 ∨ ((p5 ∨ p5) ∨ (((p1 ∧ p4) ∧ p3) → p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_728498873854272594896000108735 : ((((p3 → (False ∧ p2)) ∨ (p2 → (p4 ∨ (((((((p4 → p5) ∧ p4) ∨ True) ∨ True) → p3) ∨ (p4 ∧ p2)) ∨ ((p2 ∧ False) → p3))))) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_302527055323455775469931123339 : (False ∨ (False ∨ (((p3 → p2) ∧ True) ∨ (p1 → ((False → p4) → (p1 → (p4 → (((p2 ∧ ((p3 → p2) ∨ p2)) ∧ p5) ∨ (p5 → True))))))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323229279223528513559285530391 : (p5 ∨ ((((((False ∧ p5) → False) ∨ p4) → False) ∨ ((p1 ∧ ((p5 ∧ False) ∧ (p4 → ((True ∨ p5) ∧ True)))) → (False ∧ p5))) ∨ (p5 ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- False on the left can always be used.
  apply False.elim h7
  -- Conjunctions on the left can always be decomposed.
  let h8 := h1.left
  let h9 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h10 := h9.left
  let h11 := h9.right
  -- Conjunctions on the left can always be decomposed.
  let h12 := h10.left
  let h13 := h10.right
  -- False on the left can always be used.
  apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_608628936152049116548199382525 : ((((((p4 ∨ (((False ∧ True) → (((p4 ∨ (p5 ∧ p1)) → p1) ∧ True)) ∧ (False ∧ (p2 ∧ (p4 ∨ p4))))) ∧ (p4 → True)) ∨ True) ∨ p3) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321657368782923083452342273781 : (p4 ∨ (p4 → ((((p3 → (p2 ∧ p1)) ∨ ((False ∨ p4) → ((p1 ∧ (False → p5)) → (p4 → (True ∧ (p4 ∨ p4)))))) → (p4 → p2)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173181274641379064294386394683 : ((p4 ∨ (((p3 → True) → p1) ∧ (((p4 ∨ (p4 ∧ p4)) → p1) → (p3 ∧ p5)))) ∨ (((p2 ∨ (p5 ∨ p1)) ∨ (True ∧ True)) ∨ (p4 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112023443848576326283849890192 : ((((False ∨ (p1 ∧ False)) ∧ (((((True → (p1 ∧ (p3 ∧ (False ∧ True)))) → p4) ∨ (p5 ∨ p3)) ∧ p4) ∨ (p4 → False))) ∨ p5) ∨ (True ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185911464946402038122654339331 : ((((((p2 ∧ p4) ∧ False) → True) ∨ (p1 ∧ (p3 → False))) ∧ p2) → ((((p5 ∨ (p1 → (p3 ∨ (p5 → (True ∧ p2))))) → p3) → False) ∨ p2)) := by
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
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337084374046317316819855584136 : (p1 → (((((((((p4 ∨ p4) ∨ (p3 ∧ p5)) ∧ p2) → p2) ∨ (p5 ∧ p1)) ∧ False) → p2) → ((p3 ∧ p5) ∨ (False ∨ p3))) ∨ (False → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191753431240993266172282481967 : ((False ∨ (p3 ∨ ((p1 ∧ (p3 ∨ (p2 ∧ p5))) → p5))) ∨ (((p4 ∨ p5) ∧ (False ∧ p3)) ∨ ((True → p1) → ((True → p4) → (True ∧ p1))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62567471304940368276552164857 : ((p3 ∧ (True → ((((p4 ∨ (p2 ∨ False)) → ((True → p4) → (p1 ∨ True))) ∨ (p3 ∨ (p4 → (p2 ∧ ((p1 ∨ p5) → False))))) → p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197280310377838898436554972098 : (((((p5 → p4) → p5) ∨ (p1 ∨ p5)) → p4) ∨ ((p1 → ((p2 ∧ p1) → p1)) → (p2 → (((p3 → p5) ∨ False) → (True → (p4 ∨ True)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- False on the left can always be used.
    apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_102943797927820748502679160862 : (((((p2 ∨ (p5 → p3)) ∨ ((p1 ∧ ((p5 ∧ p2) ∧ False)) ∨ (True ∨ (True → False)))) ∨ (False → ((True → False) ∧ p5))) ∨ p2) ∧ (p3 ∨ True)) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138857936578497779310433153715 : (((p1 ∨ ((((p5 ∨ False) ∨ (((p1 → False) → p2) ∧ ((p2 ∨ True) ∨ p2))) ∨ ((p2 ∧ p2) ∨ p3)) ∧ p5)) ∧ p4) → (p3 ∨ (False ∨ p4))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Disjunctions on the left can always be decomposed.
        cases h9
        case inl h10 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h3
        case inr h11 =>
          -- False on the left can always be used.
          apply False.elim h11
      case inr h12 =>
        -- Conjunctions on the left can always be decomposed.
        let h13 := h12.left
        let h14 := h12.right
        -- Disjunctions on the left can always be decomposed.
        cases h14
        case inl h15 =>
          -- Disjunctions on the left can always be decomposed.
          cases h15
          case inl h16 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h3
          case inr h17 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h3
        case inr h18 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h3
    case inr h19 =>
      -- Disjunctions on the left can always be decomposed.
      cases h19
      case inl h20 =>
        -- Conjunctions on the left can always be decomposed.
        let h21 := h20.left
        let h22 := h20.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h3
      case inr h23 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h23



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115323407651783824930148885890 : ((((False → p1) ∧ (p3 → (((p1 → p2) ∨ p5) → p1))) → (p2 ∨ (False → (((p5 ∨ p4) ∨ (p5 ∧ (p2 ∨ p1))) ∨ False)))) ∨ (p3 → p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168282516935487088345992177835 : (((p3 ∧ p3) ∧ (((True → (p2 ∧ ((True ∧ True) ∨ True))) ∧ ((p3 → p1) → p5)) ∨ p4)) → (p5 ∨ ((p2 → ((p5 ∧ p4) ∧ p5)) ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_855930906187033414285287576837 : ((((((False → (p2 ∧ (p1 ∧ (((((False → p3) ∨ (True → ((p4 → False) → p2))) ∧ p4) ∨ p5) ∨ (True ∧ p1))))) → False) ∨ True) → p3) → p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((False → (p2 ∧ (p1 ∧ (((((False → p3) ∨ (True → ((p4 → False) → p2))) ∧ p4) ∨ p5) ∨ (True ∧ p1))))) → False) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207449199042918155487936859218 : (((p4 ∨ ((True ∨ False) → False)) ∨ False) → (p4 ∨ ((False ∨ ((True → ((p1 → (True → (False → p5))) ∨ p4)) ∨ (True → True))) → (p2 ∧ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h3 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h4 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h5 : (True ∨ False) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h6 := h4 h5
      -- False on the left can always be used.
      apply False.elim h6
  case inr h7 =>
    -- False on the left can always be used.
    apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150392652251473661420179413581 : (((((True → False) ∧ ((p2 ∨ True) ∨ (True ∧ (True → ((True → (p3 ∧ p5)) ∨ (False ∨ p4)))))) ∧ p2) ∧ p3) → (((p2 ∧ p4) ∨ True) ∧ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h14 := h1.left
  let h15 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h16 := h14.left
  let h17 := h14.right
  -- Conjunctions on the left can always be decomposed.
  let h18 := h16.left
  let h19 := h16.right
  -- Disjunctions on the left can always be decomposed.
  cases h19
  case inl h20 =>
    -- Disjunctions on the left can always be decomposed.
    cases h20
    case inl h21 =>
      -- We want to use the implication h18 based on <expert-advice>. So we show its premise.
      have h22 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h18, we can now drive its conclusion.
      let h23 := h18 h22
      -- False on the left can always be used.
      apply False.elim h23
    case inr h24 =>
      -- We want to use the implication h18 based on <expert-advice>. So we show its premise.
      have h25 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h18, we can now drive its conclusion.
      let h26 := h18 h25
      -- False on the left can always be used.
      apply False.elim h26
  case inr h27 =>
    -- Conjunctions on the left can always be decomposed.
    let h28 := h27.left
    let h29 := h27.right
    -- We want to use the implication h18 based on <expert-advice>. So we show its premise.
    have h30 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h18, we can now drive its conclusion.
    let h31 := h18 h30
    -- False on the left can always be used.
    apply False.elim h31



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244795003632223109185338310267 : ((p1 ∧ p1) ∨ ((((((p5 ∨ p1) ∨ p2) ∨ ((((p2 ∧ (p5 ∨ (p4 ∨ p5))) ∨ (p4 → p3)) ∧ (p4 ∨ p5)) ∧ p1)) ∨ p2) ∨ False) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305451117235712986389650538789 : (p1 ∨ ((False ∨ (p2 ∧ ((p1 ∨ (p1 ∧ False)) → (((False → p5) ∨ True) → (p4 ∧ p4))))) → (((False ∨ (p5 ∨ p4)) → (p5 ∨ False)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- False on the left can always be used.
    apply False.elim h2
  case inr h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_175216432277480985391700368186 : ((False ∨ (p5 → ((p4 ∧ ((((True → p2) ∨ (p1 → True)) ∨ p1) ∨ False)) ∨ False))) → (((p1 ∨ p2) → (p1 → p3)) → (p3 ∨ (True ∧ True)))) := by
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
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171339433937917691373499166179 : ((((((p2 → ((p2 ∨ p3) ∧ (False → p3))) ∨ (p1 → p3)) → True) → p5) ∧ p4) ∨ ((p5 ∧ (((False → p1) ∨ False) → False)) → (True → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h5 : ((False → p1) ∨ False) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h6
    -- False on the left can always be used.
    apply False.elim h6
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h7 := h4 h5
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133593337180200711145734432021 : ((((True → (((True ∧ (p4 ∨ p1)) ∧ (p4 → p3)) → (((p3 → p4) ∨ ((True ∧ p5) ∧ p3)) ∧ False))) ∨ True) ∧ False) ∨ (p4 ∨ (False → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111943768080975373916481993146 : ((((p2 ∧ (p2 → ((p5 ∧ p1) ∨ (p2 → (p4 ∧ p5))))) → (((p3 ∧ p3) ∧ ((True ∨ True) ∨ True)) → (False ∧ False))) ∨ True) ∨ (p2 ∨ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173006908303798080441454772856 : ((p5 ∧ (p2 ∧ ((True ∧ (True → ((p5 ∧ p2) ∧ (False ∧ (p4 → p5))))) → p1))) ∨ (p2 ∨ (((p3 ∧ p3) ∨ (p4 ∨ p4)) ∨ (p3 ∨ True)))) := by
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
theorem thm_5_vars_50245179819464380390663666656 : ((((((((p1 ∧ (p1 → p2)) → (p2 ∨ True)) → p1) → False) → ((p1 ∨ p3) → (True → p5))) → p4) ∨ (p3 ∨ ((p4 ∧ False) → p4))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_311863970513678418078207462708 : (p2 ∨ (p2 ∨ ((((p2 → (p2 ∧ ((p3 ∨ p5) ∨ ((((p2 ∧ p2) → ((p5 → p2) ∨ p4)) ∧ p3) → p4)))) ∨ (False → p1)) → p5) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112526075521764968916723553947 : ((((((False ∧ (True ∨ ((((p4 → False) ∧ p5) ∨ False) ∨ p4))) ∨ (True ∨ ((True → p1) ∨ p4))) ∧ (p4 → False)) → p1) → p4) ∨ (False → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58230067141235475593228627618 : (((p4 ∧ p4) ∧ (p4 ∨ (((((p5 ∧ (p4 → p3)) ∨ ((False → (p2 → (p1 ∨ (p4 ∨ True)))) ∨ (p3 → p1))) ∧ p1) ∨ p3) ∧ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309345271870349427782677800633 : (p2 ∨ (((((p2 ∧ p1) ∧ p3) ∧ (False ∨ (((p5 → (p2 ∨ (p1 → False))) ∨ p3) → False))) ∨ ((False ∨ (p5 ∨ False)) → p4)) ∨ (p3 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156916859415645163228946777502 : ((((((False ∨ (True ∧ p5)) → True) ∧ ((p4 ∨ ((p5 ∧ p2) ∧ (p1 → p2))) ∧ p3)) → p4) ∨ p2) ∨ (p2 → (p4 → ((p5 ∨ p2) ∨ p3)))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134024242145647851658409076679 : (((((p3 ∨ (p1 ∧ (False ∧ (p1 ∨ ((p2 → ((p4 ∨ p4) ∧ ((True ∧ p1) → True))) ∨ p4))))) ∨ True) ∨ p4) ∨ True) ∨ ((True ∧ p1) → False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192891000092998679017417040094 : (((p1 ∨ (False → (p2 → (p5 → True)))) ∧ (False → p3)) → (p2 ∨ ((((True → (p5 ∨ p3)) ∨ p2) → p1) → (False ∨ ((p4 ∨ True) ∨ p1))))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167559737181951263335670586736 : ((((((p2 ∨ False) ∨ (False → ((p4 ∨ p1) → p2))) → (True ∧ p5)) → True) ∨ (p2 → p3)) → ((p3 ∨ (((p2 ∨ True) ∧ p3) ∧ True)) → p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h4 =>
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h5 =>
      -- One of the premise coincides with the conclusion.
      exact h3
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h7.left
    let h10 := h7.right
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h12 =>
        -- One of the premise coincides with the conclusion.
        exact h10
      case inr h13 =>
        -- One of the premise coincides with the conclusion.
        exact h10
    case inr h14 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h15 =>
        -- One of the premise coincides with the conclusion.
        exact h10
      case inr h16 =>
        -- One of the premise coincides with the conclusion.
        exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_719643191657320061076125894224 : ((((p5 ∨ (True → (p4 → p5))) ∨ (((((p1 ∨ p5) ∨ p2) ∨ (False → ((True ∨ p2) → (p5 ∨ (False ∨ p1))))) ∧ (p1 ∧ p1)) ∧ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340811265471519275467595131959 : (p2 → ((((p2 → (p1 ∨ (((p3 ∨ p4) ∧ p3) ∧ (p4 → (p2 → (p3 ∨ p5)))))) ∧ (False ∧ (False ∧ (p2 → p4)))) ∧ (p2 ∨ False)) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55243648776010430127686100030 : ((((p1 ∨ p3) ∧ (p4 ∧ (p1 ∨ p4))) ∨ (p3 → ((False → (True ∧ p4)) → ((True ∨ (True ∨ p2)) → ((p4 → (p1 ∧ p5)) ∨ p5))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40404003156922023216693226951 : (((((p4 ∨ (p5 ∨ (((p2 ∧ False) ∨ ((False → (False ∨ (False → p3))) ∧ p2)) ∨ (True ∨ p2)))) ∨ (p3 ∨ (p3 ∧ True))) ∨ False) ∨ p2) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_348518243175180417351202417703 : (p3 → (p3 ∧ ((p4 ∧ p2) ∨ (((((False ∨ p4) ∧ p2) ∨ True) ∨ (((p5 → p5) → p3) ∧ (True ∧ ((False ∧ p3) ∧ True)))) ∧ (p3 ∧ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152691218553318787712400701387 : (((p2 ∧ p1) ∨ ((p2 ∧ ((False ∧ p2) ∧ (p3 ∨ False))) ∨ ((True → p2) ∧ (((False → p4) ∧ False) → p3)))) → (p2 ∧ ((p2 ∨ p5) ∧ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Conjunctions on the left can always be decomposed.
      let h11 := h9.left
      let h12 := h9.right
      -- False on the left can always be used.
      apply False.elim h11
    case inr h13 =>
      -- Conjunctions on the left can always be decomposed.
      let h14 := h13.left
      let h15 := h13.right
      -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
      have h16 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h14, we can now drive its conclusion.
      let h17 := h14 h16
      -- One of the premise coincides with the conclusion.
      exact h17
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h18 =>
    -- Conjunctions on the left can always be decomposed.
    let h19 := h18.left
    let h20 := h18.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h19
  case inr h21 =>
    -- Disjunctions on the left can always be decomposed.
    cases h21
    case inl h22 =>
      -- Conjunctions on the left can always be decomposed.
      let h23 := h22.left
      let h24 := h22.right
      -- Conjunctions on the left can always be decomposed.
      let h25 := h24.left
      let h26 := h24.right
      -- Conjunctions on the left can always be decomposed.
      let h27 := h25.left
      let h28 := h25.right
      -- False on the left can always be used.
      apply False.elim h27
    case inr h29 =>
      -- Conjunctions on the left can always be decomposed.
      let h30 := h29.left
      let h31 := h29.right
      -- We want to use the implication h30 based on <expert-advice>. So we show its premise.
      have h32 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h30, we can now drive its conclusion.
      let h33 := h30 h32
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h33
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h34 =>
    -- Conjunctions on the left can always be decomposed.
    let h35 := h34.left
    let h36 := h34.right
    -- One of the premise coincides with the conclusion.
    exact h35
  case inr h37 =>
    -- Disjunctions on the left can always be decomposed.
    cases h37
    case inl h38 =>
      -- Conjunctions on the left can always be decomposed.
      let h39 := h38.left
      let h40 := h38.right
      -- Conjunctions on the left can always be decomposed.
      let h41 := h40.left
      let h42 := h40.right
      -- Conjunctions on the left can always be decomposed.
      let h43 := h41.left
      let h44 := h41.right
      -- False on the left can always be used.
      apply False.elim h43
    case inr h45 =>
      -- Conjunctions on the left can always be decomposed.
      let h46 := h45.left
      let h47 := h45.right
      -- We want to use the implication h46 based on <expert-advice>. So we show its premise.
      have h48 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h46, we can now drive its conclusion.
      let h49 := h46 h48
      -- One of the premise coincides with the conclusion.
      exact h49



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324411868345226317228423202715 : (p5 ∨ (((p1 ∨ p4) → (p3 ∨ (p2 → True))) → (p5 → ((((True ∨ (p5 ∧ (True ∨ False))) ∧ (p5 ∧ (p5 → p3))) ∨ (True ∨ p3)) ∧ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199786836649353869121564348263 : (((((p1 ∧ True) ∨ False) ∧ p1) ∧ (p2 → True)) → (p3 ∨ ((((True → True) ∧ (p5 ∧ (True ∨ (p1 ∨ p4)))) → p2) ∨ ((p1 ∧ p4) ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h9 =>
    -- False on the left can always be used.
    apply False.elim h9



