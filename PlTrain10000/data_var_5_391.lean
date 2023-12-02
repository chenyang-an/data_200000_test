variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56444399801400258030040495957 : ((((True ∨ True) ∨ (p5 ∧ p5)) → ((False ∨ ((((p1 ∨ False) → ((((p2 ∧ p1) ∨ p2) → p4) → p4)) ∨ (p2 ∧ p3)) ∧ p4)) ∧ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258524152861513483258706269626 : ((p5 ∨ p3) → ((p2 ∨ ((False ∨ (p2 → p5)) ∨ ((p3 ∧ (((True ∧ p2) ∨ True) ∨ (((p2 ∧ (p3 ∧ p5)) ∧ p2) → p4))) ∨ p1))) ∨ True)) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197169989914690373971030302890 : ((((((p4 ∨ p2) → True) ∧ p1) ∧ p4) → p2) ∨ ((p4 ∧ ((((p1 ∨ p1) ∨ (False ∨ p5)) → p2) → p4)) ∨ (p3 → ((False → p2) ∨ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225040073760765152481946313253 : (((False ∧ p4) ∧ p1) ∨ (((((True → p1) ∨ (p4 ∨ (((p3 ∨ p3) → p4) ∧ (False ∧ True)))) ∨ p4) ∧ p1) ∨ ((p5 → (p5 ∧ p4)) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60822055869065725452359487878 : ((True ∧ (p5 ∧ (((p1 ∧ ((((p2 ∨ p5) ∧ True) ∨ True) ∧ (p1 → p2))) ∨ (((True ∨ p1) ∧ ((p4 → False) → p4)) ∨ p3)) → p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50459558139529550702609699714 : (((p4 ∨ (p3 ∨ ((p1 ∨ ((True ∧ ((p1 ∧ p2) ∨ ((p3 ∧ p3) ∧ (p1 ∧ p4)))) → p2)) ∨ p5))) ∨ ((p1 ∧ (True ∨ p5)) → True)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_704467435070174094142597168248 : ((((((p4 → True) → True) → (True → ((p5 → p3) ∨ p4))) → (((p1 ∨ ((p2 ∨ p3) ∨ ((p3 ∧ p2) → (p1 → p3)))) → False) → p5)) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (p1 ∨ ((p2 ∨ p3) ∨ ((p3 ∧ p2) → (p1 → p3)))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- One of the premise coincides with the conclusion.
    exact h6
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h8 := h2 h3
  -- False on the left can always be used.
  apply False.elim h8
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187217775188025505021682129981 : (((p1 → True) → (p3 ∨ ((p2 → ((p4 → p2) → False)) ∧ False))) → ((((False → p1) ∨ (p5 ∧ False)) → ((p4 ∧ (p5 → True)) ∨ p3)) ∨ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h4 : (p1 → True) := by
      -- Implications on the right can always be decomposed.
      intro h5
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h6 := h1 h4
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- False on the left can always be used.
      apply False.elim h10
  case inr h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- False on the left can always be used.
    apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118427623861507262077696812416 : ((p2 ∨ (p3 ∨ ((p4 ∨ p5) → (((p1 → (p1 ∧ p2)) ∧ (p3 ∧ p3)) ∨ (((p1 ∧ (p2 ∧ p1)) → (p1 ∨ p3)) ∨ p5))))) ∨ (p2 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_750614238683588404369627090526 : (((True ∧ ((((False ∨ ((True → p1) ∨ p3)) ∧ (p3 → ((False ∨ p2) ∧ False))) ∨ (True → p4)) ∧ ((p2 → (p1 → (False → p1))) ∧ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_609416250135658628803625154341 : ((((((True → False) → ((p2 ∧ True) ∨ (p4 ∨ (True ∧ (((((p1 → p4) → p1) ∧ ((p2 ∧ True) → p2)) ∨ p1) ∨ True))))) ∨ True) ∨ p4) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_255271441190381961867098896821 : ((p4 ∧ p5) → ((p3 ∨ (p5 ∨ p4)) ∧ (((((p5 → ((p4 ∨ False) ∨ p5)) → (p1 → ((True → p3) ∧ True))) ∧ (p3 → p4)) ∨ False) ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149230288935543771455512524073 : (((p4 ∧ p4) ∨ ((p2 ∧ ((((False → False) ∧ p3) ∨ p4) ∧ False)) ∨ ((True ∨ p2) ∧ ((p4 → p5) ∧ False)))) ∨ (True ∨ ((p5 → p4) → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234070481976144797559563282342 : ((True → (False ∧ p1)) → (((False ∨ ((((True ∧ True) ∨ ((p5 → (True ∧ p1)) ∧ (p3 ∧ True))) ∧ p4) ∧ (p5 ∧ (p1 ∧ p3)))) ∨ p1) ∧ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the left conjuct of h3 based on <expert-advice>.
  let h4 := h3.left
  -- False on the left can always be used.
  apply False.elim h4
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h5 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h5
  -- We need to get the left conjuct of h6 based on <expert-advice>.
  let h7 := h6.left
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66026566314396996678118949368 : ((p5 ∨ ((((p3 → (((False → p3) ∧ p4) → False)) ∧ p1) ∧ (((False ∨ (True ∧ (p1 ∨ ((p5 ∨ False) ∧ p5)))) ∨ True) ∨ p4)) ∧ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_704181002233863189873028657319 : (((((((p3 ∧ p3) ∧ True) ∨ (p2 → True)) ∨ (p2 → False)) → (p4 → (((((False ∧ (p4 → True)) → p2) ∧ p2) ∧ True) ∨ (p4 ∧ p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186379825765667699666736853468 : (((True ∧ ((p1 ∧ ((p1 ∧ p3) ∧ (False → p4))) → p1)) → p1) → (p4 → ((p4 → ((((p5 ∧ p4) → True) ∧ p3) → p1)) ∨ (p3 ∨ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h7 : (True ∧ ((p1 ∧ ((p1 ∧ p3) ∧ (False → p4))) → p1)) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Implications on the right can always be decomposed.
    intro h8
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- Conjunctions on the left can always be decomposed.
    let h13 := h11.left
    let h14 := h11.right
    -- One of the premise coincides with the conclusion.
    exact h13
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h15 := h1 h7
  -- One of the premise coincides with the conclusion.
  exact h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304979966932531764352344476577 : (p1 ∨ (((False ∨ (True → (p2 → (p3 ∧ (((p1 → False) ∧ p3) ∧ ((p2 ∨ p4) → ((p1 ∧ p4) ∧ p1))))))) ∧ p1) ∨ (True ∨ (p5 ∨ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208243519145386759864541866136 : (((p2 ∧ p1) ∧ (p4 ∨ (p3 → p2))) → (((p5 ∧ p1) ∧ ((True ∧ ((((p1 ∧ False) → p5) ∨ p5) ∨ (p5 → p2))) → (p2 ∧ p3))) ∨ p2)) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138344125862246155240823114447 : ((p4 → (((((((p3 → False) ∨ p5) ∧ ((((p3 → (False ∧ False)) → p1) ∨ p2) ∧ True)) ∧ p2) ∧ p5) ∨ p1) ∨ p3)) ∨ (True → (p3 → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_128010086219930696170342824686 : ((p1 → ((p2 ∨ (True ∨ (((p1 → p5) ∨ ((True ∨ (p4 → (False ∨ False))) → p3)) ∨ p1))) ∨ (((True ∨ p4) ∨ False) ∨ p1))) → (p3 → p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_216965849249152635735992557229 : (((p2 → (True → p3)) ∧ p2) → (p3 ∧ ((((((p2 ∨ True) ∧ (True → p4)) ∨ p3) ∧ False) ∧ (((p5 ∨ p1) ∨ p3) ∧ p4)) ∨ (False → False)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : p2 := by
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h6 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h7 := h5 h6
  -- One of the premise coincides with the conclusion.
  exact h7
  -- Conjunctions on the left can always be decomposed.
  let h8 := h1.left
  let h9 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h10
  -- False on the left can always be used.
  apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_343592137991360715056887849365 : (p2 → ((p2 → p3) → ((False ∧ ((((p5 ∧ (((p5 → p1) → (p4 ∨ p1)) ∨ False)) ∧ p2) ∨ (p3 ∨ p3)) ∨ (False ∧ p4))) ∨ (p5 → p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341761188257387411458367657751 : (p2 → ((p4 ∨ ((True → (p3 ∧ ((p4 → (((p2 ∧ p4) → (((p3 ∧ p4) ∨ (p1 ∧ p3)) ∨ p5)) → True)) ∧ p1))) → p4)) ∨ (False → p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263131464701018537132657439760 : (True ∧ (((p3 → ((p3 ∧ p1) ∧ (p4 → p4))) → ((((p5 ∧ (p5 ∨ p3)) ∨ ((p2 ∨ False) → (True ∧ p2))) ∨ True) → p4)) ∨ (p1 ∨ True))) := by
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
theorem thm_5_vars_156969353467713508642988843007 : (((((False → ((p5 ∧ p2) → (p2 ∨ False))) → (True ∧ p4)) ∨ (((p5 ∧ p3) → p2) ∨ p5)) ∨ True) ∨ ((p3 ∨ ((False → False) ∧ True)) ∨ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113895153429258242608065578299 : ((((((((p1 ∧ (((p3 ∧ (p4 → p5)) → (True ∨ p5)) ∨ True)) → p3) ∨ True) → False) ∧ True) → p4) ∧ (False → (False → p3))) ∨ (False → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_901950821729939772640624348826 : (((((((p3 ∧ p2) → p4) ∨ (((p3 ∨ False) → (p1 ∨ ((False → (True ∨ p3)) ∨ p2))) ∨ p2)) → p2) ∧ (p2 → (p3 ∧ (p5 → p1)))) → p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (((p3 ∧ p2) → p4) ∨ (((p3 ∨ False) → (p1 ∨ ((False → (True ∨ p3)) ∨ p2))) ∨ p2)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h7
      -- False on the left can always be used.
      apply False.elim h7
    case inr h8 =>
      -- False on the left can always be used.
      apply False.elim h8
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h9 := h2 h4
  -- One of the premise coincides with the conclusion.
  exact h9
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37150659970099518402502523448 : (((((((True → (False ∨ (((p4 → p1) → (True ∧ True)) → False))) ∧ p5) ∨ (p2 → (False ∧ False))) ∨ (p1 ∧ (p4 ∧ p4))) ∧ p2) ∧ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117682453450779787220933690748 : ((p3 ∧ (((False → (p4 → p5)) ∨ True) ∧ (((p4 ∧ False) → False) → (((False ∨ (False ∨ p4)) ∧ (p5 ∧ p3)) ∨ (p2 ∧ True))))) ∨ (True ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190931798408563766058984981606 : (((((False ∨ False) → p4) → False) ∧ ((p3 ∧ p1) ∨ False)) ∨ ((False → ((p3 → (p5 ∨ (p2 → p2))) ∧ (p1 ∨ True))) ∨ (p5 ∧ (p5 → p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111919275063595978345845999986 : ((((p5 → ((((False → p1) ∧ False) ∧ ((p2 ∨ p3) ∨ p2)) ∧ p4)) ∨ (((p1 ∧ (True ∨ False)) ∨ True) → (p5 ∨ True))) ∨ p1) ∨ (p5 ∨ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h6 =>
      -- False on the left can always be used.
      apply False.elim h6
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_311123028711809300917363797078 : (p2 ∨ ((p4 → p2) ∨ (((False ∨ p5) ∨ ((p5 → ((((p3 ∧ p2) ∨ (False → p4)) → p4) → ((p2 ∨ (p4 → True)) ∧ True))) ∨ p5)) ∨ False))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113205914234076790187290232304 : (((((((((p4 ∨ ((p5 ∨ p2) ∧ True)) ∧ p5) ∧ p5) ∨ (p1 ∨ p5)) → p4) ∨ ((True ∨ p5) → p3)) ∨ p1) ∧ (p1 → p2)) ∨ (False ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313211164586723945707790650522 : (p3 ∨ (((p2 → (True ∧ p1)) ∧ (((p5 ∨ (p4 ∨ (p5 ∧ (p3 ∨ p5)))) ∧ (p1 → ((p1 ∨ False) → ((p5 ∨ p3) ∧ p1)))) → p4)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115418613466413548999881595815 : (((((p4 ∨ (p1 ∧ p5)) ∨ (p5 ∧ p1)) ∧ p1) ∨ ((p2 ∨ True) → (p4 ∨ (p3 → ((True ∨ (p1 ∨ (True ∨ p1))) ∨ p1))))) ∨ (p5 → False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_701509952683091662328027281108 : ((((((p1 ∧ p5) ∧ p3) → ((True ∧ p3) ∧ (p4 ∧ True))) ∧ (((p5 ∨ p3) ∨ ((p3 ∨ (p3 → ((p5 ∨ p4) → p2))) ∨ True)) ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112228042437131368217765906746 : (((p2 ∨ (((((p1 → (True ∨ ((False ∧ (p1 ∨ p2)) ∧ False))) ∨ (p2 → (False ∧ False))) → (p3 ∨ False)) → p2) ∧ p4)) ∨ p1) ∨ (True ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39520511797619957479448026408 : (((False ∨ ((p3 ∨ (((False ∨ p3) ∧ (((((p3 ∨ p5) ∨ (p2 ∨ True)) ∨ (p2 ∨ True)) ∧ False) ∧ (p2 ∧ p3))) → p5)) → p3)) ∧ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256905030111169350104185998003 : ((p1 ∨ p4) → (((False ∨ p3) ∧ ((False → (p5 → (p2 → p1))) → p3)) ∨ (p5 → ((p2 ∨ (False → ((p4 ∧ True) ∧ (p3 ∧ p5)))) ∨ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- False on the left can always be used.
    apply False.elim h4
    -- True on the right can always be proven directly.
    apply True.intro
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- False on the left can always be used.
    apply False.elim h4
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- False on the left can always be used.
    apply False.elim h7
    -- True on the right can always be proven directly.
    apply True.intro
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- False on the left can always be used.
    apply False.elim h7
    -- False on the left can always be used.
    apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_163509585369472395076387848280 : (((p3 ∨ (p2 → True)) ∨ (False ∨ (True → ((p5 → ((p3 → (p5 ∨ p3)) ∨ p5)) ∧ p4)))) ∧ ((((p5 → (p2 → p2)) → p3) ∨ True) ∨ p5)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190908831819741136003562258283 : (((p1 → (True ∧ ((p2 → p2) ∧ True))) → (p3 ∨ p4)) ∨ ((False → ((p1 → ((((False ∧ (p2 ∧ p3)) → p3) ∨ p3) → p4)) ∨ p5)) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259505059728529512346117537085 : ((False → p5) → ((p4 ∧ (p3 → (((p3 ∧ (False ∨ p4)) ∧ ((((p3 ∧ p4) ∨ (False ∨ p5)) ∨ (p4 → False)) ∧ True)) ∨ p2))) ∨ (p2 ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_709458456169913781519994793526 : ((((p3 ∧ ((p4 → ((False → False) ∨ p1)) ∨ p3)) → ((((((p4 ∧ p2) ∨ p2) → p4) ∧ (True → (p1 → True))) ∨ p5) ∧ (p1 → p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314453584759037702110347142921 : (p3 ∨ (((((False ∧ p4) → p2) ∧ ((p3 → p2) ∨ ((((False ∧ (p3 → p1)) → False) ∧ p5) ∨ p1))) ∨ False) → ((p5 → p4) ∨ (p3 → True)))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
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
        -- Conjunctions on the left can always be decomposed.
        let h9 := h8.left
        let h10 := h8.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h11
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h13
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h14 =>
    -- False on the left can always be used.
    apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308489753538401428637678795294 : (p2 ∨ (((False ∨ ((p3 ∨ (((p3 ∨ p1) → p2) → (p2 ∧ (p2 ∨ p3)))) ∨ ((False ∨ True) ∧ (p3 → True)))) ∨ ((p5 ∧ p4) → p2)) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215731078558861459864908785107 : ((False ∨ (p3 ∨ (p5 ∨ p1))) ∨ (p2 → (p2 → (p2 → ((p1 → ((True ∧ True) → p3)) ∨ ((True → p5) → (((p1 ∨ p1) → p1) ∨ p1))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h5
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_357392604674031088084054937055 : (p5 → ((p4 ∧ p1) → (False ∨ ((True ∧ (True ∧ p3)) ∨ (p1 → (((False ∨ (((p1 ∨ p5) ∧ p1) ∧ p4)) ∧ p3) ∨ (True ∧ (False ∨ p5)))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h5
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197538660460416834859499010274 : (((((False ∨ p3) ∨ False) ∨ p5) ∨ (p4 ∨ p4)) ∨ ((p4 ∧ ((p5 ∨ p3) → (p1 → p4))) ∨ (((p1 ∨ True) ∨ (p3 ∨ p3)) ∨ (p2 → False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246668995689900212043161726872 : ((p5 ∧ p3) ∨ (p3 → ((((False ∨ (True ∨ (((True ∧ p3) → (p4 ∧ (p2 ∨ (((p5 ∧ p5) ∨ p5) → True)))) ∨ p4))) → False) ∨ True) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47986549477226750244316058513 : ((((p4 ∨ ((True ∧ ((p4 ∧ ((False → p4) ∧ p1)) → ((p3 → p1) ∧ True))) ∨ False)) → (((False → p4) → p3) → p5)) → (False ∧ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171495102416935387267980462171 : (((p3 → ((False ∧ p1) ∧ ((False ∧ ((p5 ∧ p5) ∨ p4)) ∨ (True → p4)))) ∧ p2) ∨ (p2 ∨ ((False ∧ (((True ∨ p2) ∨ p5) → p2)) → False))) := by
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
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57303971504605428690816044211 : ((((p5 → p2) → p1) ∨ (p1 → (((((p3 ∧ ((p2 → (p3 ∧ p1)) → True)) → (False → (p4 → True))) ∧ p4) → p3) ∨ (p1 ∧ True)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_108320777413790057788961629636 : ((True ∧ (p4 ∨ ((False ∧ (False ∧ ((False ∧ (p4 ∧ p3)) ∨ p4))) ∨ (((((False → p2) ∧ p1) ∨ p3) → True) ∧ (True ∨ p1))))) ∧ (True ∨ p1)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_616663133282752976089515236853 : (((((True → ((p1 ∨ p4) ∨ ((p1 → p1) → (p1 ∧ True)))) ∧ ((((p2 ∨ (p2 → p2)) ∧ p5) ∨ ((p2 → p1) ∨ False)) ∧ p5)) ∨ True) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_258279010891470882409471691988 : ((p5 ∨ True) → (((((p3 → False) ∧ (False → (p2 ∧ (False ∨ (p4 → p3))))) → p3) ∧ (p4 ∨ ((p3 ∨ False) ∧ ((p3 ∧ False) → p5)))) ∨ True)) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56226154920073202403138597126 : (((p3 ∨ (p4 ∧ (p3 → p2))) ∨ (((((True → p3) ∨ False) → ((p5 ∨ p5) ∨ (p5 → p2))) ∨ True) ∨ ((p5 ∧ (True ∧ p1)) ∨ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_745035864085802335429071535343 : ((((p4 ∧ p2) → ((p4 ∧ ((p1 ∧ (((p5 → (True ∨ p3)) → False) ∧ (False ∨ (((p2 ∧ p1) ∧ p3) ∧ False)))) ∨ (p3 ∨ p1))) ∧ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_595701555549204909225862181867 : (((((((p4 ∨ ((False ∧ p1) ∧ (p5 ∨ p2))) ∧ p1) ∧ p2) ∧ ((((p4 ∨ p2) → (p3 ∧ (True ∧ p1))) ∨ p3) ∨ (p1 ∧ True))) ∧ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_209069567198927521595600606491 : ((p1 ∨ (True ∨ ((p3 ∧ p1) ∧ False))) → ((p4 → ((p2 ∨ True) ∨ True)) → ((False → p1) ∧ ((p4 → ((p4 → (p1 ∧ p2)) ∨ True)) ∨ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h8
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- Conjunctions on the left can always be decomposed.
      let h12 := h10.left
      let h13 := h10.right
      -- False on the left can always be used.
      apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208929934602239049133586061296 : ((p5 ∧ (True ∨ (p4 ∧ (p1 ∨ False)))) → (p3 ∨ ((p2 ∨ (p1 ∨ ((p4 ∧ ((p2 → p1) ∨ (((True ∧ p4) ∨ True) → p5))) → True))) ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h10 =>
      -- False on the left can always be used.
      apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_86072578260232032494690820406 : (((p2 ∨ (p5 ∧ (p5 → ((p4 → (p3 → p3)) → True)))) ∧ ((True ∧ p1) ∧ (p1 ∧ ((p5 ∨ p1) → ((p3 ∨ (p4 → False)) ∧ False))))) → p5) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h6.left
    let h10 := h6.right
    -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
    have h11 : (p5 ∨ p1) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h9
    -- We have shown the premise of h10, we can now drive its conclusion.
    let h12 := h10 h11
    -- We need to get the right conjuct of h12 based on <expert-advice>.
    let h13 := h12.right
    -- False on the left can always be used.
    apply False.elim h13
  case inr h14 =>
    -- Conjunctions on the left can always be decomposed.
    let h15 := h14.left
    let h16 := h14.right
    -- Conjunctions on the left can always be decomposed.
    let h17 := h3.left
    let h18 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h19 := h17.left
    let h20 := h17.right
    -- Conjunctions on the left can always be decomposed.
    let h21 := h18.left
    let h22 := h18.right
    -- One of the premise coincides with the conclusion.
    exact h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58711539430577944687413890029 : (((p3 → True) ∧ ((p5 → ((False ∨ ((p1 ∧ p5) ∨ p3)) ∧ (p5 ∨ True))) ∨ (p3 ∧ (p5 ∨ (((True ∧ p4) ∨ p3) ∨ (p3 → p2)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_697275584859217839784574232863 : (((((p2 ∨ p4) ∧ (p3 ∧ ((p2 ∨ ((p3 ∨ p1) ∨ p3)) ∧ True))) ∧ (((p4 → (p1 ∧ (p4 ∨ p1))) ∨ True) ∧ ((True → p1) → p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_616285837099929106288857045661 : ((((((True → ((p1 ∧ (p4 ∨ (p1 ∧ p3))) ∨ p2)) ∧ (p3 ∨ True)) ∨ (p4 ∧ (((((p2 ∨ True) ∨ p4) ∨ p5) ∨ p5) → False))) ∨ True) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_51178614816947039402401579680 : (((((p4 → ((False ∨ p1) → (True ∨ p3))) ∨ ((p1 → p4) ∧ (p2 ∧ p5))) → (p1 ∧ p4)) ∨ (True → ((False → (p2 → p1)) ∨ p5))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_221511632833503255450728031770 : (((p2 → True) ∨ p4) ∧ (p5 → (p1 ∨ ((((p1 ∧ ((p3 ∧ True) → p4)) ∧ ((p3 ∨ ((True ∨ p5) ∧ p3)) ∧ False)) ∨ (p3 → p3)) ∧ True)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_653864247640539786842849069814 : (((((((p2 ∨ (p2 ∨ p3)) → p4) ∧ (((p2 ∨ (True ∨ False)) ∧ (p5 ∨ ((p3 → (p3 → p3)) ∨ p2))) → False)) ∧ p2) ∨ (p1 ∨ True)) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_115556735596677463385805101024 : ((((p5 ∨ (p5 ∧ (p1 ∧ p2))) ∧ p2) ∧ (p1 ∨ ((p1 → (((p1 ∧ ((p2 ∨ False) → p5)) ∧ False) ∨ p4)) ∨ (p4 ∧ p5)))) ∨ (p3 → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342407097711704300774969135687 : (p2 → ((p2 → ((p2 ∨ p3) → ((((False ∨ True) → p4) ∨ p3) → ((p1 ∧ False) ∨ p4)))) ∨ (p1 ∨ ((p1 ∨ (p2 ∨ (p4 → p5))) ∨ True)))) := by
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
theorem thm_5_vars_112074193636195589913809559415 : ((((True ∧ False) ∨ ((((p3 ∧ p5) ∨ (((p2 ∨ ((p3 → False) → p2)) ∨ p3) ∨ p3)) → p1) ∧ ((False ∨ p4) ∨ p4))) ∨ p3) ∨ (True ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_629688274595956779641636779623 : (((((((p3 ∧ p3) ∧ ((((p3 ∧ (p2 ∧ False)) ∧ (p4 ∨ p2)) → p4) ∧ (False ∧ p4))) ∨ ((p1 → p3) ∨ (True ∧ p5))) ∨ p5) → p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_196857505722776213648516561421 : (((p1 ∨ (p4 → (p1 ∨ (p2 ∨ False)))) ∧ p3) ∨ ((((p1 → True) ∧ p4) → (p5 ∧ p2)) ∨ ((p3 ∧ True) ∨ (p5 → (True ∨ (p5 ∨ False)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56146979347529500155050189256 : ((((True → p3) → (False ∧ p1)) ∨ (((((p2 ∨ p3) → p3) → p1) ∧ (p5 → (p3 → False))) ∨ (((p2 ∨ (False ∧ False)) → p5) ∧ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58924861731478849028370032123 : (((p1 ∧ p2) ∨ ((((True → p4) ∧ (p4 ∧ ((p1 → (p4 ∧ p3)) → p3))) → (False ∧ p1)) ∧ ((p2 ∧ p1) → (p5 ∧ (p3 ∨ p4))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161396472335250988387073599826 : ((p1 ∧ ((False ∧ (False ∧ (p2 ∧ p4))) ∨ ((p1 → (p1 ∨ p3)) → ((False ∨ True) → (p4 ∧ True))))) → (((p3 ∧ (p2 → p2)) ∨ p4) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- False on the left can always be used.
    apply False.elim h5
  case inr h7 =>
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h8 : (p1 → (p1 ∨ p3)) := by
      -- Implications on the right can always be decomposed.
      intro h9
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h9
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h10 := h7 h8
    -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
    have h11 : (False ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h10, we can now drive its conclusion.
    let h12 := h10 h11
    -- We need to get the left conjuct of h12 based on <expert-advice>.
    let h13 := h12.left
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h13
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249016518284521136682478884309 : ((p4 ∨ False) ∨ (((p4 ∧ False) ∧ False) ∨ (True ∧ (True → (((p5 → ((p1 ∧ (p1 → p1)) ∧ p2)) ∨ True) ∨ ((True ∨ False) ∨ (False ∨ True))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317937349237571004973585828020 : (p4 ∨ ((p2 ∨ ((((p2 → (p1 ∧ (False ∨ (p5 ∨ p5)))) ∧ p4) ∨ ((p4 ∧ (p2 ∨ p1)) ∧ ((p1 → True) ∧ (p5 → False)))) ∨ True)) ∨ p4)) := by
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
theorem thm_5_vars_340897144358788603072525720282 : (p2 → ((((False → p2) → (False ∧ (((True → (p4 ∧ True)) ∨ p1) → p3))) ∨ (p4 → ((True → p2) → (((p3 ∨ p5) ∨ p3) ∨ p2)))) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232027767606244365695227426040 : (((p3 ∨ p1) → True) → (((((p4 ∧ p3) ∧ p2) ∧ (False → (((True ∧ (p1 → (p1 ∧ False))) ∧ (p4 ∧ p3)) ∧ False))) ∧ (p1 ∨ False)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_769189329196111140418469325734 : (((p5 ∧ ((p3 ∧ p2) ∨ (((p2 ∨ p2) → (p1 ∧ (p1 → (p2 ∧ p1)))) ∨ ((p2 ∨ (((False ∨ (False ∨ p2)) → p2) → p5)) ∨ p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_749345007302645478347191361681 : (((True ∧ (((p1 ∨ (((p4 → (((False → (p2 ∨ p2)) → p5) → ((((True ∧ p2) ∨ p5) → True) → p1))) ∨ True) ∨ p3)) ∧ p1) ∧ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_612664972534270289594363460078 : (((((((((False → (((p3 → p5) ∧ p1) → p5)) ∧ p3) ∧ p2) ∨ (p2 ∧ p5)) ∧ (((p4 → p2) ∧ p5) ∨ p4)) ∨ (p4 → True)) ∨ p2) ∨ p3) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42056219453099099011086857636 : ((((p2 ∨ p4) ∨ ((p1 ∨ (p3 ∧ p1)) ∨ ((True ∧ p2) → ((p1 ∨ (p5 ∧ (p4 ∧ ((p5 → p1) → (p3 ∨ True))))) ∨ True)))) ∨ False) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53797805522112321982877755684 : (((((((p1 ∨ p2) → p1) → p2) → (p4 ∧ p1)) → p2) ∨ (p2 ∨ (p4 → (((True → False) → True) ∨ (True ∧ ((p1 → p2) → p3)))))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54952258935754685678594941184 : (((((p1 ∨ True) ∧ p2) ∨ (p1 ∧ p5)) ∧ (((p5 → (((p3 → p4) ∨ p4) ∨ ((False ∨ (p2 → p3)) ∨ p5))) ∧ (p5 ∧ p1)) ∨ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259552427110220915810739390999 : ((p1 → True) → ((((True → ((p2 ∨ (p2 ∨ ((False ∧ ((True → True) → p2)) ∨ (p1 ∨ False)))) → (p5 → p3))) → (True ∧ p5)) ∨ True) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_701696605495284542609721314570 : (((((p3 → p4) → ((p2 → (p4 ∨ (p3 ∧ p2))) → False)) ∧ (((p1 → (p1 ∨ p3)) → p4) ∨ ((False ∨ False) ∨ (p3 → (False → False))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_659016855907890180775214166327 : ((((p1 → ((p3 ∨ p5) → (((((p5 ∧ (p5 → ((p2 ∧ p2) ∨ p4))) ∧ (True ∧ False)) ∧ (p2 ∧ False)) ∨ p1) ∧ True))) ∨ (False ∧ True)) ∨ p3) ∧ True) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354079680928024643839635662162 : (p4 → (p5 → (((((((((p2 ∧ True) ∨ True) → (True ∧ False)) → (False ∧ False)) → False) → p4) ∧ (p2 → p1)) → (p1 → (True ∧ False))) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_238223904862905189593724738624 : ((True ∨ p4) ∧ (p5 ∨ (((((p1 ∧ (p5 ∧ p5)) ∨ p1) → ((False ∧ p3) ∨ p4)) ∨ (True ∨ p2)) ∨ (((p5 → False) ∧ (p5 ∧ p4)) → True)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
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
theorem thm_5_vars_918834613662013690696768159502 : ((((((((True ∨ (False → True)) → p5) → (p3 ∨ (p3 → p5))) ∨ p1) → False) ∧ ((False ∧ p1) → (((p3 ∨ True) ∧ p3) ∧ (p3 ∧ False)))) → p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : ((((True ∨ (False → True)) → p5) → (p3 ∨ (p3 → p5))) ∨ p1) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h7 : (True ∨ (False → True)) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h8 := h5 h7
    -- One of the premise coincides with the conclusion.
    exact h8
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h9 := h2 h4
  -- False on the left can always be used.
  apply False.elim h9
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114895840638105073073740089269 : (((p4 ∨ (p2 ∨ (((False ∧ True) ∨ (((p3 → True) → p1) → True)) → p4))) ∨ (((False ∧ p5) → (p2 → (True → False))) ∨ p4)) ∨ (p2 ∧ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41121235677283032769130916320 : ((((p2 → (((p4 ∨ p5) → ((p4 ∧ p5) ∨ (p4 ∧ p3))) ∧ (((p5 → False) ∨ (p3 ∨ False)) ∨ p2))) ∧ ((p5 → p2) ∨ True)) ∨ True) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_621077302251894877868881647917 : (((((p2 → p4) → ((p2 ∨ p5) ∨ (False ∧ (p3 ∨ ((((True → p4) ∧ True) ∨ p4) → (((p5 → p4) ∧ p3) ∨ (p4 → True))))))) ∨ True) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_344514636773486130893941820536 : (p2 → (True → (p3 ∨ ((p3 ∨ p3) → (((((p2 → (p3 → ((p2 ∧ False) ∧ ((False ∨ p4) ∧ True)))) ∨ True) ∨ False) ∨ True) ∧ (p2 ∨ p1)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h6 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h7 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47590043109315132420319932376 : (((p2 → ((p1 ∨ p3) → ((False → ((p2 ∧ (((p4 ∧ True) ∨ p2) ∧ (True ∧ p3))) → p1)) → (True → (p4 ∧ p2))))) ∨ (p1 ∨ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231413685292400494073176792330 : (((p1 → p3) ∨ p4) → ((p4 ∧ p2) ∨ ((p1 → True) → (((False ∧ p4) ∨ ((((p3 ∨ False) ∧ p3) ∧ p5) ∨ False)) ∨ ((False → True) ∧ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h4
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h7
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61796736145117554190140894650 : ((p2 ∧ (((((p4 ∨ False) ∨ (p2 → True)) ∧ (p2 ∧ (((p1 ∨ p5) ∨ (((False ∨ True) ∧ False) → p3)) → (p4 ∧ p4)))) ∧ p5) ∨ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338096144696927543431497830663 : (p1 → (((p5 ∨ ((p2 → (p4 → True)) ∨ p2)) → p1) ∧ (p5 ∨ (((((((p3 → p3) → p2) ∧ p3) ∨ (p4 ∨ True)) ∨ p5) ∨ p3) ∧ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h6 =>
      -- One of the premise coincides with the conclusion.
      exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



