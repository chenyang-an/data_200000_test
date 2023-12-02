variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67346083371097316172280458518 : ((p1 → (((p4 ∧ (p4 ∨ p1)) → (((p1 ∨ True) → (p4 → (((p4 → p1) ∨ ((False ∨ p4) ∨ False)) ∧ p3))) ∨ (p4 → False))) ∨ True)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310381849099019808397411590969 : (p2 ∨ ((((False ∨ p3) ∧ ((p5 ∧ True) → False)) ∧ p2) ∨ ((p5 ∨ ((False ∧ p4) ∨ p2)) ∨ (((p4 ∧ p1) → p4) ∨ (p5 ∧ (p2 → p5)))))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_624767660903584197966759909823 : ((((p5 ∨ ((((((((p3 ∨ True) ∧ p2) ∨ ((p3 ∨ p3) ∧ p3)) → ((False ∧ p3) ∨ p4)) → False) ∧ (False ∨ True)) ∧ p2) ∨ p1)) ∨ True) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_245586535820614031488305925533 : ((p3 ∧ False) ∨ (((True → ((p2 ∧ (p1 → p1)) ∨ (False ∧ ((False → True) ∧ p5)))) ∧ (((((p2 ∧ p1) → p3) ∧ p2) ∨ p5) ∧ p1)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179157779428133288438652055612 : ((p2 ∧ (((False ∨ (p4 ∨ (p5 ∧ p3))) ∨ True) ∧ (False ∨ (p1 ∨ False)))) ∨ (p4 ∨ (((p2 ∧ p1) → p1) ∧ ((p3 ∧ (p4 ∨ p5)) → True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305300651696825581401740815997 : (p1 ∨ ((((True ∧ (((p5 ∧ p4) ∧ p3) ∨ p5)) ∨ (p4 → True)) ∧ (p1 ∧ (p4 ∧ (p2 ∧ p2)))) ∨ ((True ∧ False) → ((p2 → p5) → p1)))) := by
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
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178670401656365664589692461648 : (((p1 ∧ (p4 → (p1 ∨ p5))) ∧ ((True ∨ (True ∨ p1)) ∧ (True → p4))) ∨ (p2 ∨ ((False ∨ (True → (p4 ∨ True))) ∧ ((False → False) ∨ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191145647654246070513438073228 : ((((p5 ∨ p1) ∨ p3) ∨ (True ∧ ((True ∨ p3) → False))) ∨ (((((p4 → p3) → (p2 → p5)) ∨ p1) → True) ∨ (p3 → (p4 ∧ (p2 ∨ p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354324751838832288814911710840 : (p5 → ((((p5 → (p4 ∧ ((True ∨ p2) → p1))) ∧ (p5 → (p2 → ((p5 ∨ p1) → True)))) → (((False ∧ p2) ∨ p1) → (p5 → p1))) ∧ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- False on the left can always be used.
    apply False.elim h6
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h2.left
    let h10 := h2.right
    -- One of the premise coincides with the conclusion.
    exact h8
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168948631334891847598526441958 : ((True → (p5 ∧ ((p3 ∨ (((p4 ∧ True) ∨ (p5 ∨ False)) → p1)) ∧ ((p4 ∧ False) ∨ p5)))) → (((p5 → p2) → p1) ∨ ((p3 → True) ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57299794537759425393452527740 : ((((p4 → p1) → p2) ∨ (((((p2 ∨ p1) ∧ True) ∧ (((False ∨ True) ∨ True) → ((p3 → False) ∧ True))) ∨ (True → (p2 ∧ p5))) → p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249288932160475097525272749656 : ((p4 ∨ p5) ∨ ((((((p3 ∧ (True → (((p5 ∧ p5) → p3) → (((p5 ∨ True) ∧ p4) ∧ p5)))) → (p1 ∨ p4)) → False) ∧ False) ∨ True) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65890778236552227057308259337 : ((p4 ∨ (True ∧ ((((p4 ∧ (p1 → True)) ∧ ((False → p5) → (p1 → p2))) ∧ (p3 → p2)) ∧ (((p4 → p1) ∧ (True → p5)) → False)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336089074629292219566835989856 : (p1 → (((((True ∨ p5) ∨ p3) ∧ (p1 → ((p1 ∨ (((p1 ∧ False) ∨ p2) ∨ (True ∨ p5))) → ((True ∧ False) ∧ (p5 ∨ p1))))) ∧ True) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51866255350874453433934304757 : (((((p3 ∧ ((((p2 ∧ p4) ∧ True) ∧ p3) ∧ p3)) ∧ (p3 ∧ (p1 ∧ True))) ∨ True) ∨ (p1 ∧ (((False ∨ p1) → (p1 ∨ p5)) ∨ p3))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149897666897268912903034035987 : ((p2 ∨ (False ∨ (p4 ∨ (p2 ∨ (p2 ∨ ((p4 ∨ (p1 ∨ (p3 → ((p1 → p3) → True)))) ∨ (p1 ∨ p4))))))) ∨ ((True → p3) ∧ (True ∧ p4))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63269326557822454008161969138 : ((p5 ∧ (((True → (True ∧ (p3 ∨ p1))) ∧ p4) → ((((True → p2) ∨ (p5 ∧ p1)) → p5) ∨ (((p1 ∧ p4) ∨ p2) → (p3 → p3))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351529281382394922492215084476 : (p4 → (((((p4 ∨ p3) → (p2 ∧ (p5 → (p5 ∨ p2)))) → (p1 ∧ p3)) ∧ (p1 ∨ (p2 ∨ True))) ∨ ((((p2 ∨ p3) ∧ p4) → p2) → p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113466096094868437197342427307 : (((((True → p5) → ((p5 → (p2 ∧ p5)) → ((((p5 ∨ p2) → ((p1 ∨ p5) → p3)) ∧ True) ∧ False))) → p4) ∨ (p1 ∨ p2)) ∨ (False → False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178229891118204548785036718164 : (((p2 → (p5 → (((True ∧ p3) ∧ p4) ∨ (p5 ∨ (p1 ∧ p4))))) → False) ∨ (True ∨ (((False ∧ ((p1 ∧ p1) ∨ p1)) ∨ (p3 ∧ p1)) ∧ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_264960639726175299753445817628 : (True ∧ ((p2 ∨ p2) → (True → (((p4 ∧ p2) ∨ (((p4 ∨ p2) ∨ True) ∧ (((True ∨ (p1 ∨ p2)) → p4) → (p4 ∧ True)))) ∧ (p2 ∨ p3))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h5 : (True ∨ (p1 ∨ p2)) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h6 := h4 h5
    -- One of the premise coincides with the conclusion.
    exact h6
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
    -- Implications on the right can always be decomposed.
    intro h8
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
    have h9 : (True ∨ (p1 ∨ p2)) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h8, we can now drive its conclusion.
    let h10 := h8 h9
    -- One of the premise coincides with the conclusion.
    exact h10
    -- True on the right can always be proven directly.
    apply True.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h11 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h11
  case inr h12 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111571746606883619743626201484 : (((((False ∧ p5) ∧ ((p3 ∧ (p2 → (((p2 ∧ False) ∨ ((p5 → (False ∨ p2)) → p1)) → (p4 ∧ False)))) ∧ p5)) ∧ p2) ∨ True) ∨ (p1 → p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_560369660189622965989029155 : (((p3 ∨ ((p2 ∨ ((p3 ∨ p3) ∧ (True ∧ ((p4 ∨ (False ∧ p2)) ∧ p1)))) ∨ (p4 → ((p4 → p5) ∨ (p5 ∨ p5))))) ∨ True) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_85950552257187348729351332116 : ((((((p2 ∧ True) ∨ p5) ∨ ((p5 ∧ p4) ∧ p3)) → p1) ∧ (((p4 → (((p2 ∧ p5) ∨ p3) ∨ ((p5 ∨ True) ∨ p3))) → False) ∧ p1)) → p3) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h6 : (p4 → (((p2 ∧ p5) ∨ p3) ∨ ((p5 ∨ True) ∨ p3))) := by
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
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h8 := h4 h6
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190909552436952401677632076434 : (((p2 → (((p5 ∧ False) ∨ p1) ∨ False)) → (p2 ∨ p2)) ∨ ((((p4 ∨ ((True ∨ p4) → p3)) ∨ p1) ∨ (True → ((p1 ∨ p1) → p1))) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171423672313250209331678394244 : ((((p4 ∨ False) ∧ ((False ∨ ((p2 ∧ (p3 ∨ p5)) ∨ p2)) ∨ (p3 → True))) ∧ True) ∨ (p4 → ((p2 → (p4 ∨ False)) → (p1 → (True ∧ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167279241175985341814444081911 : (((((p2 ∨ (((False ∨ p1) ∨ (p4 ∧ (p5 → p5))) ∨ p4)) ∧ (False ∧ p3)) ∨ p1) → p5) → (p4 → ((p4 → (p2 ∧ (False ∧ p2))) → p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : p4 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- We need to get the left conjuct of h6 based on <expert-advice>.
  let h7 := h6.left
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_748854788299300879909737668483 : ((((p4 → p1) → ((((((p3 ∧ p5) ∧ p3) ∧ ((True ∧ ((True ∨ (False ∧ p1)) ∧ (p3 ∧ (p1 → True)))) → p4)) ∨ True) ∧ p5) ∨ True)) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_118875738542370805349162075640 : ((True → ((p1 ∧ p5) ∨ (((False ∧ (p5 ∧ (p5 → p1))) → (p2 → True)) → (((True ∨ p2) → (p1 → (p3 ∧ p5))) ∨ p5)))) ∨ (False → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58121587920524675750438896766 : (((p2 ∧ True) ∧ (((p1 ∧ (p3 → p3)) → p2) → ((p1 → (p5 ∨ (((p5 ∧ True) → (((p1 → True) ∧ True) ∧ True)) → False))) ∧ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321697944831759882591700909995 : (p4 ∨ (p4 → (p4 ∧ ((True ∨ (((p1 ∧ ((((p5 ∨ p4) ∨ True) ∨ (p5 → (False ∨ p4))) ∨ p3)) ∨ p4) ∨ (p4 ∧ p4))) → (False ∨ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Conjunctions on the left can always be decomposed.
        let h7 := h6.left
        let h8 := h6.right
        -- Disjunctions on the left can always be decomposed.
        cases h8
        case inl h9 =>
          -- Disjunctions on the left can always be decomposed.
          cases h9
          case inl h10 =>
            -- Disjunctions on the left can always be decomposed.
            cases h10
            case inl h11 =>
              -- Disjunctions on the left can always be decomposed.
              cases h11
              case inl h12 =>
                -- Show the right disjunct based on <expert-advice>.
                apply Or.inr
                -- True on the right can always be proven directly.
                apply True.intro
              case inr h13 =>
                -- Show the right disjunct based on <expert-advice>.
                apply Or.inr
                -- True on the right can always be proven directly.
                apply True.intro
            case inr h14 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- True on the right can always be proven directly.
              apply True.intro
          case inr h15 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
        case inr h16 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h17 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h18 =>
      -- Conjunctions on the left can always be decomposed.
      let h19 := h18.left
      let h20 := h18.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317776645516780224555954141983 : (p4 ∨ (((p1 → ((p1 ∨ (p2 → (((p1 ∧ p2) → False) ∨ p5))) ∨ (p5 ∧ p2))) → ((False ∧ (True ∧ ((True ∨ p5) ∧ p4))) ∧ p3)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314018625752278463971947935807 : (p3 ∨ ((p1 ∨ (((False → (True ∧ p4)) ∧ p3) ∧ ((p2 ∨ ((((p4 ∧ p1) ∨ p3) ∨ (p5 ∧ False)) → False)) ∨ (p3 → p4)))) ∨ (False → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135771395814980139149882339657 : ((((((((p5 ∨ p1) ∨ (False → p5)) ∨ p3) → (p3 ∨ p2)) ∧ p5) ∨ p2) → ((False ∧ (p4 ∧ (p2 ∧ p1))) ∨ True)) ∨ ((p1 ∨ p1) ∨ p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134708576368411993561432708986 : ((((p3 → (p4 ∧ (p3 ∧ False))) → (p2 ∧ ((False ∨ True) → (p5 → (True → (((False ∧ p2) ∧ p3) ∨ p2)))))) → p3) ∨ (p3 ∨ (False → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_327847991907735314683933517504 : (True → (((p3 ∨ ((((p2 ∨ p1) → p5) ∨ p1) ∨ (p2 → p2))) → ((((True ∧ (p1 ∨ (p3 ∧ p5))) ∨ p1) ∧ True) ∨ p2)) ∨ (p4 → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52447421563890306843560935502 : (((p2 ∧ ((p1 → p5) → ((True ∨ p2) ∨ (False ∧ (p5 ∨ (False ∨ p4)))))) ∧ (((p5 ∨ p2) ∨ False) → (p2 ∨ (p1 → (p3 ∨ p4))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_613470691221046522086063598891 : (((((True → ((((True → (p2 → ((False ∧ (p3 ∧ p2)) ∨ ((True ∧ p3) ∨ p4)))) → (True ∧ p3)) ∧ p3) ∧ False)) → (True ∧ p1)) ∨ p3) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- False on the left can always be used.
  apply False.elim h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_702673266563496322008659446933 : (((((p1 ∧ ((True ∨ True) ∧ (p2 ∨ p3))) ∧ (False → p1)) ∨ (((((p4 ∧ p2) ∧ p3) ∧ (p1 → False)) ∨ (p5 ∨ (p5 ∧ p4))) ∧ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111240136412075412943625712451 : ((((True → True) ∧ ((p4 ∨ (p1 ∨ (((((p5 → p2) ∨ (p4 ∨ p4)) ∨ p4) ∨ ((p5 ∧ False) → p5)) ∨ p1))) ∧ True)) ∧ p4) ∨ (p1 → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148439862212872031574841872513 : (((p5 ∨ (False ∨ (((((p2 ∨ p2) ∧ (False ∧ p1)) ∨ p2) → True) ∧ p3))) → (p1 ∨ ((p2 → False) ∧ p1))) ∨ ((False → (True ∧ p1)) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181525158740053958214120878092 : ((True → ((p4 ∨ ((False ∨ p2) → ((p3 → p4) → p5))) ∧ (p5 ∧ True))) → (p4 ∨ ((p3 → ((p5 ∨ True) → (False ∨ (p2 ∨ p1)))) ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_780190667515492095895960267627 : (((p2 ∨ (((p1 → (p5 ∧ ((p1 ∨ ((p4 ∨ True) → False)) → (False ∧ (False → ((p1 ∨ False) → p5)))))) ∨ False) ∨ ((True ∧ True) ∧ True))) ∨ p5) ∧ True) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345994564996317699091557807164 : (p3 → ((((p2 ∨ p3) → False) ∧ ((((((False → False) ∧ p1) ∨ (p1 ∧ (p4 ∨ (True ∧ True)))) ∧ p3) ∨ (p3 ∧ (p1 ∧ p5))) → True)) → p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h5 : (p2 ∨ p3) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h5
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_700198763853893373067256508229 : (((((False → True) ∨ (p1 ∧ ((p1 → (False ∨ (p3 ∧ True))) → p5))) → ((((p2 ∧ (p4 → p2)) → False) ∧ ((p2 ∧ p2) ∨ False)) ∨ True)) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_90506523100402736292217650812 : (((p2 ∧ p3) ∧ (p3 ∧ (p3 → ((p1 ∧ p1) ∧ (p3 ∧ ((True ∧ p3) → ((((True ∧ (p4 ∨ False)) ∧ False) → (p5 → True)) ∧ False))))))) → False) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h3.left
  let h7 := h3.right
  -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
  have h8 : p3 := by
    -- One of the premise coincides with the conclusion.
    exact h6
  -- We have shown the premise of h7, we can now drive its conclusion.
  let h9 := h7 h8
  -- We need to get the right conjuct of h9 based on <expert-advice>.
  let h10 := h9.right
  -- We need to get the right conjuct of h10 based on <expert-advice>.
  let h11 := h10.right
  -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
  have h12 : (True ∧ p3) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- One of the premise coincides with the conclusion.
    exact h6
  -- We have shown the premise of h11, we can now drive its conclusion.
  let h13 := h11 h12
  -- We need to get the right conjuct of h13 based on <expert-advice>.
  let h14 := h13.right
  -- False on the left can always be used.
  apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310523506144473613922443475797 : (p2 ∨ (((True → ((p4 ∧ p5) ∧ p1)) ∧ p2) → ((((False → (False ∧ True)) → True) ∨ (p5 ∨ ((p3 ∧ p4) ∧ p1))) → ((p1 ∧ p4) ∨ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h1.left
    let h5 := h1.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h6 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h7 := h4 h6
    -- We need to get the right conjuct of h7 based on <expert-advice>.
    let h8 := h7.right
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h1.left
      let h12 := h1.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
      have h13 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h11, we can now drive its conclusion.
      let h14 := h11 h13
      -- We need to get the right conjuct of h14 based on <expert-advice>.
      let h15 := h14.right
      -- One of the premise coincides with the conclusion.
      exact h15
    case inr h16 =>
      -- Conjunctions on the left can always be decomposed.
      let h17 := h16.left
      let h18 := h16.right
      -- Conjunctions on the left can always be decomposed.
      let h19 := h17.left
      let h20 := h17.right
      -- Conjunctions on the left can always be decomposed.
      let h21 := h1.left
      let h22 := h1.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148310378079750989364439067452 : (((p1 ∧ (((p4 → ((((p3 ∨ p4) ∧ (p4 → False)) ∧ False) → p4)) ∧ p5) → False)) → (p3 ∧ (p2 ∨ p5))) ∨ (p4 → (False → (p1 → p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115612490970636070038937871005 : (((p3 ∨ ((p4 ∨ p2) ∨ (p3 ∨ True))) ∧ ((False ∨ ((p4 → (True ∨ p2)) ∨ (p4 ∧ (True → (p4 ∧ (True ∨ True)))))) ∧ True)) ∨ (p4 ∨ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198727613928751165826219336575 : ((p5 ∨ (p3 ∧ (p1 ∧ ((p3 ∧ p4) ∧ p5)))) ∨ (((p3 ∨ (((False ∨ p3) ∨ (p5 ∨ p5)) ∨ p3)) ∨ p4) → (False ∨ ((p2 ∧ False) → p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- False on the left can always be used.
      apply False.elim h6
    case inr h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Disjunctions on the left can always be decomposed.
        cases h8
        case inl h9 =>
          -- Disjunctions on the left can always be decomposed.
          cases h9
          case inl h10 =>
            -- False on the left can always be used.
            apply False.elim h10
          case inr h11 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h12
            -- Conjunctions on the left can always be decomposed.
            let h13 := h12.left
            let h14 := h12.right
            -- False on the left can always be used.
            apply False.elim h14
        case inr h15 =>
          -- Disjunctions on the left can always be decomposed.
          cases h15
          case inl h16 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h17
            -- Conjunctions on the left can always be decomposed.
            let h18 := h17.left
            let h19 := h17.right
            -- False on the left can always be used.
            apply False.elim h19
          case inr h20 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h21
            -- Conjunctions on the left can always be decomposed.
            let h22 := h21.left
            let h23 := h21.right
            -- False on the left can always be used.
            apply False.elim h23
      case inr h24 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h25
        -- Conjunctions on the left can always be decomposed.
        let h26 := h25.left
        let h27 := h25.right
        -- False on the left can always be used.
        apply False.elim h27
  case inr h28 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h29
    -- Conjunctions on the left can always be decomposed.
    let h30 := h29.left
    let h31 := h29.right
    -- False on the left can always be used.
    apply False.elim h31



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_804613994695916430529627137511 : (((p3 → (((p2 ∧ (False ∨ p1)) ∧ p1) ∨ ((p5 ∧ p1) ∧ ((True → True) → ((p3 ∧ (((p4 → (p4 → p4)) ∨ p3) ∧ p4)) ∧ p5))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135289216581437671963167259873 : (((p4 → (p1 → ((p4 ∨ (p3 ∧ p3)) ∧ (((p5 ∨ (True ∨ p5)) → ((p2 ∧ True) → False)) ∨ p5)))) → (p3 ∧ True)) ∨ (True ∨ (p2 → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172171927199089648519343648443 : (((((p3 ∨ p3) → p2) → ((p3 ∨ (p5 ∨ p4)) → p4)) ∨ (True → (p1 → p1))) ∨ (p5 ∨ ((p3 ∧ (p3 → p4)) ∨ (False ∨ (p5 ∨ p1))))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_749827124524900698444095602220 : (((True ∧ ((False ∨ ((((((p1 ∧ ((p5 ∧ (p2 ∨ p5)) ∧ (p1 ∨ p1))) ∨ False) ∨ ((p2 → True) ∨ p3)) ∧ p3) → p1) ∨ True)) ∨ p2)) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
theorem thm_5_vars_123660000825048011034591964850 : (((((((p5 ∧ p4) ∧ p4) ∧ p2) ∨ True) → (p2 ∨ (p2 ∨ (p3 → (False → True))))) → (p3 ∨ (False ∧ (p3 ∧ (False ∧ p3))))) → (p1 ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((((p5 ∧ p4) ∧ p4) ∧ p2) ∨ True) → (p2 ∨ (p2 ∨ (p3 → (False → True))))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- Conjunctions on the left can always be decomposed.
      let h7 := h5.left
      let h8 := h5.right
      -- Conjunctions on the left can always be decomposed.
      let h9 := h7.left
      let h10 := h7.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h12
      -- Implications on the right can always be decomposed.
      intro h13
      -- True on the right can always be proven directly.
      apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h14 := h1 h2
  -- Disjunctions on the left can always be decomposed.
  cases h14
  case inl h15 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h15
  case inr h16 =>
    -- Conjunctions on the left can always be decomposed.
    let h17 := h16.left
    let h18 := h16.right
    -- False on the left can always be used.
    apply False.elim h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112665071367567070502189106614 : (((((((p2 → p2) ∧ p1) → p5) ∧ ((p5 → (p5 ∧ ((p5 → (p4 → p4)) ∧ p1))) ∨ p4)) ∨ ((True ∨ p4) → p4)) → p2) ∨ (False → False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184819134730795386151519517650 : (((((p2 ∨ False) → p2) ∨ p2) → ((True → False) ∧ (False ∨ p3))) ∨ ((((p1 ∨ p2) → p1) → ((p3 → p2) ∨ ((p2 ∧ p1) → False))) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_349107819225496389692909333146 : (p3 → (True → ((((((p3 ∨ p1) ∨ (p1 ∨ p2)) ∧ ((p1 ∨ (p1 → True)) → (p2 ∧ p3))) ∨ (p3 → p5)) ∧ p2) → ((p4 → False) ∨ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h1
      case inr h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h1
    case inr h12 =>
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h1
      case inr h14 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h1
  case inr h15 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40588157810866477831917307599 : ((((((p3 ∧ (False → p5)) ∧ (p5 → (((((p4 ∧ p1) ∨ (p2 ∧ p5)) ∨ ((False → p2) ∧ p4)) → False) → p5))) ∧ True) → False) ∨ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342805704551349965362295902249 : (p2 → ((p4 → (p5 → (True ∧ ((True ∨ p2) ∧ p1)))) → (((((p4 ∧ (p3 → p5)) ∧ (p5 ∨ (p1 → True))) ∨ True) ∧ (p3 → True)) ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313937804075026870722935541198 : (p3 ∨ (((p1 ∧ ((((p5 → p4) ∨ False) ∧ (((p3 → p3) ∧ ((((p2 → p1) ∧ p4) ∧ p1) ∨ p3)) → p1)) ∨ False)) ∨ True) ∨ (False ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64716963485761804858528070666 : ((p1 ∨ (p3 → (((p3 ∧ (p4 ∧ (p4 ∨ p4))) ∨ (p2 ∨ (False → p1))) ∧ (((p1 ∧ (p5 ∨ True)) ∧ p3) ∧ (p1 ∧ (p4 ∨ p3)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_20284143282111967798140811609 : ((((p3 → True) → ((False ∨ (p5 ∨ ((p5 ∧ (p3 → p4)) → False))) ∨ True)) ∨ (p2 → (((p1 → p3) ∧ p1) → (False ∨ (True ∧ True))))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_337191519466200498152985993129 : (p1 → (((((p3 ∧ (((((False → (False ∨ p5)) → (False ∧ p5)) ∨ p4) ∧ p5) ∧ (True ∧ p5))) ∨ True) ∨ False) → (p4 ∧ p2)) → (p2 ∧ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (((p3 ∧ (((((False → (False ∨ p5)) → (False ∧ p5)) ∨ p4) ∧ p5) ∧ (True ∧ p5))) ∨ True) ∨ False) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- One of the premise coincides with the conclusion.
  exact h5
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h6 : (((p3 ∧ (((((False → (False ∨ p5)) → (False ∧ p5)) ∨ p4) ∧ p5) ∧ (True ∧ p5))) ∨ True) ∨ False) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h7 := h2 h6
  -- We need to get the left conjuct of h7 based on <expert-advice>.
  let h8 := h7.left
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149533693285728989275715367638 : ((p2 ∧ ((((p1 ∧ (True ∨ p5)) ∧ ((p1 ∧ p5) → p5)) ∧ (True ∧ (p3 ∧ ((False → p5) → p1)))) ∧ p1)) ∨ (p2 → ((p3 → False) → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64436785218048647517054012552 : ((p1 ∨ ((((p3 → p4) ∧ (((p4 ∧ ((p1 ∧ ((p4 ∧ ((p4 ∧ p3) ∨ p4)) → p5)) ∨ True)) ∧ True) ∨ p5)) ∨ p3) ∨ (True ∨ p1))) ∨ p4) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62191394570774210633694465089 : ((p3 ∧ (((p5 → (((p1 ∧ (p5 ∧ p2)) ∧ (p1 ∧ (p5 ∧ (((p1 → ((False → p5) → p2)) → p5) ∧ p5)))) ∧ p2)) → p2) ∧ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313321165992095544664421752677 : (p3 ∨ ((p3 ∨ ((((p2 ∨ p1) → (((True → True) ∧ (p4 ∨ (((p2 ∧ False) → True) ∧ False))) ∧ p5)) ∨ p2) ∧ (p2 → (p2 ∨ p3)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158984388078993881218738421540 : ((p3 ∨ ((p5 ∨ (((True → False) ∨ p2) ∨ p4)) ∨ (True ∨ (p5 → (True ∧ (p3 ∧ (True ∧ False))))))) ∨ ((False ∨ (p3 ∨ (True ∨ True))) ∧ True)) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114373393440748490177693404078 : ((((p1 → (p4 ∨ ((p3 ∨ p5) ∨ (p2 → ((((p5 ∧ p2) ∧ True) ∧ p5) ∨ p5))))) ∨ False) ∨ (((p3 → p5) → p2) → p5)) ∨ (p4 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191784257080691448054941920186 : ((p1 ∨ (False ∨ (((p1 ∨ (p5 → p1)) ∨ p2) ∨ p5))) ∨ (((((((p5 → p1) ∨ p3) ∨ p4) ∧ (p2 ∨ True)) ∧ False) → (p3 → p1)) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    cases h7
    case inl h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h9 =>
        -- False on the left can always be used.
        apply False.elim h4
      case inr h10 =>
        -- False on the left can always be used.
        apply False.elim h4
    case inr h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h12 =>
        -- False on the left can always be used.
        apply False.elim h4
      case inr h13 =>
        -- False on the left can always be used.
        apply False.elim h4
  case inr h14 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h15 =>
      -- False on the left can always be used.
      apply False.elim h4
    case inr h16 =>
      -- False on the left can always be used.
      apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228456852084945964661391215432 : ((False ∨ (p2 ∨ p5)) ∨ (False ∨ (((False ∨ (False → (p2 ∧ p2))) ∧ (((p4 ∨ (p5 ∨ ((True ∧ p3) ∧ True))) → p4) ∨ (p2 ∨ p2))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213897895964742141527414989390 : (((p4 ∨ (p5 ∧ p5)) ∨ p4) ∨ ((p5 ∨ p4) ∨ ((p2 ∧ ((p5 ∨ p5) ∧ (((True → (False → p2)) → (p1 → p5)) → (p4 ∧ p3)))) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117618278969641000235151389132 : ((p3 ∧ (((((((p2 ∧ p5) ∨ True) ∧ p3) ∧ p4) ∨ ((False ∧ (p3 ∨ (p2 ∨ p2))) → (p4 ∧ (p4 ∨ True)))) → p1) ∧ p3)) ∨ (p5 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_612966084137312809664162243366 : (((((p3 → (p4 ∨ (((((p4 → (False ∧ p2)) ∨ True) → False) ∧ (((p4 → (p1 ∧ p4)) ∨ p2) ∨ p5)) ∨ False))) ∨ (True → False)) ∨ True) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_714155908237447854812895186247 : (((((p2 ∨ (False ∨ (True ∧ p4))) → p5) → ((p5 ∨ ((p3 ∨ p2) ∨ True)) ∧ ((p4 ∧ ((p3 → (p2 ∧ p4)) ∧ (p5 ∧ False))) → False))) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h6.left
  let h8 := h6.right
  -- False on the left can always be used.
  apply False.elim h8
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218272930464640212810607580569 : (((p2 ∨ p1) ∨ (False ∧ True)) → (False ∨ ((((p4 ∧ p4) → (p2 ∨ p5)) → p5) ∨ (((p3 → True) → (True ∧ ((p1 ∧ p2) ∨ False))) → p2)))) := by
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
      -- Implications on the right can always be decomposed.
      intro h4
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h7 : (p3 → True) := by
        -- Implications on the right can always be decomposed.
        intro h8
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h9 := h6 h7
      -- We need to get the right conjuct of h9 based on <expert-advice>.
      let h10 := h9.right
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- Conjunctions on the left can always be decomposed.
        let h12 := h11.left
        let h13 := h11.right
        -- One of the premise coincides with the conclusion.
        exact h13
      case inr h14 =>
        -- False on the left can always be used.
        apply False.elim h14
  case inr h15 =>
    -- Conjunctions on the left can always be decomposed.
    let h16 := h15.left
    let h17 := h15.right
    -- False on the left can always be used.
    apply False.elim h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_326953398253588551583888069560 : (True → ((((p3 → ((p2 ∧ (p2 ∧ ((((False ∨ p4) ∨ True) ∧ p3) → p3))) ∨ p1)) → (((p4 ∨ False) ∨ p1) → p4)) ∨ (p4 ∨ True)) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322596777274972248301582550717 : (p5 ∨ ((p1 → (((True ∧ p2) ∧ True) ∨ ((False → (p1 ∨ p3)) ∧ ((p1 → (((((p5 → False) ∧ p5) ∨ p5) ∨ True) ∨ False)) ∧ True)))) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351544019556731034008882855639 : (p4 → ((p3 ∧ (False ∧ ((p3 ∧ (((p3 ∧ False) → True) ∨ ((p5 ∨ (p3 ∨ p3)) → True))) → p5))) ∨ ((False ∨ p5) ∨ ((p4 ∨ p4) ∨ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_875482683574030217560887263573 : ((((((True → (p3 ∨ ((((p3 ∧ (p2 ∨ ((p3 → (True ∨ False)) ∨ p4))) → p1) ∨ (p3 ∨ p2)) ∧ False))) ∨ True) → False) ∧ (True ∨ p4)) → p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h5 : ((True → (p3 ∨ ((((p3 ∧ (p2 ∨ ((p3 → (True ∨ False)) ∨ p4))) → p1) ∨ (p3 ∨ p2)) ∧ False))) ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h6 := h2 h5
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h8 : ((True → (p3 ∨ ((((p3 ∧ (p2 ∨ ((p3 → (True ∨ False)) ∨ p4))) → p1) ∨ (p3 ∨ p2)) ∧ False))) ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h9 := h2 h8
    -- False on the left can always be used.
    apply False.elim h9
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65659397153400763447099194226 : ((p4 ∨ ((p4 → (p1 ∨ ((((p4 ∧ p4) → ((p4 ∧ ((False → p5) → (p5 → (False ∨ (p5 ∧ p1))))) ∨ True)) ∨ p1) ∨ p2))) ∨ p5)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_172960159707467044737306466605 : ((p4 ∧ ((p5 ∨ ((p1 ∨ (p1 ∨ (((p3 ∧ p3) ∧ p1) → p1))) → p3)) ∨ p3)) ∨ (True → ((((p4 ∧ p4) ∨ (p2 ∧ False)) ∧ p4) → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- False on the left can always be used.
    apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_658247197933904949662723988655 : ((((p5 ∧ (True ∧ (p5 ∨ ((p4 ∨ ((((p1 ∧ False) ∧ ((p3 ∧ p4) → (True → True))) → p2) → p2)) ∨ (p1 → False))))) ∨ (p5 ∧ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173871453182332568356631849471 : ((((True ∨ ((((p4 → False) ∨ False) ∨ p4) → ((p2 ∨ True) ∧ p1))) ∧ p1) → False) → (((p5 → True) → ((p2 ∧ False) ∧ p4)) ∨ (p4 → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245890113135367810637127755367 : ((p3 ∧ p5) ∨ ((((p4 ∧ ((p4 ∨ (False ∨ p3)) ∨ (p1 ∧ p3))) ∧ (p4 ∨ (p1 → p5))) → (p1 ∨ ((p1 → p1) ∨ (p3 ∨ False)))) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h9
        -- One of the premise coincides with the conclusion.
        exact h9
      case inr h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h11
        -- One of the premise coincides with the conclusion.
        exact h11
    case inr h12 =>
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- False on the left can always be used.
        apply False.elim h13
      case inr h14 =>
        -- Disjunctions on the left can always be decomposed.
        cases h3
        case inl h15 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h14
        case inr h16 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h14
  case inr h17 =>
    -- Conjunctions on the left can always be decomposed.
    let h18 := h17.left
    let h19 := h17.right
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h20 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h18
    case inr h21 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303840636808214697995385159854 : (p1 ∨ ((((p2 ∧ p5) ∨ ((p5 ∧ (p4 ∨ (p2 → ((p4 ∨ (((False ∨ False) → p3) ∧ (p3 → p4))) → p3)))) → p3)) ∨ (p5 ∨ True)) ∨ p2)) := by
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
theorem thm_5_vars_737716558482824766528398671704 : ((((p5 → p5) ∧ (((p1 ∨ (p4 ∧ (p5 ∨ ((((p1 → p1) ∧ ((p3 → True) ∧ p3)) ∨ p1) → (p2 ∨ p1))))) ∨ (p3 → p1)) ∨ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_963549439372374653919609559546 : ((((p3 → p1) ∧ (((p5 ∨ (False → (((p5 → True) ∨ p5) ∨ p1))) ∨ ((p4 → p5) ∧ (p2 ∨ p4))) → (((False ∨ p3) ∨ p2) ∧ p5))) → p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : ((p5 ∨ (False → (((p5 → True) ∨ p5) ∨ p1))) ∨ ((p4 → p5) ∧ (p2 ∨ p4))) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- False on the left can always be used.
    apply False.elim h5
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h4
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- One of the premise coincides with the conclusion.
  exact h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172463077119278502820019667940 : (((p4 ∨ ((p1 → False) ∧ True)) ∨ (True → ((p5 ∨ p2) ∨ ((True → p5) ∨ True)))) ∨ (p1 ∨ ((p5 → (p3 → p3)) ∨ ((p5 → p2) ∨ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_247285181247609588536140389667 : ((False ∨ False) ∨ ((((False ∨ p2) ∧ ((((p2 ∧ ((False → p5) ∧ p2)) → (True ∧ (True ∨ True))) ∧ (p3 → p5)) ∨ (p4 ∨ p2))) ∨ p2) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_69176412550868056683123921844 : ((p5 → (((False ∨ (True → (p1 ∨ (((False ∧ True) → (p2 ∧ False)) → p1)))) ∧ p1) ∧ (((((False → False) ∨ True) ∧ False) ∧ True) ∨ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37955844653546151282588366589 : (((((p1 ∨ (p2 → (((p2 → True) → ((p4 → p4) ∨ p1)) ∨ ((p1 → (p3 → p2)) ∨ (p4 → True))))) ∧ p4) ∨ (False ∨ p4)) ∧ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156930065265882006604730621321 : ((((((p4 ∨ p1) ∨ ((True → ((False ∨ p1) → (p2 → True))) → p3)) ∨ p5) ∧ (True ∧ False)) ∨ True) ∨ ((p2 → True) → (p2 ∨ (p4 ∨ False)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307749577246938007953583672849 : (p1 ∨ (p3 → (((p2 ∨ (p5 ∨ ((True → (False → p1)) → p2))) ∨ (p5 → p3)) ∨ (p5 ∨ (((p4 ∧ p2) ∧ (p5 → (p3 ∨ p1))) ∨ p1))))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328400536576258162533490227247 : (True → (((((((True → ((p4 ∨ (p5 ∨ True)) ∨ False)) → (p3 → False)) ∧ True) ∨ True) → p2) ∧ p5) ∨ (False ∨ ((p4 ∨ p3) → (True ∧ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191835758833970999304639077517 : ((p3 ∨ (((p5 ∨ (p4 ∨ p3)) ∨ p5) ∨ (True ∨ p5))) ∨ (((p3 → (p3 ∧ ((p2 → p3) ∨ (False → False)))) ∨ p3) ∨ (True → (p5 ∨ p3)))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225397767311068756594471673508 : (((p2 ∨ p4) ∧ p5) ∨ ((True ∧ p1) → ((False → (p2 → False)) ∧ ((p4 ∨ (((p2 ∧ p5) ∧ p4) ∧ (p4 ∨ p5))) ∨ ((False ∨ p1) ∨ p3))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h2
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_10212880727313852769229946891 : (((p2 ∨ (((False → p4) ∧ (((p1 → (p2 → (p1 ∨ p5))) ∨ ((False → p2) → p1)) ∧ (((p2 ∧ True) → p5) → False))) → p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167600875627698841417126436273 : (((p2 ∨ (p2 ∨ (((p3 → p4) ∧ (((p4 → p4) ∨ False) ∨ p5)) ∨ False))) ∨ (p1 → True)) → (p5 → ((((p4 ∧ p4) ∨ p2) ∧ True) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h7 =>
        -- Disjunctions on the left can always be decomposed.
        cases h7
        case inl h8 =>
          -- Conjunctions on the left can always be decomposed.
          let h9 := h8.left
          let h10 := h8.right
          -- Disjunctions on the left can always be decomposed.
          cases h10
          case inl h11 =>
            -- Disjunctions on the left can always be decomposed.
            cases h11
            case inl h12 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- True on the right can always be proven directly.
              apply True.intro
            case inr h13 =>
              -- False on the left can always be used.
              apply False.elim h13
          case inr h14 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
        case inr h15 =>
          -- False on the left can always be used.
          apply False.elim h15
  case inr h16 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



