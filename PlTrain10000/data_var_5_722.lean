variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118341823405900342936990786568 : ((p2 ∨ (((p2 ∨ (p5 → p3)) ∧ ((((p5 ∧ ((((p3 ∧ p4) ∨ p3) → False) ∧ (p3 → p4))) ∧ p1) → p4) ∨ True)) ∨ p5)) ∨ (p4 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_798168069034628154965983062819 : (((p1 → (((False ∧ (p4 ∨ (True → ((((p3 ∧ False) ∧ True) ∧ p1) → p3)))) ∨ ((True → False) ∧ p5)) ∨ (((p3 ∨ p2) ∧ p3) ∨ p1))) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_149014887627845644240230077462 : ((((p5 ∧ p5) ∨ False) ∨ ((((((p2 ∨ True) ∧ p5) → p2) ∧ (p4 → (p2 → False))) → (p3 ∨ p1)) ∨ True)) ∨ (True ∨ (p3 ∧ (p5 ∨ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_25471618724046292360700992113 : (((p4 ∧ (p2 → p1)) → ((p1 → (p2 ∧ (False ∨ ((((p5 ∨ (p3 → p4)) ∨ (p5 ∨ p5)) ∧ (p4 → p1)) ∨ p5)))) ∨ (True → True))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_203474186970669953881724906102 : ((True ∨ ((p4 ∨ True) → (p5 → False))) ∧ (((p2 → ((((p2 → p1) → p4) → p2) ∧ (p2 ∧ (((False ∧ True) ∨ p1) → p3)))) → p2) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341966641911036381791248267753 : (p2 → (((((((True ∧ (False ∨ (p1 ∨ p5))) ∨ p1) → (((p5 ∧ p3) ∨ (p5 ∧ True)) ∧ p3)) ∨ True) → p3) ∨ p4) ∨ ((p5 → p3) → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115898556771266970551774237390 : (((((p4 → p2) ∨ p2) → p2) ∨ (((False ∧ (((p3 → (False ∧ p2)) → ((p1 → p5) ∨ p3)) ∧ p1)) ∧ False) ∧ (p2 → p3))) ∨ (True ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171836214217498887842447095071 : (((((p2 ∨ p5) ∧ True) → ((False ∧ (p3 ∧ p3)) ∨ (p2 → (False ∨ p3)))) → p2) ∨ (((False ∧ (False → p4)) ∧ ((False ∧ p5) → p5)) → False)) := by
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
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38545930209002576168092635477 : (((((False ∧ True) ∧ (False ∧ (p4 ∧ ((p3 ∧ p4) → False)))) ∧ (((p2 ∧ p1) ∧ p5) ∨ ((p3 ∧ (p1 → (p5 ∨ p5))) ∨ True))) ∧ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42376142982793893509027649671 : (((p4 ∧ ((((p2 ∧ (p4 → ((p2 ∨ ((((p3 ∧ p2) → p3) ∨ p1) → p5)) ∧ (p2 ∧ False)))) ∨ p5) ∨ (True → p3)) → p1)) ∨ True) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301595582901711562122341809198 : (False ∨ (((p1 ∧ p1) ∨ False) → (((((p5 ∧ p5) → ((False → False) → p2)) ∨ p2) ∧ p1) ∨ ((((p3 ∨ False) ∧ (p5 ∧ False)) ∧ p5) ∨ p1)))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133516372280774136697152693884 : (((((((p5 → p3) → (False ∨ p4)) ∧ (((p3 → ((p5 → p5) ∧ p1)) ∨ (False ∨ p3)) ∧ False)) ∨ p1) ∧ False) ∧ p5) ∨ (True ∨ (p3 ∧ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_786433533408093201830014488547 : (((p4 ∨ ((p1 → (((p2 ∨ ((p5 ∨ (p1 ∨ p5)) → (p5 ∧ p1))) ∨ p4) → p4)) ∨ ((((p3 ∧ p5) → True) → p3) → (True ∧ True)))) ∨ p5) ∧ True) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_720598965436017161068044791853 : ((((((p5 ∨ p5) ∧ p2) → p5) → (((((p2 → ((True ∨ ((p3 ∨ p3) → False)) → True)) → (False ∧ p1)) ∧ p2) → (False ∧ p2)) ∧ True)) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h5 : (p2 → ((True ∨ ((p3 ∨ p3) → False)) → True)) := by
    -- Implications on the right can always be decomposed.
    intro h6
    -- Implications on the right can always be decomposed.
    intro h7
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h8 := h3 h5
  -- We need to get the left conjuct of h8 based on <expert-advice>.
  let h9 := h8.left
  -- False on the left can always be used.
  apply False.elim h9
  -- Conjunctions on the left can always be decomposed.
  let h10 := h2.left
  let h11 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h11
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_229870939825165781530968873957 : ((p5 → (p2 ∨ p2)) ∨ ((False ∨ (((p3 ∨ p5) → ((p1 ∧ ((p1 ∧ p4) ∨ p2)) ∧ p1)) ∨ ((p5 → p1) → (True ∨ (p2 ∧ p1))))) ∨ p5)) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_786958512887285357996042619429 : (((p4 ∨ ((p1 ∧ False) ∧ (p5 ∨ ((p4 ∨ p4) ∧ (p1 ∧ (True ∧ (((False ∨ p3) ∧ (p5 → ((p1 ∧ p1) ∧ (p3 ∨ p4)))) ∨ p3))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_586552130642479257022985288539 : ((((((p4 ∨ p4) ∧ (p2 → ((True ∨ ((False ∨ p2) ∧ False)) → (p4 ∨ (False → (p2 → ((p2 ∨ (p1 ∨ p5)) → p2))))))) ∧ p5) ∧ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148199499640463065006118051155 : ((((True ∨ p3) → (p1 ∨ (((((p1 → p1) ∨ p1) → True) → (p1 ∨ p4)) ∨ p3))) ∧ ((True ∧ p2) ∧ False)) ∨ (((p3 ∧ p4) ∨ True) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198626032985607153556033752840 : ((p3 ∨ ((((p2 ∨ p3) ∨ False) ∧ p5) ∧ p4)) ∨ ((True ∨ p2) ∨ (p3 ∧ (((p4 ∨ (p1 → (p2 ∨ p1))) ∧ p5) → (True → (p4 ∨ p1)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158294273339048607522415116677 : ((((p5 ∨ p4) ∨ p1) → (((False ∨ (p3 ∧ p5)) → p4) ∧ ((p1 ∨ ((p1 → True) → p5)) → p5))) ∨ ((True → p5) ∨ (p4 → (p4 ∨ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180625658586984950481845111654 : (((True → ((p4 ∧ True) ∧ (p4 → p5))) ∧ (p2 ∧ ((p1 ∨ p2) → p4))) → ((False ∧ p2) ∨ (((True → True) → ((p3 → True) → p3)) ∨ True))) := by
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
theorem thm_5_vars_172890798988821663103256317244 : ((p1 ∧ (p4 ∨ ((((p4 ∧ p1) ∨ True) ∨ ((p3 → p1) ∨ True)) → (p5 ∧ p4)))) ∨ ((p3 ∧ (((p1 ∨ p2) → p3) ∧ False)) → (p4 ∨ p3))) := by
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
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52028338259683968048202250726 : (((p2 ∨ (((p1 → p5) ∧ (True → (p3 ∨ ((p4 ∧ p4) ∨ p3)))) → (p2 ∨ p5))) ∨ ((((True ∨ (p2 ∧ p5)) → p3) → p2) ∨ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_867779108558489328842727109506 : (((((p5 ∨ False) ∨ (((True ∨ p4) → False) → ((((p3 ∧ p3) ∧ (p5 → p2)) ∧ False) ∧ (((p3 ∧ False) ∨ p5) ∧ (p1 → True))))) → False) → p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p5 ∨ False) ∨ (((True ∨ p4) → False) → ((((p3 ∧ p3) ∧ (p5 → p2)) ∧ False) ∧ (((p3 ∧ False) ∨ p5) ∧ (p1 → True))))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h4 : (True ∨ p4) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h5 := h3 h4
    -- False on the left can always be used.
    apply False.elim h5
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h6 : (True ∨ p4) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h7 := h3 h6
    -- False on the left can always be used.
    apply False.elim h7
    -- Implications on the right can always be decomposed.
    intro h8
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h9 : (True ∨ p4) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h10 := h3 h9
    -- False on the left can always be used.
    apply False.elim h10
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h11 : (True ∨ p4) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h12 := h3 h11
    -- False on the left can always be used.
    apply False.elim h12
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h13 : (True ∨ p4) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h14 := h3 h13
    -- False on the left can always be used.
    apply False.elim h14
    -- Implications on the right can always be decomposed.
    intro h15
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h16 := h1 h2
  -- False on the left can always be used.
  apply False.elim h16
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231963379451239883631618277732 : (((p1 ∨ p3) → p2) → (p3 → ((p1 ∧ (((p2 → p2) ∨ p5) ∧ (False ∧ p5))) ∨ (((((p5 → False) ∨ p3) ∧ (True ∨ p2)) ∨ p4) ∧ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161116589062989170659136797879 : (((p3 ∨ p5) ∧ ((((((p1 ∨ p5) → p5) ∨ ((p4 ∨ True) ∧ (False ∨ p1))) ∨ p3) → True) → p1)) → (((False ∧ p2) ∨ p2) ∨ (p2 ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h5 : (((((p1 ∨ p5) → p5) ∨ ((p4 ∨ True) ∧ (False ∨ p1))) ∨ p3) → True) := by
      -- Implications on the right can always be decomposed.
      intro h6
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h7 := h3 h5
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h8 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h9 : (((((p1 ∨ p5) → p5) ∨ ((p4 ∨ True) ∧ (False ∨ p1))) ∨ p3) → True) := by
      -- Implications on the right can always be decomposed.
      intro h10
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h11 := h3 h9
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158742504893368423106936101826 : ((p4 ∧ (((((p1 → True) → p2) ∧ p1) ∧ (((p5 ∨ p5) ∧ p4) ∧ ((True ∧ p5) ∨ p1))) ∧ p2)) ∨ (p2 ∨ (((False ∨ p4) ∨ p2) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115303567649694130573708861912 : ((((p1 ∧ ((False ∧ (p5 ∨ p1)) ∧ (p2 ∧ True))) → p3) → (p4 → ((False ∨ ((((p4 → p4) ∨ p4) → p2) ∧ p2)) ∨ p4))) ∨ (p3 ∨ p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45612712474210056413666019011 : (((p3 ∨ (p1 ∨ (((p4 ∨ p3) ∧ ((((p5 → p3) ∧ ((True ∧ p1) ∧ ((p2 ∨ p2) → False))) ∧ (p5 ∨ p3)) ∧ p5)) ∨ False))) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207875352818869767292705501648 : ((((False ∧ p4) → p3) ∧ (p2 ∧ p2)) → (True → (p4 → ((((p1 ∨ ((p4 ∧ p3) ∧ True)) → (p1 ∧ False)) ∧ (p1 ∨ p4)) ∨ (p2 ∧ p2))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h7
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_806832606865602980957206368631 : (((p4 → ((p2 ∨ (((p3 ∧ (p4 → ((p5 ∨ p1) → (p2 → p2)))) ∨ ((p2 → p4) ∨ p2)) ∧ ((p2 → p4) → p1))) ∨ (True → p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345469292649975020737872175375 : (p3 → ((((((p1 ∨ (p5 → p4)) ∨ p5) ∨ ((False → (p5 ∧ False)) ∧ ((p2 ∧ p3) ∨ (p2 ∧ p3)))) ∧ False) ∨ ((p5 → True) ∧ True)) ∨ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114857499659906537380621022832 : (((((p4 → (p4 ∨ (p2 → (p5 ∨ (p4 → p2))))) → False) ∧ (False ∨ True)) ∨ ((False ∨ (p4 ∨ ((p3 ∨ True) ∨ p3))) ∨ True)) ∨ (p3 ∨ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52958363894605352787446437182 : ((((p3 ∨ ((p1 → ((p5 ∨ False) ∨ False)) ∧ (p5 → p5))) ∨ p1) ∧ (((False ∧ p2) ∨ (True ∧ p4)) ∨ ((p2 ∧ True) → (p4 ∧ p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48641519819088139392790302612 : ((((False ∨ ((False ∨ (((p3 ∧ False) ∧ p4) → (p2 ∨ (False → (p2 ∨ p1))))) ∨ p5)) → ((p5 → p2) ∧ p1)) ∧ ((p4 → p5) ∨ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207320990973932392702926874457 : ((((p5 ∨ p4) ∧ (p5 → p4)) ∨ False) → ((False ∧ (p2 → (p3 ∧ (((p3 → True) ∨ p4) ∧ (False ∧ ((True ∨ p2) ∨ (p4 ∧ p4))))))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- Disjunctions on the left can always be decomposed.
    cases h3
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
    -- False on the left can always be used.
    apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55876013685296106151445148231 : (((True ∨ (p3 → (p2 ∧ p2))) ∧ (((True → (p1 ∨ (p3 ∧ (p2 ∧ (((p4 ∨ True) ∨ (False ∨ p3)) ∧ True))))) ∧ (p1 ∧ p1)) → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40433038613680016530692586408 : ((((((True → p5) ∧ (((True ∨ (p5 ∨ p3)) ∧ p3) → p1)) ∧ (((True → (True → (p1 → (p4 ∨ p4)))) ∧ p2) ∨ p3)) ∨ True) ∨ p1) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_694540374822642529061106088457 : ((((p1 ∧ ((p3 ∧ ((p1 ∧ p1) ∧ True)) ∧ ((p2 → (p5 ∨ True)) ∧ p3))) ∨ (((True ∧ False) → p1) ∧ (((p3 ∨ p1) ∨ True) ∨ p5))) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_203845902969585855536629783414 : ((False → ((p4 → p1) ∨ (p3 ∧ True))) ∧ (p1 → ((((p2 → True) → ((p1 ∧ p2) ∧ p5)) ∨ p4) → (((p3 → p5) ∧ p5) ∨ (p4 ∨ p2))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h5 : (p2 → True) := by
      -- Implications on the right can always be decomposed.
      intro h6
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h7 := h4 h5
    -- We need to get the left conjuct of h7 based on <expert-advice>.
    let h8 := h7.left
    -- We need to get the right conjuct of h8 based on <expert-advice>.
    let h9 := h8.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h9
  case inr h10 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190702679819996366231862389132 : ((((p4 ∧ (p4 ∧ (p2 → p5))) ∨ p1) ∧ (p5 ∧ p3)) ∨ (((p5 → (p4 ∨ p1)) → ((False ∧ p4) → (p4 ∧ p4))) ∧ (False ∨ (p3 → p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h3
  -- Conjunctions on the left can always be decomposed.
  let h5 := h2.left
  let h6 := h2.right
  -- False on the left can always be used.
  apply False.elim h5
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h7
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111319338685591977553302195291 : (((p1 ∧ (((p3 → (p4 ∨ True)) → p3) ∨ (p3 → (((p1 ∨ (True ∨ (((p2 ∧ p3) ∧ p4) → p2))) → False) ∨ False)))) ∧ True) ∨ (False → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307833649067028565518779051360 : (p1 ∨ (p4 → (p3 ∨ ((False ∨ (p3 ∨ ((((True ∧ p3) → (p2 → (p1 → True))) ∧ (p3 ∧ (p2 ∧ p5))) → False))) ∨ ((p4 → p4) ∨ False))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340917010095274368268048210889 : (p2 → (((((p3 ∧ p4) ∨ (True ∨ (p5 ∧ p2))) ∨ p5) → (((True → p5) → ((p1 → p5) ∧ ((p2 ∧ (True → p1)) ∨ p1))) ∨ p2)) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h1
      case inr h9 =>
        -- Conjunctions on the left can always be decomposed.
        let h10 := h9.left
        let h11 := h9.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h11
  case inr h12 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_698298526932300479122279931085 : (((((((p3 → False) ∨ p2) → (p3 ∨ (p4 → p4))) ∧ (p2 ∨ p4)) ∨ ((((((p3 ∧ (p5 ∨ p5)) ∧ p2) → False) ∧ p1) → False) ∨ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_903485968428737604590996948527 : ((((True → (p3 → (p1 ∨ (((((p4 ∨ p1) → p3) ∧ ((p2 → p5) ∨ p4)) ∨ p5) → (p1 → p1))))) ∧ (p5 ∧ ((p5 → p3) → True))) → p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- One of the premise coincides with the conclusion.
  exact h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_802567811463666960186506894856 : (((p2 → (p4 ∨ (p4 ∨ (p1 ∨ (((False ∧ ((p1 → p1) → p4)) ∨ (((p1 → False) ∨ p5) → p1)) ∨ (p5 → (True ∨ (p2 → p4)))))))) ∨ p3) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197013431156711074929217497068 : (((((p1 ∨ p4) ∧ p4) ∨ (False ∨ False)) ∨ True) ∨ ((p2 ∨ ((((p5 → p4) ∨ False) → p2) → (((p4 ∧ (p3 ∨ False)) ∧ p3) ∨ p2))) → p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_124485612687605065101016691885 : ((((((False → p4) ∨ True) ∧ p4) ∨ False) ∧ (p3 → (((p4 ∨ ((p4 ∨ (p5 ∨ p1)) → (p2 → (True ∨ p4)))) → False) ∨ p4))) → (True → p4)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h9 =>
      -- One of the premise coincides with the conclusion.
      exact h7
  case inr h10 =>
    -- False on the left can always be used.
    apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_392938400016705982721752198498 : (((((p3 ∨ (p2 ∧ p2)) → ((((False → p1) ∨ p2) ∨ p4) → ((p2 ∨ (p5 ∨ ((p4 ∧ p3) ∧ (p5 ∧ (p3 ∨ True))))) ∨ True))) ∨ False) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h5 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h6 =>
        -- Conjunctions on the left can always be decomposed.
        let h7 := h6.left
        let h8 := h6.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h10 =>
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
  case inr h14 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h15 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h16 =>
      -- Conjunctions on the left can always be decomposed.
      let h17 := h16.left
      let h18 := h16.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317999467747062614452085632695 : (p4 ∨ ((((((False → ((p5 → ((p4 ∨ p2) → p3)) ∧ (((True ∨ p1) ∧ (False ∨ p1)) ∨ p1))) ∨ True) ∧ (p3 → False)) ∧ p2) ∧ p3) → p5)) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h8 =>
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h9 : p3 := by
      -- One of the premise coincides with the conclusion.
      exact h3
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h10 := h7 h9
    -- False on the left can always be used.
    apply False.elim h10
  case inr h11 =>
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h12 : p3 := by
      -- One of the premise coincides with the conclusion.
      exact h3
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h13 := h7 h12
    -- False on the left can always be used.
    apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166523654647154488144245131144 : ((p4 ∨ ((p1 ∨ p4) ∧ ((p5 ∨ p2) ∧ (p1 ∨ (((p2 ∧ p2) ∨ (True ∨ p2)) ∨ p3))))) ∨ (((p3 ∧ p2) ∨ ((p4 ∨ p4) ∧ p1)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135307937676289807241661501707 : ((((((((((p4 → p2) ∧ True) ∧ p5) ∨ p1) ∨ True) ∨ (p1 ∨ p5)) ∨ (p2 ∧ p1)) → p1) ∧ ((p4 ∧ p1) ∨ p2)) ∨ (False → (True → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197992242962085897193470288218 : (((p4 ∨ p5) ∧ (p4 → ((p3 → p5) → p4))) ∨ (p4 ∨ (p1 → (p3 → ((((p5 ∧ ((p4 ∨ p1) → True)) → False) → (p1 ∧ p4)) ∨ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_990037391825115338631599669192 : (((p3 ∧ (p2 ∧ (((((p3 ∧ ((p5 → True) → False)) ∨ p1) ∨ False) ∧ ((((False ∨ p1) → p3) ∧ p5) ∧ p2)) ∧ (False ∨ (p4 ∨ p4))))) → p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- Conjunctions on the left can always be decomposed.
      let h14 := h9.left
      let h15 := h9.right
      -- Conjunctions on the left can always be decomposed.
      let h16 := h14.left
      let h17 := h14.right
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h18 =>
        -- False on the left can always be used.
        apply False.elim h18
      case inr h19 =>
        -- Disjunctions on the left can always be decomposed.
        cases h19
        case inl h20 =>
          -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
          have h21 : (p5 → True) := by
            -- Implications on the right can always be decomposed.
            intro h22
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h13, we can now drive its conclusion.
          let h23 := h13 h21
          -- False on the left can always be used.
          apply False.elim h23
        case inr h24 =>
          -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
          have h25 : (p5 → True) := by
            -- Implications on the right can always be decomposed.
            intro h26
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h13, we can now drive its conclusion.
          let h27 := h13 h25
          -- False on the left can always be used.
          apply False.elim h27
    case inr h28 =>
      -- Conjunctions on the left can always be decomposed.
      let h29 := h9.left
      let h30 := h9.right
      -- Conjunctions on the left can always be decomposed.
      let h31 := h29.left
      let h32 := h29.right
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h33 =>
        -- False on the left can always be used.
        apply False.elim h33
      case inr h34 =>
        -- Disjunctions on the left can always be decomposed.
        cases h34
        case inl h35 =>
          -- One of the premise coincides with the conclusion.
          exact h28
        case inr h36 =>
          -- One of the premise coincides with the conclusion.
          exact h28
  case inr h37 =>
    -- False on the left can always be used.
    apply False.elim h37
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111339705600471371770086180249 : (((p3 ∧ ((False ∨ (((((False ∧ True) ∨ (p1 ∨ p4)) ∨ (False ∧ p1)) → p1) ∧ p3)) ∧ (((p3 ∧ p1) ∧ p5) → p1))) ∧ p5) ∨ (p2 → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56527113975543769257330447277 : (((True ∨ ((False → True) → True)) → (((p4 ∨ (False ∨ p4)) ∧ (((p4 ∧ (False ∧ p3)) ∧ p4) ∨ (p1 ∧ (p5 → (p1 ∧ False))))) ∨ True)) ∨ p5) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66532181813665198887266260861 : ((True → ((((p2 ∨ (p5 → p4)) ∨ (p4 ∨ True)) → ((p3 → (((True ∨ (p4 → p2)) ∧ ((False ∧ p5) ∧ p3)) → False)) ∧ p4)) → p4)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : ((p2 ∨ (p5 → p4)) ∨ (p4 ∨ True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68303335199269744255158523123 : ((p3 → (((((p4 → ((True ∨ (((p2 → p1) ∨ p3) ∨ p3)) → p2)) ∨ p4) → p2) → (p1 ∨ p3)) ∧ (((True ∨ p3) ∧ p1) ∨ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67679504521180965806503706428 : ((p1 → (p1 → (((((p1 ∧ False) → True) ∨ (False → (False → p4))) → ((((p4 → ((p2 ∧ False) → p5)) → p1) ∧ p2) ∨ p3)) ∨ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138421644563206541744828385416 : ((p5 → ((False → ((False ∧ (p1 ∨ ((p2 ∧ ((False ∧ p2) ∧ p2)) ∨ p3))) ∧ ((p5 → (p2 ∨ p1)) → p5))) → False)) ∨ ((True → False) → False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_632291818066583493898885554000 : (((((p2 ∧ (p5 ∨ (((p1 ∧ (((p5 ∨ (p2 ∨ p3)) → ((p1 ∧ p3) ∧ (p2 ∨ p2))) ∨ True)) ∨ (p2 → p1)) → p4))) → True) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_619495334723485648955030529368 : (((((True → (p5 → p1)) → (((p4 → (p3 → (((False ∨ p3) ∨ ((True ∧ p5) ∨ False)) ∧ p3))) → (True → (True ∨ p4))) → p1)) ∨ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299404512166894994284517639932 : (False ∨ ((p1 ∧ (True → ((((p4 ∧ ((p2 → (((p3 ∧ False) ∨ False) → p2)) ∨ False)) ∧ p2) → p3) ∧ (((p1 ∧ p5) → p5) ∨ p3)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_724233196711344477386156891516 : ((((p3 ∧ (p1 → p2)) ∧ (((p4 ∨ ((p2 → (True ∨ p4)) → (p1 ∧ True))) ∧ (((p1 ∨ (True ∧ False)) ∨ p1) ∧ (p1 ∨ p2))) ∨ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219133373085423020603883625990 : ((True ∨ (p1 ∨ (p3 ∨ p2))) → ((False ∨ p4) ∨ (p4 → (p1 ∨ (p5 ∨ (True → (p4 ∨ (((p2 → ((False ∧ p5) ∧ p4)) ∧ p4) ∨ False)))))))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h7
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h10
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h11
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h10
      case inr h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h13
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h14
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46205379656830776116077729253 : ((((((((True → ((p4 ∨ p4) ∧ p4)) ∨ p1) ∨ (p3 ∧ ((False → True) ∨ p3))) → (p1 ∨ p5)) ∧ False) ∧ (p5 ∧ p5)) ∧ (p5 → p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197940728030179866360502077248 : (((False ∧ p1) ∧ (p2 → ((p5 ∨ p5) ∨ p1))) ∨ (((True ∧ (p3 ∧ (False ∨ False))) ∧ (True ∧ (((p3 ∨ True) ∨ p4) ∨ (p5 ∨ p3)))) → p1)) := by
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
  let h6 := h5.left
  let h7 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- False on the left can always be used.
    apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42486223677471599473289618746 : (((False ∨ (((((p2 ∧ ((p5 ∨ False) → True)) ∧ ((True → False) → (p3 ∨ p2))) ∨ ((p2 ∨ True) ∨ (p2 ∨ p1))) ∨ False) ∧ True)) ∨ False) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_254331148744352521446026921671 : ((p2 ∧ p4) → (((p5 → (False ∨ ((p1 → False) ∧ (True ∧ (((((p3 ∧ p1) → False) ∨ False) → p2) ∧ p5))))) ∨ ((p5 ∧ p1) ∨ True)) ∨ p3)) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55983952903471373679568087695 : ((((p3 ∧ (p3 ∨ p4)) ∧ True) ∨ (p2 ∨ ((p1 ∨ ((((p3 ∧ p4) → (((p1 ∨ True) → (p2 ∨ p4)) → p4)) ∧ True) ∨ p1)) ∧ True))) ∨ p3) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h4
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234194176116464112034281919837 : ((False → (p1 ∧ False)) → (p5 → (p2 ∨ (((False ∧ (p1 → False)) ∧ (p2 ∧ ((False ∧ (False ∨ (p5 ∧ (p5 ∧ (p1 → False))))) ∧ False))) ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172862452565621475379417899642 : ((False ∧ (p1 → (((p5 ∧ ((p1 → p5) ∨ True)) → (p2 ∨ (p2 ∧ p3))) → p5))) ∨ (p1 ∨ (((p5 ∧ (p4 ∧ p2)) → (p5 ∨ p2)) ∨ p3))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258229343558454052475625287666 : ((p4 ∨ p5) → ((((p3 → (True ∧ (p4 → p5))) ∨ p2) → (p5 ∧ (p2 ∨ ((p4 ∧ p4) ∨ (p3 ∨ ((p3 → p5) → p5)))))) ∨ (True → p4))) := by
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
    exact h2
  case inr h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h7 =>
      -- One of the premise coincides with the conclusion.
      exact h4
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h9
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h10 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341874328430200881456705969109 : (p2 → ((p1 ∨ (((((p1 → p4) ∧ ((((True ∧ p3) → p3) ∧ True) ∨ p3)) ∨ True) ∧ (p2 → ((p3 ∨ p2) ∧ p3))) ∨ p1)) → (p4 → p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h9 =>
        -- Conjunctions on the left can always be decomposed.
        let h10 := h9.left
        let h11 := h9.right
        -- Disjunctions on the left can always be decomposed.
        cases h11
        case inl h12 =>
          -- Conjunctions on the left can always be decomposed.
          let h13 := h12.left
          let h14 := h12.right
          -- One of the premise coincides with the conclusion.
          exact h3
        case inr h15 =>
          -- One of the premise coincides with the conclusion.
          exact h3
      case inr h16 =>
        -- One of the premise coincides with the conclusion.
        exact h3
    case inr h17 =>
      -- One of the premise coincides with the conclusion.
      exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_683694460067809586868730476743 : (((((p5 ∧ ((((p1 ∨ (p3 ∨ (False ∧ p3))) ∧ (False → (p1 ∨ False))) → p5) ∨ False)) ∧ p5) ∨ ((True ∨ (False ∧ (p4 ∧ True))) ∨ False)) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_191887676363810655244537594815 : ((p4 ∨ (p4 → (p5 ∨ (p5 ∧ (False ∨ (p2 ∧ p5)))))) ∨ ((((True ∧ p1) ∧ ((True ∧ p2) ∧ (p4 ∧ p1))) ∧ True) ∨ (p5 ∨ (True → True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228961601224212806204250774545 : ((p4 ∨ (p1 → p4)) ∨ ((False ∨ ((p1 ∧ ((False ∧ p4) ∨ (p4 ∧ True))) ∨ (p3 → (p3 → (p1 → (p5 → ((True ∨ p5) ∨ p1))))))) ∨ p3)) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_726137880339786824797936761363 : (((((p3 ∧ p1) ∨ p5) ∨ ((((p5 ∧ p5) ∨ (p1 → (p5 ∧ True))) ∧ (((p3 ∨ p3) ∧ (p2 ∨ (p3 ∧ p4))) ∨ p5)) ∨ (True ∨ False))) ∨ p2) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_596453857037002996933784640261 : ((((((((p5 ∧ p2) ∧ (p4 ∧ p4)) ∧ p3) ∧ p3) → (((True → (p3 ∨ p4)) → False) ∨ ((p4 → (True ∨ (p3 → False))) → False))) ∧ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116590541453222722638451255291 : (((p4 ∨ p4) ∧ (True → ((p1 → p3) → ((p4 ∧ p5) ∨ (p5 ∧ (((p1 → True) ∨ (True → True)) → ((p5 ∨ p5) ∧ p5))))))) ∨ (p3 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_183946974084201900988919426223 : (((p3 ∨ (((p4 ∧ True) ∨ (True → (p2 ∨ p4))) → p3)) ∧ p5) ∨ ((p3 → p3) ∨ ((p4 ∨ (((False → p2) ∨ p4) ∨ (p2 ∧ p1))) → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179736658823282966615489852461 : (((((p5 ∧ (p1 ∧ (p2 → (p5 ∨ p2)))) ∨ p2) ∧ (False → p4)) ∧ p3) → (p5 → ((p3 → False) ∨ ((p1 ∨ p5) ∨ ((False ∧ p4) ∧ True))))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h10
  case inr h12 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317678205243432150269205978869 : (p4 ∨ ((((p4 → False) ∧ (p1 ∨ (False ∨ (((p4 ∨ ((True → ((p1 → p2) ∨ p3)) → p2)) ∧ (p1 → False)) ∨ (p3 → False))))) → p5) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322241868482449332832457249975 : (p5 ∨ (((((p1 ∨ p2) ∨ (((True → p2) ∨ (((p3 ∧ (p2 ∧ (p5 ∧ False))) ∨ (p5 ∧ (p4 ∧ p1))) → p3)) ∨ p5)) ∨ p5) ∨ True) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_344931887555022228108417360189 : (p3 → (((((True ∨ False) ∧ ((p4 ∧ p2) ∧ (((p4 → True) → ((p5 → p2) ∨ (False ∨ (p5 ∨ (False ∧ p1))))) ∧ p1))) ∨ True) ∨ p4) ∧ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_793026370756218793980486374338 : (((True → ((p4 ∨ p5) ∨ (((p1 → p1) ∧ p4) ∧ ((False ∨ True) → ((((p2 ∧ p1) → p3) → (p5 ∧ p5)) ∨ (p2 ∨ (p5 ∧ p2))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47187223338623427338297133612 : ((((((p4 ∧ p3) → False) → (p2 ∧ ((p5 ∨ True) ∨ (True ∨ p3)))) ∧ ((p3 ∨ (p3 ∧ (p4 ∨ (True ∧ True)))) ∧ p5)) ∨ (True → True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_318344274295434857720170213918 : (p4 ∨ ((p5 ∧ (True → (((False ∧ ((p3 ∧ p5) → (p5 ∧ True))) → (p4 → (True ∧ (False → ((p1 ∧ (p5 ∨ False)) → True))))) ∧ p1))) → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_612219021698850358456069979979 : ((((((p4 ∨ (p1 → (p3 ∧ p2))) → ((p1 → p5) ∧ (p1 → (p5 → (p3 ∧ ((p4 ∨ False) ∨ (True → p5))))))) ∧ (p1 ∧ False)) ∨ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_430606653017438544393001162523 : ((((((p1 → True) → p4) ∨ (p1 → (((((p1 ∨ p1) → (p5 ∨ p2)) ∨ ((True → (False ∨ False)) → False)) ∨ p2) ∨ False))) ∨ (p3 → p3)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_678778117713690997686172506311 : (((((p5 → p2) → ((((p1 → ((p1 ∨ p3) ∨ p5)) ∨ ((p1 ∨ p1) ∨ p3)) → p4) ∨ (True → p3))) ∨ ((p5 → p5) → (p2 → p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198547261555257885494879392687 : ((False ∨ (True → (p1 → ((p3 ∨ p3) → False)))) ∨ ((((False ∨ p4) ∨ (((p1 → p4) ∨ True) ∨ (p2 ∨ (p1 ∧ (True ∨ p5))))) ∨ True) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_779211786547235807451739296705 : (((p2 ∨ ((((p4 → ((p1 ∧ p4) ∧ (p2 ∨ (False ∨ p4)))) ∧ (p3 ∧ p1)) ∨ ((p4 ∨ ((p3 ∨ False) ∨ True)) ∨ (False ∧ False))) ∧ True)) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187471737883633344622890761883 : ((True ∨ (p2 → (((p2 ∧ p2) ∨ p5) ∨ ((p4 ∨ p5) ∧ p4)))) → (((((True ∨ ((p4 → (p5 ∨ p4)) ∨ p4)) → False) → p3) → False) → p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h4 : (((True ∨ ((p4 → (p5 ∨ p4)) ∨ p4)) → False) → p3) := by
      -- Implications on the right can always be decomposed.
      intro h5
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h6 : (True ∨ ((p4 → (p5 ∨ p4)) ∨ p4)) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h7 := h5 h6
      -- False on the left can always be used.
      apply False.elim h7
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h8 := h2 h4
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h10 : (((True ∨ ((p4 → (p5 ∨ p4)) ∨ p4)) → False) → p3) := by
      -- Implications on the right can always be decomposed.
      intro h11
      -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
      have h12 : (True ∨ ((p4 → (p5 ∨ p4)) ∨ p4)) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h11, we can now drive its conclusion.
      let h13 := h11 h12
      -- False on the left can always be used.
      apply False.elim h13
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h14 := h2 h10
    -- False on the left can always be used.
    apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_701777224728431256603393426945 : ((((p2 ∧ ((p3 → ((p2 ∧ True) ∧ False)) ∧ (True → p3))) ∧ (((True → ((True ∨ p4) → (p5 → p4))) ∨ (p4 ∧ p5)) ∧ (p1 → p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_731983329598057449886320642547 : ((((True ∧ True) ∧ ((False ∧ (p4 ∧ ((True → (p4 ∨ (p5 ∨ (p2 → True)))) ∧ p1))) ∧ ((p4 ∨ ((p1 ∨ p5) ∨ p1)) ∨ (p4 ∧ False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_266010974891630702088229071836 : (True ∧ (p1 → ((p2 → ((False → p1) ∧ ((((p5 ∨ p3) → ((p4 ∧ p5) ∧ (False → (False ∧ (p1 ∧ False))))) ∧ p4) → False))) ∨ (p1 ∧ p1)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149255210517384596620816581190 : (((p3 ∨ p1) ∨ ((p5 ∧ p2) → (p5 → ((((p4 ∨ (p3 ∨ p3)) ∧ False) ∨ p2) ∧ (p4 ∧ (p2 → False)))))) ∨ (((False ∧ p1) ∧ p2) → p2)) := by
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
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263080441691463809113326768183 : (True ∧ (((((((True → (False ∧ p1)) → (((p4 ∧ (p5 → False)) ∧ p2) ∨ p3)) ∧ True) → False) → ((p3 → p3) → False)) ∨ p5) ∨ (False ∨ p5))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : (((True → (False ∧ p1)) → (((p4 ∧ (p5 → False)) ∧ p2) ∨ p3)) ∧ True) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h4
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h5 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h6 := h4 h5
    -- We need to get the left conjuct of h6 based on <expert-advice>.
    let h7 := h6.left
    -- False on the left can always be used.
    apply False.elim h7
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h8 := h1 h3
  -- False on the left can always be used.
  apply False.elim h8



