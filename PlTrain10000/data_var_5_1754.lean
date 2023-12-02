variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148995382760500757875142274388 : (((False → (p2 ∧ False)) ∧ (((p5 → ((p5 → p4) → ((p4 → (False ∧ p4)) ∨ (p4 ∨ p1)))) ∧ p3) ∨ p5)) ∨ (False ∨ (p4 → (True ∨ p1)))) := by
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
theorem thm_5_vars_47380271630691674191093437303 : ((((p5 ∧ p5) → (((((((p2 ∨ False) ∨ (p1 ∧ p3)) ∧ p1) → False) ∨ p4) → (p4 ∧ (p3 ∨ (p2 ∧ p3)))) ∨ p5)) ∨ (p2 ∨ p4)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259191235977156629268566290609 : ((False → False) → (((True ∧ True) → (p3 ∨ ((p4 ∧ True) ∨ ((((((p4 ∧ p1) → p2) ∧ (p1 ∨ False)) ∧ (p3 ∨ p3)) ∨ p5) ∧ p2)))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_478083492944145192138899668377 : (((((False ∨ p5) → (p5 → ((p5 ∨ False) → (p1 ∧ True)))) → ((((False → (p5 ∨ p5)) → False) ∨ ((False ∧ p3) ∧ p4)) → (p1 ∧ True))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h4 : (False → (p5 ∨ p5)) := by
      -- Implications on the right can always be decomposed.
      intro h5
      -- False on the left can always be used.
      apply False.elim h5
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h6 := h3 h4
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h8.left
    let h11 := h8.right
    -- False on the left can always be used.
    apply False.elim h10
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45334009164490134246375758576 : (((p3 ∧ (p2 ∧ (((((p3 ∨ ((((True ∧ (p1 ∨ True)) → p3) → p4) ∨ p3)) ∧ (p4 ∧ (p5 → p1))) → p4) → p2) ∨ p4))) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117359607383581078326496308601 : ((False ∧ (False ∨ ((True ∧ (True ∧ (((p2 ∨ True) ∧ (p3 ∨ p1)) ∧ (((p3 → p4) → p3) ∨ p3)))) ∧ (p5 ∨ (p1 ∧ p3))))) ∨ (False → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_139798401627620854141967020400 : (((p3 ∨ (((p4 ∧ (p4 ∨ False)) ∨ ((((p3 ∧ p5) ∨ False) → (False → p3)) ∧ True)) ∨ (p2 ∨ (p5 → p1)))) → False) → ((False ∧ p4) ∨ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p3 ∨ (((p4 ∧ (p4 ∨ False)) ∨ ((((p3 ∧ p5) ∨ False) → (False → p3)) ∧ True)) ∨ (p2 ∨ (p5 → p1)))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- False on the left can always be used.
    apply False.elim h4
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h2
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135071176846410949633065113528 : (((((((p5 → ((p2 → p5) ∨ p3)) ∨ (p4 → ((p2 ∨ True) ∧ p1))) ∧ p5) → p4) ∨ (True ∧ p5)) ∨ (p5 ∨ True)) ∨ (p3 ∧ (False ∨ p4))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_653385338684270323947857833862 : ((((p3 → ((False → p3) → ((p3 ∧ ((p2 ∨ p4) → ((p4 → p2) ∧ p2))) ∧ (((p4 → p2) → (p1 ∧ p1)) ∧ False)))) ∧ (p4 → p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227671335242217131747042911637 : ((False ∧ (p3 → False)) ∨ (p3 → ((p4 → p4) → (((p1 ∨ p1) ∨ (((p5 → p4) ∧ (p4 → ((p2 ∨ False) ∧ (p1 ∨ p1)))) ∨ p1)) ∨ True)))) := by
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
theorem thm_5_vars_61130385273232845467868951799 : ((False ∧ ((((p4 ∧ p1) ∨ ((True ∧ p1) ∧ False)) ∨ p4) ∨ ((p5 ∧ (True ∧ ((True ∧ p3) ∧ False))) → ((p1 → p4) → (p3 ∧ p4))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158764369972550685429483958616 : ((p4 ∧ ((True ∨ p1) ∧ ((p4 ∨ ((p3 ∧ (p1 → p5)) ∨ ((p3 → p5) → (p4 ∨ False)))) ∨ p4))) ∨ (p1 → ((p3 → (False ∨ p1)) ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112133803204156297829081359914 : (((False ∧ ((True ∧ (p4 → (((((False → p3) ∨ p1) → p4) ∨ p5) → p3))) → (p2 ∨ (p5 ∨ ((p5 → p1) ∧ p4))))) ∨ False) ∨ (p5 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66604526719881066225849508010 : ((True → ((True ∧ (((((False ∨ p2) ∧ p5) ∨ p4) ∨ p2) ∧ ((False ∧ (p3 ∨ p1)) ∨ (p5 ∧ p2)))) ∧ ((p1 → p5) ∧ (p2 ∧ p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_936152948736615561673939999565 : ((((p2 ∨ (True ∨ (False → ((p1 ∨ p3) ∨ p2)))) → ((((p2 ∧ (True ∨ p1)) ∧ (((p5 → p3) ∧ p4) → p5)) ∨ True) → (p2 ∧ p1))) → p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p2 ∨ (True ∨ (False → ((p1 ∨ p3) ∨ p2)))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : (((p2 ∧ (True ∨ p1)) ∧ (((p5 → p3) ∧ p4) → p5)) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- One of the premise coincides with the conclusion.
  exact h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324691666743409574684040180467 : (p5 ∨ ((p1 → (p4 ∨ p4)) ∨ ((False ∨ (True → (p1 → ((p4 ∨ ((((p1 → p4) → True) → p3) ∧ (p5 ∧ True))) ∧ p5)))) ∨ (p4 → True)))) := by
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
theorem thm_5_vars_207257580201172411883943807953 : ((((False → (p1 → p1)) ∨ p3) ∨ p3) → (p2 → ((((p4 → p1) ∧ (p5 → (p2 → p2))) ∧ p4) ∨ ((((p1 ∨ True) ∨ p2) ∧ p2) ∨ p3)))) := by
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_3054209241695177451834137119 : ((p5 → (p2 ∨ p1)) → (((((((False ∨ p4) → p5) → (True ∨ (True → p1))) ∨ (p1 ∨ (p4 → p3))) → p1) ∨ (True ∨ p4)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111400844768049462438228227614 : (((p1 ∨ (p3 → ((False ∧ ((p3 ∧ False) ∨ (True ∧ p5))) ∨ (p1 ∨ (((p2 ∧ ((p5 ∨ True) ∨ p5)) ∧ p5) → p1))))) ∧ True) ∨ (True ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136544816531198372315855101212 : ((((p1 ∨ p5) ∧ p3) ∨ (p5 ∨ (((p3 → True) → ((p1 ∧ p1) → ((p1 ∨ p1) → (True ∧ (False ∧ p1))))) → p5))) ∨ ((p2 ∨ False) → p2)) := by
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
    -- False on the left can always be used.
    apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_596146212832724840634793439890 : ((((((((p4 → p5) ∧ (True → p2)) → True) ∧ True) ∧ (p4 ∨ (((p1 ∧ (False ∧ p4)) → (p5 ∨ ((p4 ∨ False) ∧ p1))) → p4))) ∧ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_650428125631611020127474688361 : (((((((((p4 ∧ p4) → (False ∧ False)) ∧ True) → (p3 → p4)) → (p5 ∨ p2)) → (False ∧ (True ∨ (True ∨ (p5 ∧ True))))) ∧ (p1 ∧ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215007285307085498714906135745 : (((True ∨ p5) → (p4 → p3)) ∨ (((p3 → ((p2 → (p4 → p1)) → p5)) → (((p2 ∨ (True ∨ p3)) ∧ p2) ∨ (p4 ∧ p2))) ∨ (p2 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303813557824341912572595859272 : (p1 ∨ (((p3 ∧ ((True → ((((False ∧ ((p4 ∧ p3) ∨ True)) → (p1 → p5)) → p3) → p4)) → ((p3 ∧ False) ∨ (p1 ∧ p4)))) → False) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47036466797804848485036011439 : ((((((p2 ∨ ((False ∨ False) → (p3 → p2))) ∨ (((True → (True → p1)) ∨ (False → p1)) ∨ True)) → p4) ∧ (True → p4)) ∨ (p5 → p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232408308575605380390278741174 : (((p5 → p5) → p3) → (p1 ∨ ((((p4 ∨ (((p2 ∧ p4) → p2) → p2)) ∨ ((p4 ∨ (True ∨ (p4 ∨ p1))) ∨ p1)) ∨ (p1 ∧ p3)) ∨ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_111880703032222467695715157662 : (((((p4 ∨ p2) ∨ (((p1 ∨ False) ∨ (False → p2)) → ((p2 ∨ p3) ∨ (True ∨ p3)))) → (p1 ∧ ((p3 ∨ p4) ∧ p5))) ∨ p3) ∨ (p2 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50488718864219522067631708468 : (((p4 → ((((True ∨ p3) → True) ∨ (p4 ∧ (p5 → ((p1 → p2) ∧ p3)))) → (p2 → (p1 ∧ True)))) ∨ (p4 ∨ (p2 ∧ (p1 → p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44014673706979013446226787409 : (((((p4 ∧ ((((p5 → p1) ∧ True) ∧ (p3 → (False ∨ p1))) ∨ p4)) → (((p2 ∧ (p2 → p2)) ∨ False) ∨ True)) → (p2 → p3)) → p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115549257467504031093441794485 : ((((((True ∨ p4) ∨ p5) ∧ True) ∧ p1) ∧ (((p4 → True) ∧ p1) → (((True → ((p3 → p1) → p3)) ∧ p2) → (p2 → p3)))) ∨ (p1 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51310496717502220506206439273 : (((p3 ∨ ((((((p5 ∨ p4) → p5) ∨ p5) ∨ (p2 ∧ (p4 → False))) → (p3 ∨ p1)) ∨ False)) ∨ ((True ∨ p1) → ((True ∨ p3) ∨ False))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_804538879991484343151151199368 : (((p3 → (((p4 → (p3 ∧ (p2 ∧ p2))) → p4) ∨ (((False ∧ True) → p5) ∧ ((True ∧ p2) ∨ (p1 → (p3 → ((p4 ∨ p2) → True))))))) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h5
  -- Implications on the right can always be decomposed.
  intro h6
  -- Implications on the right can always be decomposed.
  intro h7
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135566166972372330057113847303 : (((p1 → ((False ∨ False) ∨ (p1 ∧ (True ∨ ((p4 ∧ p4) ∨ ((False ∨ p4) ∧ p4)))))) ∧ (((p5 → True) → p4) ∧ p5)) ∨ ((p5 → p5) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_611869040571764914000318742633 : (((((p4 → (False ∧ (p4 ∧ ((p2 ∧ (((True → False) ∨ p4) ∧ (True ∧ (p3 ∧ ((p1 ∧ (False ∧ p5)) ∧ False))))) → False)))) → p1) ∨ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_727288216324493569117303912246 : ((((p1 ∧ (False ∨ True)) ∨ ((False ∨ (((p3 → (((False → p1) ∨ True) ∧ True)) → (False ∧ False)) ∧ ((False ∧ p3) → (p3 ∨ True)))) ∨ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_482736343679040421426481152540 : (((((p5 ∨ p1) ∨ (p1 → (p3 → (p5 → False)))) → (((p4 → (p4 ∧ (p2 ∧ p5))) ∧ p1) ∨ (p5 → ((p4 → p3) ∨ (True ∨ p4))))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h4
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_601679286783420921497376187086 : ((((p3 ∧ (p5 ∨ ((((p5 → False) ∨ p5) ∨ (p2 ∨ p3)) ∨ (False → (p2 → ((p2 ∨ p5) ∧ ((False → (p2 ∧ p5)) → p1))))))) ∧ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_262410617341976510548051664075 : (True ∧ ((False ∧ ((((p4 → True) ∧ (((p5 ∧ p3) ∧ (((p2 ∧ ((False ∨ p3) ∧ p1)) → False) ∨ p3)) → p4)) → (p5 → p3)) → False)) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2688477410350529921267765278 : ((((p5 ∨ (p5 ∨ p5)) ∧ False) → p2) → ((((False ∨ p1) → p4) ∧ (False ∧ p2)) ∨ (p1 → (((p4 ∧ p5) ∨ (p1 → p4)) → True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135412548501689189996581443057 : ((((p4 → (True ∧ p4)) → (p3 → ((p5 ∨ (False → (p1 ∧ (p2 ∨ p3)))) ∧ (p1 ∧ False)))) ∨ (True ∧ (p3 ∧ True))) ∨ ((True ∧ p4) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53648670445336828243676580650 : ((((False → (p1 ∨ p1)) ∨ (p1 ∨ (p1 → (p4 ∨ p3)))) ∧ ((p1 ∨ (p3 ∨ p1)) ∧ (p2 ∧ ((False ∧ True) ∧ ((p4 ∧ p5) ∧ p1))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_746455683165527288412386168689 : ((((p2 ∨ p3) → (((((p2 ∨ p2) ∨ p4) ∧ (p4 ∨ p5)) → (((p1 ∧ p1) ∧ (((p3 ∧ p4) ∧ p1) ∨ (p2 → p1))) ∧ p3)) ∨ True)) ∨ False) ∧ True) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159213699426165243226473269233 : ((p2 → ((p1 ∧ p1) ∨ ((True → ((p4 ∧ p3) ∧ ((True → p4) → p2))) ∨ ((p1 → p2) ∧ p4)))) ∨ (((p4 → True) → p1) ∨ (p1 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_690238366682161339480230333954 : ((((p5 ∨ (False ∨ ((((p1 ∧ p4) ∨ p3) → (p4 → ((p4 ∧ p2) ∨ False))) ∧ False))) ∨ (p2 → (p1 ∨ (p2 → (p4 ∨ (p1 → True)))))) ∨ p3) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338432495536675121441710015951 : (p1 → ((p2 → (p5 ∧ (True → p4))) → (((((False → (p2 ∨ False)) → p4) → ((p1 ∧ p5) ∨ p4)) ∧ ((False ∧ p2) ∧ (p1 → True))) ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54704672508891850335930368546 : ((((((p5 ∧ p4) → p2) ∨ p3) ∨ (p1 → True)) → ((((p5 ∧ p2) → ((p3 ∧ (p2 ∨ (p2 ∨ True))) ∧ False)) ∧ p4) ∧ (p1 → p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190037238556565504699141027223 : ((((((p5 ∨ (False ∨ p5)) ∧ p4) → False) ∨ p1) ∧ p5) ∨ ((((p5 ∧ (True ∨ p1)) ∧ p2) ∨ (False ∨ (p5 → (p1 ∧ p5)))) ∨ (True ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263384012735473826813125671165 : (True ∧ ((((p5 ∨ p3) ∨ (((p3 ∨ ((False ∨ (True ∧ p1)) ∧ p5)) ∨ (True ∧ ((p4 → p5) → True))) → p1)) → p4) ∨ (False → (True → p2)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134908142923489665874654869072 : ((((p2 ∧ (False ∧ (((True → p3) ∨ p2) ∨ (((p5 ∨ ((p3 ∨ p1) ∧ p1)) → p4) ∧ False)))) ∧ p4) ∧ (p1 → p3)) ∨ ((p2 ∨ False) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58592086154648992412396192590 : (((False → True) ∧ ((p4 ∧ (((p4 → (p5 ∧ p2)) ∧ p3) ∧ ((((p2 ∧ (p1 → (p1 → (p3 ∧ True)))) → p1) → p1) ∧ p4))) → p2)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
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
  let h7 := h5.left
  let h8 := h5.right
  -- Conjunctions on the left can always be decomposed.
  let h9 := h6.left
  let h10 := h6.right
  -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
  have h11 : p4 := by
    -- One of the premise coincides with the conclusion.
    exact h10
  -- We have shown the premise of h7, we can now drive its conclusion.
  let h12 := h7 h11
  -- We need to get the right conjuct of h12 based on <expert-advice>.
  let h13 := h12.right
  -- One of the premise coincides with the conclusion.
  exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178927698326719811990892198616 : (((p4 → p2) ∧ (p3 → (((((p2 ∨ False) ∨ False) ∧ p4) ∧ p1) ∨ p4))) ∨ (p3 → (((p5 ∧ p5) ∧ p1) ∨ (((True ∧ False) → p2) ∨ p4)))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_787103667039692547240360887397 : (((p4 ∨ ((p5 → p4) ∨ ((((True ∧ p2) ∧ (p2 ∧ p3)) → ((False → p2) → p1)) ∧ ((p1 ∧ (True → ((p2 ∧ p3) ∨ p3))) ∨ True)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68763038712560710093156043645 : ((p4 → ((False ∨ (((p4 ∨ True) ∧ (p4 → p2)) ∨ (False ∧ (p1 ∨ p5)))) ∧ ((p1 → False) ∨ ((False → (p3 ∧ (p1 ∧ p4))) ∨ True)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337413293373961407971826633093 : (p1 → (((p3 ∧ ((p3 → p5) ∧ (((True ∨ ((p4 ∨ p3) ∧ (False → (p3 → p5)))) → (p1 ∧ p2)) → p3))) ∨ p5) → (p5 ∧ (p4 ∨ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h8 : p3 := by
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h9 := h6 h8
    -- One of the premise coincides with the conclusion.
    exact h9
  case inr h10 =>
    -- One of the premise coincides with the conclusion.
    exact h10
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- Conjunctions on the left can always be decomposed.
    let h14 := h13.left
    let h15 := h13.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h16 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46934386104726226987872203622 : ((((p1 ∧ ((((p4 → p5) ∧ ((p2 ∨ False) ∨ (p1 ∨ ((p2 → p1) ∧ (p4 ∨ p5))))) ∧ (p2 ∧ False)) ∧ p1)) ∨ True) ∨ (p3 ∨ p4)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59816422801763116422706137187 : (((p3 ∧ True) → (p5 → (((p3 → (p5 ∧ (((p3 → p1) → p3) → p4))) → p2) → ((p5 ∧ p4) → ((p1 ∨ p3) ∧ (p4 ∧ True)))))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h1.left
  let h8 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h7
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h9 := h4.left
  let h10 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h11 := h1.left
  let h12 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h10
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158135436716855184031171600422 : (((((p5 ∨ p1) ∧ p5) → p1) ∨ ((False ∨ ((p2 → p5) → (p4 ∨ (True ∧ p2)))) ∨ (p1 → True))) ∨ (p4 ∧ (p4 ∨ (False ∧ (False ∨ p2))))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115242742562220518280910727793 : (((((p1 ∨ (False ∨ (p2 ∧ p2))) ∧ p3) ∧ (p2 ∨ p1)) ∨ ((False ∧ ((p3 ∨ p2) → p1)) → (p4 ∧ (False → (p1 ∧ p4))))) ∨ (p4 ∧ p2)) := by
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
  -- False on the left can always be used.
  apply False.elim h2
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h4
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65786188839551649281095888738 : ((p4 ∨ ((((p3 ∨ ((p5 ∨ p5) ∧ True)) ∧ p3) → ((True ∨ p2) ∧ False)) ∧ ((True ∨ (p4 ∧ (p4 → p1))) ∧ (True → (p5 ∧ True))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319754384473397298536720196830 : (p4 ∨ ((p2 ∧ (((False ∧ p4) ∧ p3) ∨ p3)) ∨ (((True ∨ ((p3 → ((p1 ∧ False) ∧ p4)) ∨ (p4 ∧ ((p4 → p4) → p5)))) → True) ∨ p3))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192712487607070047535696848264 : (((((p1 ∧ p2) ∧ p2) ∨ (p3 ∧ (p1 → p1))) → p5) → (True → (p4 → (((p3 → (((p5 ∧ p4) ∧ p4) ∨ (p3 ∨ p3))) → p2) ∨ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_352896194231800490714690702152 : (p4 → (True ∧ ((p3 ∨ (p3 → p5)) → ((p1 ∧ (True ∧ (p3 → p1))) ∨ (((((p4 → (False ∨ (p2 ∧ p4))) ∨ p5) ∨ p1) ∨ True) ∨ p4))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200019621102146974086545512432 : ((((False → p1) ∨ (p3 → p4)) → (True → p4)) → (p1 ∨ ((((False ∨ ((p3 ∧ p1) → (p4 → p4))) ∧ p1) ∨ (p3 ∨ False)) ∨ (False → p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_325111659030563918762617466064 : (p5 ∨ ((p4 → p3) → (p5 ∨ (True ∧ ((((p2 ∧ p5) ∨ p1) → p2) → ((p4 → p3) ∨ (((p4 ∨ p5) ∧ p3) ∧ (p4 → (p5 ∨ False))))))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h4 : p4 := by
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h4
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164454877385188603252830589777 : (((((p1 ∧ p5) ∨ ((((p3 ∧ False) ∨ (False ∧ p4)) ∧ (p1 ∧ p3)) ∨ p1)) ∧ p3) ∧ False) ∨ (((True ∧ ((False → p5) → p2)) ∧ p5) → p5)) := by
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
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57161084780476576867619575311 : ((((p1 ∧ p3) ∨ False) ∨ (((True ∧ (p3 ∧ ((p4 → p4) → p1))) ∧ ((((p1 ∧ (p2 ∧ p3)) ∨ False) → p1) → (p1 ∨ p1))) ∨ True)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156776707595163073335332516073 : ((((p4 → True) → (True → ((p4 ∨ ((((p2 ∨ (p1 → p2)) ∧ p3) ∧ p4) ∨ p2)) ∧ p4))) ∧ p4) ∨ ((p4 ∧ True) → (p5 ∨ (p5 → True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65637164286289375255451932897 : ((p4 ∨ (((((p4 → (p1 → ((p3 ∧ p4) ∨ p3))) ∨ (p4 → False)) ∨ (False ∧ (p4 → False))) ∨ ((p4 → (p4 ∧ p3)) ∨ True)) ∨ p2)) ∨ p2) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301157332456980192209437088901 : (False ∨ ((p2 ∧ ((True ∨ p5) ∧ (p2 ∧ (p2 ∨ False)))) ∨ (((p5 ∧ (((p2 ∨ False) ∧ (p3 ∧ p5)) ∨ False)) → (p3 ∨ True)) ∨ (p2 ∧ p1)))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h6.left
      let h9 := h6.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h10 =>
      -- False on the left can always be used.
      apply False.elim h10
  case inr h11 =>
    -- False on the left can always be used.
    apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158442575404453182809671034649 : (((p3 ∨ False) ∨ ((((p3 ∨ (((True ∨ p4) ∨ p2) ∨ (p5 → p5))) ∨ p1) → (p1 → True)) → p3)) ∨ (False ∨ (True ∨ (False → (p4 → p3))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_4316317758059702138564733859 : (True → (p1 → (((p4 ∨ (p5 ∧ False)) ∨ (((p5 ∧ (p1 → p5)) → (False → False)) ∧ (p5 ∨ (p4 ∨ (True → (p2 ∧ p3)))))) ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52703780373041636210674109824 : (((p4 → (((((p3 ∨ True) ∧ (p2 → p3)) ∧ (p4 ∧ p5)) → False) ∨ True)) ∨ (True → (p3 ∨ (p5 ∧ ((False ∨ (p2 ∧ p1)) ∧ p4))))) ∨ p1) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258324257272795990536409309279 : ((p5 ∨ True) → (p3 ∨ (p5 → (((p4 ∧ (p3 ∧ p3)) → (((p2 ∨ (p2 → (p1 ∨ (p4 ∧ False)))) ∧ True) ∧ (p3 ∧ (p2 → p3)))) ∨ True)))) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305723965140678180529770523613 : (p1 ∨ ((p4 → (True → ((p5 → ((p2 → p5) ∧ p1)) ∧ p2))) → ((((((p2 ∨ True) ∧ p2) → p1) → False) ∨ p2) ∨ (p4 → (p1 → True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135676147956729834249254927209 : (((p4 → (((True ∧ ((p4 ∧ p3) ∨ ((p4 → (p4 → p4)) ∨ p3))) ∧ p4) ∧ p4)) → ((p3 ∧ (p3 ∧ p1)) ∨ p2)) ∨ ((p1 ∨ p5) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54074244356670071361205245245 : ((((p2 → (p2 ∧ p2)) → ((p4 ∨ p2) ∨ (p3 → p5))) → ((p2 ∧ ((((False → (True ∨ True)) → p3) → p2) → (p1 ∧ p5))) ∧ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206093876289504835167051549565 : ((p3 ∧ (p4 ∨ (p2 ∨ (p3 → p5)))) ∨ (True → ((((((p2 ∧ (False → ((True → p5) → p4))) ∧ (p2 ∧ p5)) ∨ p2) ∧ p3) ∨ p4) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_704280612859538774876916302840 : ((((((p1 → p1) ∧ (p5 → p2)) ∧ ((p4 ∨ False) → False)) → (p3 → (((((p3 ∨ p5) ∧ p1) → ((p5 → True) ∨ True)) → p4) ∨ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214903616516112957397458588429 : (((p4 → p3) ∨ (False ∧ p5)) ∨ ((p4 ∨ ((p2 ∧ p2) ∧ (((False ∧ p2) → (p3 → p4)) → ((p5 → (False → False)) ∧ True)))) ∨ (p5 → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179167096754122189325170509419 : ((p2 ∧ (p1 ∧ ((((p1 → p4) ∧ p4) → p5) → ((p5 ∨ False) → p5)))) ∨ (p2 ∨ ((p1 → p3) → (p5 → (p2 ∨ (True ∨ (True ∨ p5))))))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157473779966328334777685138057 : ((((False → (((p2 → ((False ∧ p4) ∧ ((p5 → p5) ∧ p1))) → p5) → p4)) → p2) ∨ (p2 ∧ p3)) ∨ ((p5 → True) ∧ ((p4 → p5) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191987380370837038273639252276 : ((p1 → (((True ∨ (False → p5)) → (p5 ∨ p4)) ∧ p3)) ∨ ((((False → (p1 ∨ (True → p2))) ∨ ((p2 → True) ∧ (p5 ∧ True))) ∨ p2) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185458366647377328091598283951 : ((p1 ∨ ((p5 ∨ ((p4 ∧ (p4 ∧ (p1 → p5))) ∨ True)) ∧ p5)) ∨ (((p2 ∨ p1) ∨ ((p1 ∨ (p1 ∨ False)) ∧ p1)) ∨ ((p5 → True) ∧ True))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150032803567458044284984662760 : ((p5 ∨ (True ∧ (p4 → ((p5 ∧ p5) ∨ ((p1 ∧ p2) ∨ ((p4 ∨ (p1 ∧ (p4 ∨ p2))) ∨ (False → p3))))))) ∨ (p4 ∧ ((p1 ∧ p4) ∧ p1))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_229528699087128452199255434638 : ((p2 → (p4 ∨ p3)) ∨ (((((p5 → (p5 ∧ (p5 ∧ (((p1 ∧ True) ∨ (p2 ∧ p5)) ∧ p2)))) ∨ p2) ∨ False) ∨ ((False → p4) ∨ p1)) ∨ p4)) := by
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
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263748116010033519824865053292 : (True ∧ ((p5 ∨ ((p5 ∧ p3) → ((((p4 ∧ (p4 → (p3 ∧ False))) ∨ p4) → (p2 ∧ p5)) ∨ p1))) → (False ∨ (((p2 ∨ p5) ∨ True) ∨ p3)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152308246233188690094903721244 : (((((p5 → p1) ∨ p4) ∨ p3) ∧ (((True → (p4 ∧ (p3 ∨ ((p3 → p5) ∧ (True ∨ p2))))) ∧ True) ∧ p3)) → ((p2 ∧ p5) ∨ (p4 ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h3.left
      let h7 := h3.right
      -- Conjunctions on the left can always be decomposed.
      let h8 := h6.left
      let h9 := h6.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h3.left
      let h12 := h3.right
      -- Conjunctions on the left can always be decomposed.
      let h13 := h11.left
      let h14 := h11.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h10
  case inr h15 =>
    -- Conjunctions on the left can always be decomposed.
    let h16 := h3.left
    let h17 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h18 := h16.left
    let h19 := h16.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_887650846516343762207863593267 : ((((((((((p4 → (p3 ∧ p2)) → (p5 → p2)) → False) ∧ ((p3 → (p2 ∧ False)) ∧ p4)) ∧ p1) ∧ True) ∨ (True ∨ p5)) → (True → False)) → p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((((((p4 → (p3 ∧ p2)) → (p5 → p2)) → False) ∧ ((p3 → (p2 ∧ False)) ∧ p4)) ∧ p1) ∧ True) ∨ (True ∨ p5)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
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
  -- False on the left can always be used.
  apply False.elim h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161585925219542611973684360596 : ((True ∨ ((p5 → (p5 ∧ True)) → (p3 ∨ ((p1 → (False ∨ False)) ∨ (p4 ∧ (p3 ∨ (False ∧ p3))))))) → ((p3 ∨ ((p1 ∨ p1) ∨ p3)) ∨ True)) := by
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
theorem thm_5_vars_768766375617895462942600677568 : (((p5 ∧ ((False ∧ ((True → (p1 ∧ (False ∨ True))) ∨ p3)) ∨ ((((((False ∨ (p2 → (True ∨ p4))) → p5) → True) ∧ p2) ∨ p5) ∨ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313063524139198153229159746425 : (p3 ∨ (((p3 ∨ (True ∨ ((p1 → p5) ∨ (p5 → (p5 ∧ (p2 ∨ (p5 ∨ (p2 ∧ ((False ∨ False) ∨ (p2 ∧ (p1 → p1))))))))))) → p4) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113589043986998469141584751904 : (((p4 ∧ ((((True ∧ (p2 → p1)) ∨ ((p3 ∨ p4) ∧ ((p5 → False) → ((True ∨ p3) → p1)))) ∨ p1) ∨ p5)) ∨ (False ∧ p1)) ∨ (p1 → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_624013722873949910704920591594 : ((((p2 ∨ ((((((p4 ∧ p1) ∧ (p5 ∧ ((False → (p2 ∧ p1)) ∨ p3))) → p2) ∨ (p3 ∨ p2)) ∧ p2) ∧ (p5 → (p3 ∨ p3)))) ∨ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56322763710009188350764622198 : ((((False → (p3 → p3)) ∧ p5) → (((True ∨ (p1 ∧ (p2 → ((p2 → p5) ∨ p4)))) → p2) ∨ (True ∨ ((p3 ∧ p5) ∨ (False ∧ p3))))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135602045415139142371871775275 : (((((p4 → False) ∧ True) → (((p5 ∨ p1) ∧ ((p4 ∧ p3) → p4)) ∧ (p1 ∨ p5))) ∨ (False → ((p2 → p2) ∨ p1))) ∨ ((p1 ∨ p3) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39278855983973744126179983428 : (((p1 ∧ (((p5 ∧ (True ∨ ((((p5 ∧ p2) ∨ (p3 ∨ ((False ∧ p1) → True))) ∧ p1) ∧ True))) ∧ ((p3 → p5) ∧ p3)) ∨ p2)) ∧ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113252472356094124091990371248 : ((((False ∨ (True → (p5 ∨ ((True ∧ ((p5 → (True → (p2 ∧ False))) → p4)) ∨ (p1 ∨ p1))))) ∨ (True ∧ p2)) ∧ (p3 → p2)) ∨ (p2 → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350138631032070929442136346996 : (p4 → (((((False ∨ (p2 ∨ (p2 → True))) ∧ (p3 → (p4 ∧ False))) ∨ True) ∧ (p3 ∧ (((False ∨ (p2 ∧ p3)) ∨ (p3 ∧ p5)) ∨ p5))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207819239830667795396806708283 : (((p4 → ((False → p4) ∨ p3)) → p5) → ((p1 ∧ ((p2 → p4) ∧ p5)) → ((((p2 → (p3 → p3)) → ((p5 ∨ p3) ∨ p1)) ∧ True) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136578195324607637443133291525 : (((False ∧ (False ∧ p2)) ∨ ((p2 → False) → ((p3 ∨ (((p5 ∨ p1) → (False ∨ True)) ∧ p3)) ∨ ((True ∧ p1) → p1)))) ∨ ((p1 ∧ p1) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



