variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_606203643771925818288987234792 : (((((((((p4 → (p3 ∨ (False → (p5 ∧ p2)))) ∧ p3) ∧ p5) → (p1 ∨ (((True → (p3 ∧ p5)) → p4) ∨ True))) ∧ p1) ∧ p5) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207556788777144126838108879595 : (((((False ∨ p5) ∨ p1) ∨ p1) → p2) → ((p2 → p5) ∨ ((p1 → (((p4 ∨ p4) → True) → (False → (((p4 ∧ p5) ∨ p4) → p5)))) ∨ p5))) := by
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
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- False on the left can always be used.
    apply False.elim h4
  case inr h9 =>
    -- False on the left can always be used.
    apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_689178568832638116278603014983 : (((((((p4 → (p5 → (True ∧ p5))) → (p1 ∨ (False → p4))) → (p4 → p5)) → p1) ∨ (False → ((p5 → (p2 ∨ p2)) → (True → p3)))) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319819525763776474001421631738 : (p4 ∨ (((p4 ∧ (p5 ∨ False)) → p4) ∧ (((False ∨ p2) ∨ (((False → p1) → (p4 → p4)) → p2)) ∨ (((True → p3) ∧ (p1 ∧ True)) → p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h5
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h6
  -- Conjunctions on the left can always be decomposed.
  let h7 := h6.left
  let h8 := h6.right
  -- Conjunctions on the left can always be decomposed.
  let h9 := h8.left
  let h10 := h8.right
  -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
  have h11 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h7, we can now drive its conclusion.
  let h12 := h7 h11
  -- One of the premise coincides with the conclusion.
  exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_873247237348891724539978227127 : ((((p2 → ((True ∧ ((p3 → (((p3 ∧ p2) → (p5 ∨ False)) ∨ ((p4 ∨ ((p3 ∨ p2) → p2)) → False))) ∧ (p1 → p5))) ∨ p2)) → False) → p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p2 → ((True ∧ ((p3 → (((p3 ∧ p2) → (p5 ∨ False)) ∨ ((p4 ∨ ((p3 ∨ p2) → p2)) → False))) ∧ (p1 → p5))) ∨ p2)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- False on the left can always be used.
  apply False.elim h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40324244871516360903539073030 : (((((((p2 ∨ (True ∨ (p2 ∧ (True ∧ p5)))) → ((p4 ∧ p5) ∨ ((p3 ∨ (True ∧ (True ∨ p3))) ∨ p5))) ∧ False) ∨ True) ∨ True) ∨ p2) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259697074321555978356845773694 : ((p1 → p1) → (((((True ∨ ((p2 ∨ p4) ∧ True)) → p2) → (True → p5)) ∧ True) ∨ ((p3 ∨ (p5 → p3)) → (p3 → ((False ∧ True) → p5))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_142090043165687658587930693624 : ((True ∧ (p1 ∧ (((((True ∧ p4) → p5) ∧ (p3 ∧ (p2 ∧ p1))) ∧ (True → (False ∧ p5))) → ((p3 → p4) ∧ p4)))) → (p4 ∨ (p5 ∨ True))) := by
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
theorem thm_5_vars_593003005387011743586409210185 : ((((((((p2 ∨ ((p3 → p2) ∨ ((p3 → ((True → False) ∨ p4)) ∧ True))) ∧ (False ∨ p3)) → p2) ∧ p4) ∨ (p2 ∨ (p5 ∨ p1))) ∧ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_622317205033073872476674082675 : ((((p3 ∧ (((p4 ∧ (((p2 ∧ (p3 ∨ ((p5 → (p5 ∨ (p3 → p2))) ∧ p3))) ∨ p2) → (True → (p2 ∧ p3)))) ∨ p3) → p1)) ∨ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199022942154918913497219775881 : ((((True ∨ (p2 ∨ (p3 → p3))) ∧ p5) ∧ True) → (((False → p5) → ((False ∨ p1) ∨ (False → ((p3 ∨ ((p5 ∧ True) → p4)) ∧ True)))) ∨ p5)) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134299753109837067455645540531 : ((((p4 ∨ False) → (p1 ∨ ((((p2 ∨ p3) ∧ (((p2 → True) ∨ (p2 ∧ True)) ∨ p1)) ∧ (False → p5)) ∨ False))) ∨ True) ∨ ((p5 → p4) ∨ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_662981683219307611023041844702 : ((((((p3 → True) ∧ p4) → (p3 → (((p5 ∨ ((((True ∧ p5) ∧ True) ∨ p1) ∨ p1)) ∧ ((True → p1) ∨ p5)) → True))) → (p1 ∧ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50810800385847663565039889432 : (((p3 → (((p2 ∧ ((p4 ∨ (True ∧ True)) ∧ p5)) ∧ ((p1 ∧ (True ∧ p2)) ∧ p5)) ∧ (p5 → False))) → (((p2 ∨ True) ∨ False) ∨ False)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313092712511373566037501825541 : (p3 ∨ ((((((p5 ∨ (p5 ∨ (p4 → False))) ∧ ((p2 ∨ ((True ∧ (p3 → (True → p5))) → p5)) ∧ p3)) → True) → p5) → (p2 ∧ p2)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307359386439155296210938645042 : (p1 ∨ (p4 ∨ (((True → False) ∨ (((True ∧ p1) ∨ p3) ∨ (((p3 ∧ False) ∧ ((p2 → ((p2 ∨ False) ∧ False)) → False)) → (p4 ∧ True)))) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- False on the left can always be used.
  apply False.elim h5
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_678819753313343516884785153924 : ((((False ∧ ((p3 → (((False ∧ p2) ∧ p5) ∧ (p2 ∧ (((p1 ∧ (p5 ∨ p5)) ∧ False) ∧ p5)))) → p2)) ∨ (False ∨ (True ∨ (p4 ∧ p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134529162296789733141539505785 : ((((((((p1 ∧ p4) → (False ∧ (False → True))) → p4) → ((p2 ∨ (True ∨ (p4 ∧ True))) → p4)) ∨ True) → p4) → p4) ∨ ((p3 → False) ∨ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((((p1 ∧ p4) → (False ∧ (False → True))) → p4) → ((p2 ∨ (True ∨ (p4 ∧ True))) → p4)) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65096497403739288320891132941 : ((p2 ∨ (p2 ∨ ((p2 ∨ (p3 → ((p5 ∧ (p3 ∧ p4)) ∨ ((p4 → (p3 ∨ p2)) → (p4 → (p2 ∨ p4)))))) ∨ ((True ∧ False) ∧ p5)))) ∨ p4) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47348490097287499229420458478 : ((((p3 → False) ∧ (p2 ∨ (False ∨ ((((((p2 ∧ True) ∧ ((False ∧ p4) → p1)) ∨ p4) ∨ p5) → p3) → (p5 ∨ p1))))) ∨ (True ∨ p3)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136593361324210811114439904594 : (((p1 ∨ (p4 ∨ p2)) ∨ ((((p2 → True) → (((p3 ∧ ((p1 ∨ p2) ∧ p1)) ∨ p5) ∨ p2)) ∧ True) ∧ (p2 → p5))) ∨ (p1 ∨ (p4 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112110148997842946639949814864 : ((((p5 ∨ p4) → (p4 ∧ ((p2 ∧ (p4 → True)) ∧ ((p3 ∨ p1) ∧ (True → (((p2 ∧ p4) ∨ (True ∧ p1)) ∧ False)))))) ∨ p1) ∨ (p1 → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49156476773329714783934861662 : ((((((((True ∧ p1) ∧ p4) → p4) ∧ p3) → p2) → ((((p1 ∨ (p4 ∨ False)) ∧ (p2 → p1)) ∧ p5) ∧ False)) ∨ ((True ∧ True) ∨ p2)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_82502208747528091766865413662 : (((True → (p1 ∧ ((p1 ∨ ((False ∧ p2) ∧ (True ∧ (p3 ∨ True)))) → (((False ∨ False) → True) ∧ True)))) ∧ (p1 → ((p2 ∧ p4) → p4))) → p1) := by
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
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314677120144042216033985599280 : (p3 ∨ (((((p4 ∧ (((p1 ∨ False) ∧ p3) ∧ (p4 ∧ p5))) ∨ (p5 ∧ False)) ∨ True) → False) → (p3 → ((p5 ∨ (p5 → False)) → (p2 ∧ p3))))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h5 : (((p4 ∧ (((p1 ∨ False) ∧ p3) ∧ (p4 ∧ p5))) ∨ (p5 ∧ False)) ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h6 := h1 h5
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h8 : (((p4 ∧ (((p1 ∨ False) ∧ p3) ∧ (p4 ∧ p5))) ∨ (p5 ∧ False)) ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h9 := h1 h8
    -- False on the left can always be used.
    apply False.elim h9
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h10 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h11 =>
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336223988979609148259556155279 : (p1 → ((((p4 ∨ ((True ∧ (p1 ∧ p5)) ∨ ((p5 ∧ (((p4 ∨ p1) → (p5 ∧ True)) ∨ False)) ∨ p1))) ∨ True) ∨ (p5 ∨ (p2 ∧ p3))) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56380830667279834598671322590 : (((((p4 ∧ p2) ∨ False) → p1) → ((p5 ∧ True) ∨ ((((False ∧ ((p1 → p3) → True)) ∨ p5) → p4) ∨ (p5 ∧ ((p4 ∨ p3) ∧ p1))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191033265149476291614693915907 : (((((p1 → p3) → p5) ∨ p3) → (p4 ∨ (p3 → p4))) ∨ (False → (((p4 ∨ (p4 ∧ (True → p5))) ∧ p3) ∧ (p5 → ((p3 ∨ True) ∨ p3))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_320485895677900141414665311918 : (p4 ∨ ((p4 → False) → ((((p3 → (p1 ∧ (True ∧ True))) ∨ p4) → p3) ∨ (True ∨ (True → ((True ∨ p4) ∨ (p1 ∨ ((p1 → p4) → p3)))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_318871262837800721550765135132 : (p4 ∨ ((((((p3 ∨ False) → p1) → (((p1 ∧ True) → p1) → p5)) ∧ (p2 → p3)) ∧ (((p4 ∨ p5) ∨ p5) → True)) ∨ (False → (False ∧ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41021911182168806192211286929 : ((((((False ∧ False) ∨ (p2 → (((p3 ∨ ((p3 ∧ (p5 ∧ p3)) ∨ False)) ∨ (p4 ∨ (p5 → False))) ∨ p5))) → p1) → (p1 → p4)) ∨ True) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197665453762004292363551758461 : ((((p2 → p1) ∨ (p1 ∧ p1)) → (p2 → p4)) ∨ ((p3 → p4) → (True ∧ (p2 ∨ (((p3 ∨ p4) ∧ p5) ∨ (((p5 ∨ True) → True) ∨ p3)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350931454905589170095749498664 : (p4 → ((((p2 ∨ (p1 → (p2 → p2))) → ((p4 → (((((p3 ∧ (p4 ∨ p3)) ∧ p3) ∨ False) ∨ True) ∨ True)) ∨ p3)) → False) ∨ (False ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_730954494152505071202300395842 : ((((True ∨ (p3 → p5)) → (p5 ∨ ((p3 ∨ (((True → True) ∨ (((p4 ∨ (p1 → False)) ∨ p4) ∧ p1)) → ((True → p3) ∨ p2))) ∨ True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_254841290464320118012479923602 : ((p3 ∧ p5) → ((((p2 ∨ ((True → False) ∧ p1)) ∨ p4) ∧ p3) ∨ ((((p2 ∧ (False → (p4 → p1))) → p4) ∨ (False → (False → False))) ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178771444772732675331887851714 : (((p1 ∧ (p2 → False)) ∧ ((p3 → (p4 ∨ ((p4 → p1) ∨ p4))) ∧ p2)) ∨ (((False ∨ p5) → (False ∨ False)) → (False → ((p2 ∨ p2) ∧ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_620346536627806194870351761864 : (((((p2 ∨ p1) ∨ (p2 ∧ (((p2 → True) ∨ ((p5 ∨ p4) ∧ ((True ∧ p3) → (p4 ∨ (False → p1))))) → ((p2 ∨ p2) ∨ p2)))) ∨ True) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_170419853859706590775937604122 : (((p4 ∧ (p3 ∧ p5)) ∨ ((p5 ∧ ((p3 ∨ p5) ∧ ((p5 ∧ True) → False))) → p4)) ∧ (((((p4 ∨ p1) ∧ p2) ∧ (False → True)) ∨ True) ∨ False)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h7 : (p5 ∧ True) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h2
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h8 := h5 h7
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h10 : (p5 ∧ True) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h9
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h11 := h5 h10
    -- False on the left can always be used.
    apply False.elim h11
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1354183304228336359183408261 : (((((p1 ∨ (False ∨ p5)) → False) ∨ ((p1 ∨ ((p2 ∨ (((p4 ∧ (p5 → True)) → False) → p5)) ∨ True)) ∨ p1)) ∨ p1) ∧ (p4 ∨ True)) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172837632125445551451930662499 : ((False ∧ (((((p1 ∨ p3) ∧ (False ∧ p5)) → ((p5 ∧ p5) ∨ True)) ∧ p2) ∨ False)) ∨ (((p2 ∨ False) ∧ (p2 → False)) → (True ∧ (p1 ∧ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h5 : p2 := by
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h6 := h3 h5
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- False on the left can always be used.
    apply False.elim h7
  -- Conjunctions on the left can always be decomposed.
  let h8 := h1.left
  let h9 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h10 =>
    -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
    have h11 : p2 := by
      -- One of the premise coincides with the conclusion.
      exact h10
    -- We have shown the premise of h9, we can now drive its conclusion.
    let h12 := h9 h11
    -- False on the left can always be used.
    apply False.elim h12
  case inr h13 =>
    -- False on the left can always be used.
    apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_778936211915346377964536766896 : (((p1 ∨ (p2 → (((p4 ∧ (p2 → False)) → ((p5 ∧ p1) ∨ (p4 ∧ (((((p5 ∧ p2) ∨ p4) → p5) ∨ p5) ∧ p1)))) ∨ (p5 → True)))) ∨ p1) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_688923534393746666707297931459 : (((((p1 ∧ (p5 ∨ (True ∧ (((p5 → (p1 → (p2 ∨ False))) ∧ True) ∧ p1)))) ∧ p4) ∨ (p2 → ((p3 ∧ p5) ∧ ((p4 → True) ∨ p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49801793030918180413950622015 : (((True → (((True ∧ p3) ∧ True) ∨ (p1 → ((((((p1 → p5) ∧ p4) ∨ p2) ∨ p2) ∨ p3) → (p2 ∧ p1))))) → (p4 ∧ (p4 ∧ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_743246347991807382101891241716 : ((((p4 → p5) ∨ ((p5 → (p2 ∧ p2)) ∧ (((((p1 ∨ (p2 ∨ False)) → p3) → p2) ∧ ((True → (p5 ∧ p2)) ∨ (p4 → False))) ∨ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54631654611509040915057353082 : (((((p5 ∨ p3) ∧ ((True ∨ False) → p3)) ∧ p4) → ((((p5 → True) ∧ ((p3 ∨ (p3 ∧ False)) ∧ p1)) ∨ (p1 ∧ True)) ∧ (p2 → p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158997845617401001390618221764 : ((p3 ∨ (p4 ∨ (((True ∧ (True ∨ True)) ∧ (p5 ∧ (p4 ∨ (p4 ∧ True)))) → ((p1 ∨ p1) ∨ False)))) ∨ (((False ∧ (p5 ∨ False)) → p2) ∨ p1)) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_774368163420362267607814729955 : (((False ∨ (((p1 ∧ (p2 ∧ p4)) ∨ (((False ∧ ((True ∧ p3) ∧ p5)) ∧ False) ∧ (False → (p5 ∧ p3)))) ∨ ((p3 ∧ (p5 → p3)) → True))) ∨ p3) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156878142698274447482602365237 : ((((p5 → ((p3 ∨ (((p2 ∧ p2) ∧ p5) ∨ (True ∨ False))) ∧ (p4 ∨ (p1 ∧ False)))) ∧ True) ∨ True) ∨ ((p1 → (False → p3)) ∨ (p5 ∨ False))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_761289423789123099015339132841 : (((p3 ∧ ((((((p1 → True) ∨ True) ∨ ((p5 → p1) → (False → (p5 → p3)))) ∧ (p2 ∧ ((p1 ∨ (True ∧ p1)) → p1))) → p1) ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317574523166744587189168123828 : (p4 ∨ (((((p1 ∨ (((p3 ∧ ((p2 → (p1 → p1)) ∧ (p3 ∧ ((False → p5) ∨ p1)))) ∨ p3) ∨ False)) ∨ (False ∧ p4)) ∧ p4) ∧ False) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190542651665077258008673032381 : ((((False ∨ ((p5 → p1) ∨ p4)) ∧ (p5 ∧ p1)) → p3) ∨ ((True ∧ (p4 ∨ (((False ∧ p2) ∨ (p3 → (p5 ∧ True))) ∨ p5))) → (False ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Conjunctions on the left can always be decomposed.
        let h8 := h7.left
        let h9 := h7.right
        -- False on the left can always be used.
        apply False.elim h8
      case inr h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117280619703172660522642181749 : ((False ∧ ((False ∧ (p3 → ((p3 → ((((p3 → p1) ∧ False) ∨ p4) ∨ (p2 ∧ (p1 → False)))) ∨ (p1 ∧ (p3 → False))))) ∨ True)) ∨ (True ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47304169721929159230051802058 : ((((p4 → (p2 ∨ p5)) ∧ (p2 ∨ ((((p5 → (True ∧ (False ∧ False))) ∨ p2) ∨ (p1 ∨ (p4 ∧ (p1 ∧ True)))) ∧ p5))) ∨ (True ∨ p3)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114481681699710122282122207199 : (((((((((p3 ∧ (False → (p1 ∧ False))) → p5) → p1) → p5) ∧ True) ∧ p3) → (p5 ∨ False)) → ((p2 ∧ (True → p2)) ∧ p3)) ∨ (p2 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42816132025108493486221079399 : (((p1 → (((p2 → ((p3 ∨ False) ∧ (p2 ∨ ((((p3 → p2) → p5) → True) → p4)))) ∧ (p4 → p3)) → (True ∧ (p5 ∧ p2)))) ∨ True) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248198332557413070961023471144 : ((p2 ∨ p1) ∨ ((((((p2 ∧ True) → False) ∧ True) ∨ p2) ∨ ((((p4 → p4) ∧ (p4 ∨ ((p2 ∧ p3) ∧ p3))) ∨ True) ∨ (p5 ∨ p4))) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_657541136715369468427350956667 : (((((p1 → False) ∨ (p5 → (((p2 ∨ (p1 → (p1 → p3))) ∨ False) → (((p1 ∨ ((p3 ∨ p1) ∨ p4)) → False) ∨ p5)))) ∨ (p5 ∧ p2)) ∨ p4) ∧ True) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1
  case inr h6 =>
    -- False on the left can always be used.
    apply False.elim h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_183359439033176294331367365716 : ((True ∨ ((p3 → (True ∨ ((True ∧ p1) ∨ p2))) ∨ (False → True))) ∧ ((True → p2) → ((p2 ∨ p1) ∨ ((((p3 ∨ True) ∧ p1) → False) ∨ p1)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323791938061749220925178169664 : (p5 ∨ (((p4 ∨ ((((True ∧ p5) ∧ ((p4 → p5) ∧ True)) ∧ p5) → p1)) ∨ ((False ∨ p4) ∨ p4)) ∨ ((((p1 → p5) ∨ p1) → p3) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205283085003985192631888942955 : (((False ∧ (True ∨ True)) ∨ (False ∨ False)) ∨ (((((True ∨ (p2 ∨ p1)) ∧ p3) → ((p5 → p2) ∧ p5)) ∧ p2) ∨ (p5 ∨ (True ∧ (False → p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_311029426097201826700543132033 : (p2 ∨ ((p1 ∧ p4) ∨ ((p1 ∧ (p2 ∧ p1)) → ((((False ∧ p3) ∨ p4) ∨ p1) ∧ ((True ∨ p4) ∨ ((False ∨ p4) ∨ ((False → p2) ∧ p2))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h5
  -- Conjunctions on the left can always be decomposed.
  let h6 := h1.left
  let h7 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h7.left
  let h9 := h7.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341085772555739327295813569047 : (p2 → ((p1 → ((((((p3 → p1) ∨ p2) ∧ p4) ∨ (((p4 ∧ p4) ∧ p4) ∧ False)) ∨ (True ∧ ((p5 → p1) ∧ (False ∧ p2)))) ∧ p4)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_703281885226857255366817151102 : ((((p3 ∧ (False → (p4 ∨ (False ∨ ((True ∨ True) ∨ p4))))) ∨ ((p3 ∧ True) ∨ (((((p3 → p5) → p1) → (p4 → p3)) ∧ p2) ∨ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_255252929817858721782050973084 : ((p4 ∧ p5) → (((((p5 → ((p3 → ((p5 ∨ p4) → False)) ∧ (p2 → p5))) ∨ (p3 ∨ True)) ∧ ((p4 ∨ False) → p2)) ∨ p1) ∨ (p2 → p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305878949114570180045332480242 : (p1 ∨ (((p4 ∨ False) ∧ (p4 ∨ (p2 ∨ p1))) ∨ (((p5 → (p5 → ((True → True) → p3))) → p5) → (((p3 → p3) → False) → (p1 ∧ p5))))) := by
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
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (p3 → p3) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h3
  -- False on the left can always be used.
  apply False.elim h5
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h6 : (p3 → p3) := by
    -- Implications on the right can always be decomposed.
    intro h7
    -- One of the premise coincides with the conclusion.
    exact h7
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h8 := h2 h6
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187430196439587187772181125405 : ((p5 ∧ (((p1 → p4) → p1) → (p1 ∧ (p4 ∧ (p4 → p1))))) → (((((p5 ∨ p4) ∧ (p1 → p1)) → True) ∧ ((p1 ∨ p2) → p3)) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133670967360282328514051429790 : (((((p1 ∨ (((p2 ∨ ((False ∨ p5) ∨ p5)) ∨ (p4 ∨ p2)) ∧ True)) → ((p5 ∨ p3) ∨ p3)) → (False ∧ p1)) ∧ p2) ∨ (p2 ∨ (p2 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136228789325134791474146285230 : (((((p5 ∧ p5) ∧ p5) ∧ (False ∨ p5)) ∨ (((p3 → (p2 ∧ (p5 ∧ (p1 ∨ p1)))) ∨ (p5 → True)) ∨ (p4 → p5))) ∨ (p1 ∨ (p3 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_888787222929321898293845008051 : (((((p4 ∨ ((p1 ∧ ((p3 → (p1 ∧ p3)) → p4)) → p3)) ∨ ((p5 ∨ ((False ∧ False) ∨ (True → (False ∨ p3)))) ∨ True)) → (p5 ∧ p2)) → p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p4 ∨ ((p1 ∧ ((p3 → (p1 ∧ p3)) → p4)) → p3)) ∨ ((p5 ∨ ((False ∧ False) ∨ (True → (False ∨ p3)))) ∨ True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- One of the premise coincides with the conclusion.
  exact h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204104249259321256502547151090 : (((((True ∨ p4) ∧ p1) ∧ p4) ∧ p1) ∨ (((((p3 → p5) → False) ∧ ((((p1 → p4) ∧ p1) → (True ∧ (p1 ∧ p4))) → p3)) ∧ p5) → p3)) := by
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
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h6 : (p3 → p5) := by
    -- Implications on the right can always be decomposed.
    intro h7
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h8 := h4 h6
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60134945077637023740502763780 : (((p4 ∨ False) → ((True → (False ∧ False)) → ((p1 ∨ ((p2 ∧ (p1 ∧ (p3 ∧ ((p2 → (p3 ∧ (False → True))) ∨ False)))) ∨ p1)) ∧ p1))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h4 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h5 := h2 h4
    -- We need to get the left conjuct of h5 based on <expert-advice>.
    let h6 := h5.left
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- False on the left can always be used.
    apply False.elim h7
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h8 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h9 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h10 := h2 h9
    -- We need to get the left conjuct of h10 based on <expert-advice>.
    let h11 := h10.left
    -- False on the left can always be used.
    apply False.elim h11
  case inr h12 =>
    -- False on the left can always be used.
    apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44893943019044547906339399377 : ((((True ∧ (p4 ∨ False)) → (p5 ∨ (p5 → (((p4 → p1) ∧ True) → ((p3 ∨ p4) → (((p5 ∧ True) ∧ (True ∨ p4)) → True)))))) → p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356431808493213668621225836053 : (p5 → (((p5 ∧ (((False ∨ p1) → (p2 ∨ p2)) → (p1 ∧ p4))) ∧ p4) ∨ ((p5 → (False ∧ False)) → (p3 ∧ ((True ∧ (p4 ∨ True)) ∨ p1))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : p5 := by
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- False on the left can always be used.
  apply False.elim h5
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43321183662420610199192374484 : (((((p3 ∨ (True ∧ ((p3 ∧ (((p1 ∨ (p2 ∧ ((p2 → p3) ∨ p2))) ∧ p4) → (p3 ∧ (True ∨ p2)))) ∨ False))) ∨ p3) ∨ True) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_775436719383281862910761915633 : (((False ∨ (p3 ∧ (((p2 → (((True ∨ (p2 → False)) ∨ (False ∨ (((p1 ∧ p2) ∧ (True ∨ False)) ∨ p3))) → (p1 ∧ p2))) ∨ p5) ∧ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_130158456292880138837954375401 : ((((p5 ∨ p3) ∨ (p5 ∧ (((p2 → ((True ∧ False) ∨ (p2 → (False ∨ p1)))) → (p3 ∧ p2)) ∧ p4))) ∨ (p3 → True)) ∧ (p2 ∨ (True ∧ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_702451106830402667891409328632 : (((((False ∨ ((p3 ∧ p3) → (p2 ∨ (p5 ∧ p1)))) ∨ p4) ∨ (True ∨ (((p3 → p2) ∨ ((p1 → (False → (p1 → False))) ∨ True)) ∨ True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186270145729178973644386708370 : (((((p5 → (True → p2)) → ((p1 ∨ False) → False)) ∨ True) → False) → ((((p1 → False) ∧ ((False ∨ (p5 ∨ p1)) → (False ∧ p1))) ∧ p3) ∧ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : (((p5 → (True → p2)) → ((p1 ∨ False) → False)) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- False on the left can always be used.
  apply False.elim h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h9 : (((p5 → (True → p2)) → ((p1 ∨ False) → False)) ∨ True) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h10 := h1 h9
      -- False on the left can always be used.
      apply False.elim h10
    case inr h11 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h12 : (((p5 → (True → p2)) → ((p1 ∨ False) → False)) ∨ True) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h13 := h1 h12
      -- False on the left can always be used.
      apply False.elim h13
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h14 =>
    -- False on the left can always be used.
    apply False.elim h14
  case inr h15 =>
    -- Disjunctions on the left can always be decomposed.
    cases h15
    case inl h16 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h17 : (((p5 → (True → p2)) → ((p1 ∨ False) → False)) ∨ True) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h18 := h1 h17
      -- False on the left can always be used.
      apply False.elim h18
    case inr h19 =>
      -- One of the premise coincides with the conclusion.
      exact h19
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h20 : (((p5 → (True → p2)) → ((p1 ∨ False) → False)) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h21 := h1 h20
  -- False on the left can always be used.
  apply False.elim h21
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h22 : (((p5 → (True → p2)) → ((p1 ∨ False) → False)) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h23 := h1 h22
  -- False on the left can always be used.
  apply False.elim h23



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_247953305043465990252899779355 : ((p1 ∨ p4) ∨ (((False ∨ ((p1 ∧ ((False → p3) ∨ p3)) → (((False → p3) ∧ (p2 → (p4 ∨ (p2 ∧ p4)))) ∨ (p1 ∨ p4)))) ∨ p2) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309821223224748062975709886711 : (p2 ∨ ((p2 → ((p5 → ((p2 ∨ ((p2 ∧ (p1 → p1)) ∨ False)) → (True ∧ False))) ∨ (p3 → (p3 ∨ p3)))) ∨ (((False ∧ p2) → p2) ∧ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148709721899536584994261677203 : ((((p5 ∨ ((True ∧ p5) ∧ p5)) ∧ (p3 → p5)) → ((p5 → (p2 ∨ p5)) → ((p1 ∧ p2) ∧ (p3 → p1)))) ∨ (True → (False → (p2 ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136101118799617680904723263761 : ((((p2 → ((False → False) ∨ (p2 → True))) → p2) ∨ ((False → ((p5 ∧ (p3 ∨ p2)) → p2)) ∧ (False → (True ∧ p3)))) ∨ ((p5 → False) → p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- False on the left can always be used.
    apply False.elim h1
  case inr h6 =>
    -- False on the left can always be used.
    apply False.elim h1
  -- Implications on the right can always be decomposed.
  intro h7
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244667184928289894336717421347 : ((False ∧ p5) ∨ (p5 → (False ∨ ((False ∧ p2) ∨ (((p4 ∨ False) ∧ p2) ∨ (True → (((p2 → (p1 ∧ p5)) ∨ ((True → p4) ∧ p5)) ∨ True))))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177901242131303538780564909505 : (((((p2 → (p4 ∨ ((False ∧ False) → p1))) → p4) ∨ (p4 → p2)) ∨ True) ∨ ((p2 ∨ (p3 ∨ p1)) → ((True ∨ p2) → (p4 → (False ∨ p3))))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173150859892658881885121270346 : ((p3 ∨ ((p5 ∧ (p4 → (p1 ∧ p3))) → (p2 → (p5 ∧ ((False ∧ True) ∧ p4))))) ∨ ((((p4 ∧ p3) → (p3 ∧ p2)) ∨ (p5 → p2)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164879764804802002137665328741 : (((p1 → (((p3 ∧ ((p5 → ((p5 → p2) ∨ (p4 ∧ p5))) ∨ False)) ∨ p3) → p4)) ∨ True) ∨ ((((False ∧ False) ∧ False) ∨ (p5 → p2)) ∨ True)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55884655236431686024890578993 : (((p1 ∨ ((p4 → False) ∨ p5)) ∧ (p3 ∨ ((p3 ∧ (p5 ∨ (True ∨ (p4 ∨ ((((False ∨ True) ∧ p3) → False) ∨ (p4 ∨ p4)))))) → p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_237934404448609437114471958774 : ((True ∨ False) ∧ ((((((((p5 ∨ True) ∧ (p5 ∧ p1)) ∨ p5) ∨ p3) ∧ (True ∧ p2)) ∧ p5) ∧ ((p4 ∧ (p5 ∨ (p4 ∨ p1))) ∧ False)) ∨ True)) := by
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
theorem thm_5_vars_341740148728197160313838730736 : (p2 → (((p1 ∨ p2) → (((p1 → (((p2 ∨ p1) ∨ p1) ∨ (p2 ∨ ((True → False) ∨ p4)))) ∧ (p1 ∧ (p1 ∧ p5))) ∨ p1)) ∨ (p5 ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51208438116716738670059263016 : ((((p5 ∧ (((p1 ∨ p5) ∧ (p1 ∧ p4)) → p5)) ∧ ((p4 ∧ (p4 ∨ (p1 → False))) → p5)) ∨ (p1 → (True ∧ ((False ∧ p5) → p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179780590309790038965808001577 : ((((p4 → (False ∧ (p5 ∧ p4))) → (True → ((True → True) → p5))) ∧ p2) → ((p5 ∧ p5) → (p5 ∨ (((p4 ∨ (p5 ∨ p5)) ∨ p2) ∧ False)))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156956827058309043799796674833 : (((((p3 ∧ (((False ∧ (p2 ∨ False)) → (p1 ∨ p2)) ∧ p1)) → False) ∨ (p2 → (True ∨ p3))) ∨ p3) ∨ (((p3 → p5) ∧ (p2 ∨ p1)) → p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301194033860410431633763675216 : (False ∨ ((p3 ∨ (p5 ∧ ((False ∧ False) ∨ (p2 ∧ p2)))) → ((((p3 ∧ p2) ∧ (False ∨ (False ∨ (p5 ∨ (p3 → p4))))) ∨ True) ∨ (p2 ∧ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- False on the left can always be used.
      apply False.elim h7
    case inr h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218335054310449678618846816162 : (((False → p5) ∨ (p2 ∨ p3)) → (p5 → (p5 ∧ (p2 ∨ ((p2 ∨ p4) ∨ ((p5 ∨ ((p4 → p4) ∨ False)) → (p3 → (False ∨ (p3 ∨ False))))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h6 =>
      -- One of the premise coincides with the conclusion.
      exact h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- Implications on the right can always be decomposed.
    intro h9
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h9
    case inr h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h9
      case inr h13 =>
        -- False on the left can always be used.
        apply False.elim h13
  case inr h14 =>
    -- Disjunctions on the left can always be decomposed.
    cases h14
    case inl h15 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h15
    case inr h16 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h17
      -- Implications on the right can always be decomposed.
      intro h18
      -- Disjunctions on the left can always be decomposed.
      cases h17
      case inl h19 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h18
      case inr h20 =>
        -- Disjunctions on the left can always be decomposed.
        cases h20
        case inl h21 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h18
        case inr h22 =>
          -- False on the left can always be used.
          apply False.elim h22



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_86038184636585338474520323712 : ((((p5 → p4) → ((p3 ∧ (False ∨ (p5 ∨ p3))) ∧ False)) ∧ (p3 ∧ ((p3 → (p5 ∧ ((p1 ∨ (False ∨ False)) ∧ False))) → (p4 ∧ False)))) → p3) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_71089916005009287727011495570 : (((((p3 ∨ True) ∨ (False ∨ (p1 → p1))) → (((False → (p2 ∧ p2)) ∧ ((p5 ∨ (((p1 ∧ p1) ∨ p4) ∧ False)) → True)) ∧ p3)) ∧ p4) → p3) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : ((p3 ∨ True) ∨ (False ∨ (p1 → p1))) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315000443883554702018990703617 : (p3 ∨ ((False → (p5 → (p4 ∧ (p3 ∧ (p3 ∨ p1))))) ∧ (p1 ∨ (((((p4 → False) → p5) → False) → ((p4 → False) ∨ True)) ∨ (p2 ∧ p3))))) := by
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
  -- False on the left can always be used.
  apply False.elim h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_17184883874116620575874487058 : ((((p1 → ((p4 ∧ True) ∧ ((((p5 → ((p5 → False) ∨ (True ∨ p5))) → p3) ∧ False) ∧ p2))) → (p5 → p1)) → ((p3 ∨ p3) → p3)) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148702951405187226452350632538 : (((((True ∨ (p3 ∨ (False ∨ p1))) → False) ∨ True) → (((True → False) → ((False ∨ False) ∨ p5)) ∨ (p4 ∧ False))) ∨ ((False ∨ (False → p3)) ∧ p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h3 : (True ∨ (p3 ∨ (False ∨ p1))) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h4 := h2 h3
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h6
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h7 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h8 := h6 h7
    -- False on the left can always be used.
    apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204387695630357656064803194963 : (((True → ((p4 ∨ p2) → p4)) ∧ False) ∨ (((p4 ∧ ((p2 ∧ ((p3 ∧ p3) ∨ ((False ∨ p2) → p3))) ∨ p2)) ∨ p1) → ((p1 ∨ p4) ∨ True))) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Conjunctions on the left can always be decomposed.
        let h9 := h8.left
        let h10 := h8.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h13 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



