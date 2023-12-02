variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340795593568832083661760753280 : (p2 → ((((p5 → p4) → (((p3 ∨ (p1 ∨ p5)) ∧ False) ∨ (((p4 → ((False ∨ ((False ∧ p3) ∧ p1)) ∨ True)) ∨ p1) ∨ p1))) → p3) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116419487016534030093776090152 : (((p3 ∨ (p3 ∨ False)) → ((p1 → ((False ∨ p4) ∨ (p4 → ((p1 ∧ p5) ∨ (p4 → p4))))) ∨ (p3 ∧ (p3 ∧ (p2 → p4))))) ∨ (p5 ∧ p2)) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h5
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
      -- Implications on the right can always be decomposed.
      intro h9
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- One of the premise coincides with the conclusion.
      exact h10
    case inr h11 =>
      -- False on the left can always be used.
      apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323685314467968370292679656135 : (p5 ∨ ((p1 ∨ ((p4 ∨ ((p3 ∨ (False ∨ (p1 ∧ (p2 → p3)))) ∨ p4)) → ((p3 ∧ p4) ∧ (p3 ∨ p5)))) ∨ ((p4 → (False ∧ p2)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328700334390729047781538768017 : (True → ((((((p4 → p4) → False) ∧ (p3 → p4)) ∨ p3) ∧ (p2 ∧ False)) ∨ ((True → False) → ((((p1 → False) ∧ (p1 ∨ p3)) ∨ p1) ∨ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340700613404039087548850271533 : (p2 → (((((((((p4 ∧ p2) → p4) ∧ (p1 ∨ p4)) ∨ (p3 → (((p3 → p2) ∨ p3) ∧ p2))) ∨ True) ∧ p1) ∨ (p1 → p4)) ∧ p3) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345437161090936887613666925897 : (p3 → ((((p4 ∨ p1) ∨ (p3 → (((False ∧ (((p1 ∧ (False ∧ p4)) ∧ (False ∨ (p4 ∨ False))) → False)) → p3) → p4))) ∧ (p2 → p3)) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_261577790566811481154014896340 : ((p5 → p4) → ((True ∨ (p4 → (False ∧ ((p5 → (p1 ∨ (p4 ∧ (p5 → (False ∨ True))))) → True)))) → (p2 → ((p1 → p5) ∨ (True ∨ p3))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134387199443005593562993662812 : (((p5 ∨ ((((True ∨ p2) ∧ ((False → ((p1 ∨ (((p5 ∨ p3) ∧ p2) → p5)) ∨ True)) → p3)) ∨ p5) → p1)) ∨ True) ∨ (False ∨ (True ∨ True))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_738691213401865882943756146546 : ((((p2 ∧ p1) ∨ (p4 ∨ ((p3 → ((((False → p4) ∧ False) ∧ (((p3 → False) ∧ p5) ∨ p2)) ∨ True)) ∨ (p1 ∧ (True ∨ (p2 ∨ p5)))))) ∨ p1) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_750375619058578700286310919764 : (((True ∧ ((False → ((True → ((p2 → p3) → ((False ∨ True) → (p5 ∨ ((p5 ∨ p3) → p1))))) ∧ ((p3 → False) ∨ False))) → (p3 → p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_618908846506692474266219761145 : (((((p3 → (p4 ∧ p3)) ∧ (((False → p3) ∧ p4) ∨ (((True → (False ∧ (((p4 → p2) ∧ p2) → (p3 ∨ p5)))) ∧ p2) ∨ p1))) ∨ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185917305739960457321652058061 : (((((p4 ∨ (p2 ∧ True)) → False) → (p2 → (True ∨ p2))) ∧ True) → (((True → (p4 ∨ p5)) ∨ True) ∨ ((((p1 → p5) → p2) ∧ p5) ∧ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321716854879486808388253544218 : (p4 ∨ (p5 → (((((p1 → ((p5 → p2) ∨ ((True ∧ (p5 ∨ (True ∨ p4))) → p5))) → (p2 → p4)) ∧ ((p5 ∨ p1) → p4)) ∨ True) ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232849171579973017423979835014 : ((p2 ∧ (False → True)) → ((p3 ∨ True) ∧ ((((p3 ∧ True) ∨ (True ∨ True)) ∧ (False ∨ (p4 ∨ ((p4 ∨ ((p4 ∧ True) ∧ p4)) ∧ p2)))) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164798760426896368207716763429 : ((((p1 ∨ (p3 ∨ False)) ∧ ((True → False) ∧ (((p1 ∨ (p2 → p3)) ∧ p3) → True))) ∨ p2) ∨ (p2 → (((False ∧ (p5 → p3)) ∧ p2) ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215106911727985216218782096339 : (((p2 → True) → (p3 ∧ p1)) ∨ (p5 ∨ (((True ∧ p4) ∧ p1) ∨ (p3 ∨ ((((p1 → p1) ∧ p4) ∨ (p1 ∨ False)) → (True ∧ (p3 → p3))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h8 =>
      -- False on the left can always be used.
      apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_352847528346548510014903872237 : (p4 → ((p4 → False) → (p5 ∨ ((p2 ∨ (p2 ∨ (((((p3 → True) → (False ∨ p2)) ∧ ((False ∨ False) ∧ p4)) ∧ p3) ∨ p5))) ∨ (p1 → p3))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : p4 := by
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249556452953152284215416580851 : ((p5 ∨ p2) ∨ ((p1 → (((False ∨ (p3 ∨ (p3 ∨ p3))) ∨ True) ∧ p1)) ∧ (False ∨ (p4 ∨ (p4 ∨ (p2 ∨ (False → ((False ∧ p2) → p4)))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h1
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_69738405117526206231494127883 : ((((((False ∧ ((((((p3 → p5) ∧ p4) → (p2 ∨ p2)) ∨ (True → (p2 → p4))) → (p4 → False)) ∧ p1)) ∨ True) → p1) ∨ False) ∧ p5) → p1) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h5 : ((False ∧ ((((((p3 → p5) ∧ p4) → (p2 ∨ p2)) ∨ (True → (p2 → p4))) → (p4 → False)) ∧ p1)) ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h6 := h4 h5
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- False on the left can always be used.
    apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180440156551722690702144910204 : (((((p4 → p3) ∧ (True ∧ p3)) ∧ ((p1 ∧ p3) → p5)) → (p5 ∨ True)) → ((((p1 ∧ (((p2 ∨ False) ∨ p3) ∧ True)) ∧ p5) ∨ True) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_353413873574705454584357923030 : (p4 → (p1 ∨ ((p4 ∧ ((((True ∧ (((False ∧ (p2 ∨ (p3 → (False → p4)))) ∧ p3) ∨ p2)) ∧ p1) ∧ (p4 → (True ∧ p2))) ∨ p2)) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68384084113831114810170021403 : ((p3 → ((((p2 ∨ p2) ∨ True) → p5) → ((p2 → (p5 ∧ False)) → (((((False → True) ∧ p1) ∧ (p2 ∧ p4)) ∧ (False ∨ p5)) ∧ False)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_703261924045867302809310787148 : ((((p3 ∧ (((p3 ∧ (False ∧ (p2 ∨ True))) ∨ True) ∧ p3)) ∨ ((p3 ∧ (((p4 → p1) ∨ True) ∨ (p5 ∧ (p1 ∨ False)))) ∨ (p4 → p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_697834566049882094242455237730 : (((((((p4 → ((p2 → False) ∨ (p1 → p3))) ∧ False) ∧ p4) ∧ False) ∨ ((p1 ∨ ((p2 → (True ∧ ((p2 ∨ p1) → False))) → p2)) → p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166451021382616380181561706575 : ((p2 ∨ (((False ∨ True) ∨ ((True ∧ ((True ∧ True) ∨ False)) → p2)) ∧ ((p3 ∧ p1) ∧ p5))) ∨ (p2 ∨ (p4 ∨ ((True ∨ False) ∨ (True → False))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53458012324435298478759381829 : ((((False ∧ p5) ∨ (p3 → ((p5 ∨ p4) ∨ (True ∧ (p3 → False))))) → ((((p2 ∧ True) ∨ p5) → ((False ∧ False) ∨ False)) → (p2 → False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245196307739833225900551762012 : ((p2 ∧ False) ∨ ((p3 ∨ p2) → (p4 → ((False → (True → p1)) → (p5 ∨ (((p4 ∨ (p4 ∧ p3)) ∧ (p2 ∧ p2)) ∨ ((p5 ∨ False) → p5))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h7 =>
      -- False on the left can always be used.
      apply False.elim h7
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h8
    -- One of the premise coincides with the conclusion.
    exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_175333658638232135063289408386 : ((p4 ∨ (p5 ∨ ((p1 ∨ False) → (True ∨ ((((p4 ∧ True) ∧ p5) ∨ p4) → True))))) → (p4 → (p4 → ((p1 ∨ True) ∧ ((p5 ∨ p2) ∨ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
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
theorem thm_5_vars_76585060977727179638563050228 : ((((((p1 → (p2 ∨ ((False → p4) ∧ ((True ∨ ((True ∨ True) ∧ p3)) ∧ p5)))) ∧ p5) → p3) ∨ (True ∨ ((p2 ∨ True) ∧ p1))) → False) → False) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((((p1 → (p2 ∨ ((False → p4) ∧ ((True ∨ ((True ∨ True) ∧ p3)) ∧ p5)))) ∧ p5) → p3) ∨ (True ∨ ((p2 ∨ True) ∧ p1))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_722465007303670007213591338479 : (((((False ∨ p3) ∧ False) ∧ (((True ∨ ((p4 → (p5 ∨ p5)) ∧ (False ∧ ((p3 ∧ ((p3 → p2) → p5)) → p4)))) → (p5 → False)) ∧ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_694140077320793777448176732106 : (((((p5 ∧ (((p3 → p4) ∧ p2) ∧ p5)) ∧ (p3 ∨ (p2 ∨ (p3 ∨ p5)))) ∨ ((((p2 → p2) ∨ (True ∨ p4)) → (p4 ∨ p2)) ∨ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346633482810733878931203556780 : (p3 → ((p3 ∧ ((p1 ∧ ((((p1 ∧ ((p3 ∨ p2) ∨ False)) ∧ p1) ∨ ((p2 → False) ∨ p2)) ∧ False)) ∨ (p2 ∨ p5))) ∨ ((p2 ∧ p1) ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147271608376839995835069644240 : ((((((False ∨ p2) → (((True → p2) → (p1 ∨ p1)) ∧ (True ∨ p1))) ∨ ((p1 → p1) ∧ p5)) ∨ True) ∨ False) ∨ (p3 ∧ ((p3 ∨ p2) ∨ p4))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66191628019941059624917044039 : ((p5 ∨ ((((p1 → p5) ∨ p4) ∧ ((True ∧ p5) ∧ (p3 ∧ ((p4 ∧ True) ∧ (p2 → p5))))) ∧ (((p2 ∧ p2) ∨ (p5 ∨ p5)) ∨ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_603725330825661524254480720441 : ((((p4 ∨ ((p2 ∧ ((((p2 ∧ p3) → (p2 ∧ ((p4 ∨ p1) ∨ p4))) ∨ (p1 ∨ ((p2 ∨ p3) ∧ p2))) ∧ p5)) ∨ (p2 → p2))) ∧ True) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_345452384830148471310566023043 : (p3 → (((((p2 ∨ p1) ∧ (p1 ∨ ((((p4 → p3) → True) → (False ∧ ((p1 → (p2 ∧ p5)) ∨ p4))) → True))) ∧ p2) → (p5 ∧ True)) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46545717032589014674272831251 : ((((p5 → False) ∨ (((p1 ∧ (True ∨ (True ∨ (p4 ∨ p2)))) ∨ p5) ∨ ((p4 ∧ ((p3 ∧ p2) ∨ (p3 → p2))) ∨ p5))) ∧ (p1 ∨ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_14516221209454321196307297172 : ((((((p5 ∨ (((p5 ∨ False) ∨ ((p5 → (p2 ∧ p3)) → ((p2 ∧ p1) ∨ p2))) ∧ (p2 ∨ False))) ∧ p2) ∧ p3) ∨ p4) ∨ (p1 ∨ True)) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244564417771881688196026494897 : ((False ∧ p4) ∨ (((p4 ∧ ((((((p2 → ((p3 → True) ∨ p1)) ∨ p4) ∨ (True → p5)) ∧ (False → False)) → p2) ∨ True)) ∧ p4) ∨ (False ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_349397830929667887835534531036 : (p3 → (p4 → ((False ∧ (((p5 ∨ ((False → (p4 → False)) ∨ (p3 → ((p5 → p3) → p5)))) → (((p5 ∨ False) → p5) → True)) → p1)) ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137094631738880215317351748330 : ((True ∧ (((((((p3 ∧ True) ∨ ((False ∨ (p2 ∨ (True ∧ (False ∧ False)))) ∧ False)) → True) ∧ p5) → False) → True) → p4)) ∨ (False → (p3 ∧ p1))) := by
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
theorem thm_5_vars_56867060009495284464143129594 : (((p1 ∧ (p2 ∧ p5)) ∧ (((False ∧ ((False ∧ p5) ∨ (p3 ∨ p4))) ∨ True) ∧ ((p4 ∧ ((p3 ∨ p1) ∧ True)) → ((p4 → p5) ∨ p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149717762173345959250495992875 : ((p5 ∧ (p4 → (p3 ∨ ((p3 ∨ (p5 ∧ (((p3 → p4) → p3) ∨ (p2 → (True ∧ (True ∧ p1)))))) → p1)))) ∨ (p4 → ((p5 → p4) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_664755603051399993365932829584 : ((((p1 → ((p3 → ((((((False → p5) ∧ p3) → ((p4 ∨ p2) ∨ True)) ∨ (p2 ∧ p3)) ∨ p2) ∧ (p3 ∧ p5))) ∧ p4)) → (p3 ∨ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64782590068098025193678358145 : ((p2 ∨ ((((((((False → (p5 ∨ p2)) ∧ ((p3 ∧ (p2 ∨ p1)) ∨ True)) ∧ False) ∨ (False ∨ p5)) ∧ p4) ∨ p2) ∨ (False → False)) ∨ p1)) ∨ p2) := by
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
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168684303810730627733373642976 : ((p5 ∧ ((p2 ∧ p3) ∨ ((True ∧ (((p1 → p2) → p1) ∨ (p3 → p4))) ∧ (True ∨ p5)))) → (p4 → (((p4 ∨ (p1 → p3)) ∨ p1) → p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h1.left
      let h7 := h1.right
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Conjunctions on the left can always be decomposed.
        let h9 := h8.left
        let h10 := h8.right
        -- One of the premise coincides with the conclusion.
        exact h2
      case inr h11 =>
        -- Conjunctions on the left can always be decomposed.
        let h12 := h11.left
        let h13 := h11.right
        -- Conjunctions on the left can always be decomposed.
        let h14 := h12.left
        let h15 := h12.right
        -- Disjunctions on the left can always be decomposed.
        cases h15
        case inl h16 =>
          -- Disjunctions on the left can always be decomposed.
          cases h13
          case inl h17 =>
            -- One of the premise coincides with the conclusion.
            exact h2
          case inr h18 =>
            -- One of the premise coincides with the conclusion.
            exact h2
        case inr h19 =>
          -- Disjunctions on the left can always be decomposed.
          cases h13
          case inl h20 =>
            -- One of the premise coincides with the conclusion.
            exact h2
          case inr h21 =>
            -- One of the premise coincides with the conclusion.
            exact h2
    case inr h22 =>
      -- Conjunctions on the left can always be decomposed.
      let h23 := h1.left
      let h24 := h1.right
      -- Disjunctions on the left can always be decomposed.
      cases h24
      case inl h25 =>
        -- Conjunctions on the left can always be decomposed.
        let h26 := h25.left
        let h27 := h25.right
        -- One of the premise coincides with the conclusion.
        exact h2
      case inr h28 =>
        -- Conjunctions on the left can always be decomposed.
        let h29 := h28.left
        let h30 := h28.right
        -- Conjunctions on the left can always be decomposed.
        let h31 := h29.left
        let h32 := h29.right
        -- Disjunctions on the left can always be decomposed.
        cases h32
        case inl h33 =>
          -- Disjunctions on the left can always be decomposed.
          cases h30
          case inl h34 =>
            -- One of the premise coincides with the conclusion.
            exact h2
          case inr h35 =>
            -- One of the premise coincides with the conclusion.
            exact h2
        case inr h36 =>
          -- Disjunctions on the left can always be decomposed.
          cases h30
          case inl h37 =>
            -- One of the premise coincides with the conclusion.
            exact h2
          case inr h38 =>
            -- One of the premise coincides with the conclusion.
            exact h2
  case inr h39 =>
    -- Conjunctions on the left can always be decomposed.
    let h40 := h1.left
    let h41 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h41
    case inl h42 =>
      -- Conjunctions on the left can always be decomposed.
      let h43 := h42.left
      let h44 := h42.right
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h45 =>
      -- Conjunctions on the left can always be decomposed.
      let h46 := h45.left
      let h47 := h45.right
      -- Conjunctions on the left can always be decomposed.
      let h48 := h46.left
      let h49 := h46.right
      -- Disjunctions on the left can always be decomposed.
      cases h49
      case inl h50 =>
        -- Disjunctions on the left can always be decomposed.
        cases h47
        case inl h51 =>
          -- One of the premise coincides with the conclusion.
          exact h2
        case inr h52 =>
          -- One of the premise coincides with the conclusion.
          exact h2
      case inr h53 =>
        -- Disjunctions on the left can always be decomposed.
        cases h47
        case inl h54 =>
          -- One of the premise coincides with the conclusion.
          exact h2
        case inr h55 =>
          -- One of the premise coincides with the conclusion.
          exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66473667667774784566265784737 : ((True → (((p2 ∧ ((((p2 ∨ (p2 ∨ p4)) → (False ∨ p4)) → p1) ∧ (p2 ∧ ((False → True) ∨ (p1 → (p1 → False)))))) ∧ p1) ∨ True)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47328674787724391065177364767 : ((((p3 → (p1 ∧ p4)) → ((p3 ∨ (False ∨ (p5 ∧ (((p2 ∧ (p5 ∧ p1)) ∨ p4) ∧ (True ∨ True))))) ∨ (p3 ∨ False))) ∨ (p3 → p3)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_786132464133725133560391121628 : (((p4 ∨ ((p3 → (((False ∨ (True ∨ ((True → p5) ∧ ((True → (True → p5)) ∧ p5)))) ∧ (p1 ∧ p4)) → False)) ∧ (p5 ∨ (False ∨ p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258367554521557564579924340880 : ((p5 ∨ False) → (((True ∨ (p1 ∨ p5)) → False) → (False ∧ (False ∧ ((p5 ∧ (p4 → (((p3 ∨ (p3 → (p2 → True))) → p2) ∨ p3))) ∨ p1))))) := by
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
    have h4 : (True ∨ (p1 ∨ p5)) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h5 := h2 h4
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- False on the left can always be used.
    apply False.elim h6
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h7 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h8 : (True ∨ (p1 ∨ p5)) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h9 := h2 h8
    -- False on the left can always be used.
    apply False.elim h9
  case inr h10 =>
    -- False on the left can always be used.
    apply False.elim h10
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h11 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h12 : (True ∨ (p1 ∨ p5)) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h13 := h2 h12
    -- False on the left can always be used.
    apply False.elim h13
  case inr h14 =>
    -- False on the left can always be used.
    apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_326005181250387813483279985651 : (p5 ∨ (True → (((p5 → (True ∧ True)) ∨ p4) → (((p4 ∧ ((False ∧ True) ∨ (((p1 ∨ (True → p4)) ∧ p1) ∨ (p3 ∨ p3)))) ∨ p2) ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60978359400924131107070480379 : ((False ∧ ((p2 ∨ (((p4 → p3) ∨ p2) ∧ (p3 ∧ ((p2 ∧ ((p3 ∨ p5) → ((p1 → p5) → p4))) ∨ ((False ∨ p4) → p3))))) ∨ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_151398782359011757900385412434 : ((((((True → p4) ∧ p4) ∨ (False → (True → p4))) ∨ (p5 → ((p3 ∧ (True ∨ True)) ∧ p2))) ∧ (p5 ∨ p2)) → ((False ∧ p4) ∨ (p4 → True))) := by
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
      let h6 := h5.left
      let h7 := h5.right
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h9
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h11
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h12 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h13 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h14
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h15 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h16
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h17 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h18 =>
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136422760849430878453784241307 : ((((p2 ∨ (p5 → False)) ∨ p4) → ((p5 ∨ p2) ∨ (p3 ∨ (p3 ∧ (p2 → (((p1 ∧ True) → p5) → (p2 ∨ p1))))))) ∨ (p5 → (p1 → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160272378770836423818209287242 : (((p3 → ((True ∨ (((p4 ∨ p5) ∨ p5) → False)) → (p1 ∧ ((p5 → False) ∧ p2)))) ∨ (p2 ∨ False)) → ((True → p2) ∨ (False → (p4 → p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- False on the left can always be used.
    apply False.elim h3
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h7
      -- Implications on the right can always be decomposed.
      intro h8
      -- False on the left can always be used.
      apply False.elim h7
    case inr h9 =>
      -- False on the left can always be used.
      apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164147955194687181391579574900 : ((p3 ∨ (p4 → (p2 → ((((((p1 → p2) ∧ p5) → False) ∨ p3) ∨ False) ∨ (p1 → p1))))) ∧ (((p4 ∧ False) ∧ False) → (True ∨ (False ∧ True)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200284870143069748778804569932 : (((p3 → (p4 ∨ p3)) → ((False ∧ p1) ∧ p3)) → (((False ∧ p5) ∧ (True ∧ p4)) ∧ ((p3 ∨ (p3 → p3)) ∨ ((p2 ∧ (p1 ∨ True)) → p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p3 → (p4 ∨ p3)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- False on the left can always be used.
  apply False.elim h6
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h7 : (p3 → (p4 ∨ p3)) := by
    -- Implications on the right can always be decomposed.
    intro h8
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h8
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h9 := h1 h7
  -- We need to get the left conjuct of h9 based on <expert-advice>.
  let h10 := h9.left
  -- We need to get the left conjuct of h10 based on <expert-advice>.
  let h11 := h10.left
  -- False on the left can always be used.
  apply False.elim h11
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h12 : (p3 → (p4 ∨ p3)) := by
    -- Implications on the right can always be decomposed.
    intro h13
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h13
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h14 := h1 h12
  -- We need to get the left conjuct of h14 based on <expert-advice>.
  let h15 := h14.left
  -- We need to get the left conjuct of h15 based on <expert-advice>.
  let h16 := h15.left
  -- False on the left can always be used.
  apply False.elim h16
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h17
  -- One of the premise coincides with the conclusion.
  exact h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_740666258550310996941912004396 : ((((p2 ∨ p3) ∨ (((p3 ∧ True) ∨ (p2 ∧ ((p4 ∧ (((p5 ∧ p5) → p2) ∧ (((p2 ∧ (p4 ∧ p2)) → p5) → p3))) ∧ False))) ∧ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191245557471734843193670176411 : (((False ∧ p4) ∧ ((False ∨ p5) ∨ ((False → True) → p4))) ∨ (False → (((False → (p1 → (p3 ∧ ((True ∨ (False ∧ True)) ∧ p1)))) ∨ p2) ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56350400311787000272081146806 : ((((True ∧ (p2 ∨ p3)) ∨ p5) → (((p3 ∨ (((p1 → p2) → ((p3 ∧ p3) → (p5 ∨ (p2 ∧ (False ∨ p1))))) ∨ p1)) → False) ∨ True)) ∨ p5) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191670204551011231616485096067 : ((p5 ∧ (((p2 → p2) ∧ (p5 ∨ (p5 → p5))) → p5)) ∨ (p5 → (((False → p3) ∨ (((p4 ∧ False) ∧ ((True ∨ False) → True)) ∨ p3)) ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198629316319406255413931372700 : ((p3 ∨ ((False ∨ (p5 → (p2 → False))) ∧ False)) ∨ (((True ∧ ((p2 ∨ (True ∨ p4)) → p4)) ∧ p2) ∨ (p3 → (False → ((p3 → True) ∧ p1))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62379384080925815066778655733 : ((p3 ∧ ((((p1 → p2) → p2) ∧ (p5 ∧ ((p5 ∧ (p2 ∧ (False ∧ p5))) → p3))) ∨ (p2 → (True ∧ ((p5 ∨ (p5 ∧ p1)) ∨ p4))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_264020161373914414982956654645 : (True ∧ ((p3 ∧ (p3 → (p1 → (((p2 ∨ (p5 ∨ True)) ∧ p3) ∧ p2)))) → (((False → (p3 ∨ p5)) → p5) → ((p5 ∨ p5) ∧ (False → True))))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h5 : (False → (p3 ∨ p5)) := by
    -- Implications on the right can always be decomposed.
    intro h6
    -- False on the left can always be used.
    apply False.elim h6
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h7 := h2 h5
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h7
  -- Implications on the right can always be decomposed.
  intro h8
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_630481936961802783520283722892 : (((((False ∨ ((True → ((p1 → (p4 → False)) → (p2 ∨ p1))) ∨ (((p4 → p3) ∧ p1) ∧ ((True ∨ (p4 → p5)) ∨ True)))) ∨ True) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134166371061174193355492781480 : (((((p1 → p2) → ((((True ∧ True) ∨ (True ∨ True)) ∧ (True ∧ True)) ∧ p5)) ∧ (((p5 ∨ p1) ∧ p1) ∧ p4)) ∨ True) ∨ ((p5 ∨ p2) → p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115711154934642470812897234401 : ((((((False ∨ p1) → p2) ∨ p2) ∨ True) → ((((p1 ∨ (p2 ∧ ((p1 ∧ False) → True))) ∨ (p5 ∨ (p1 ∧ p2))) → p1) → p5)) ∨ (False ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341709568694603457675976491244 : (p2 → (((((p5 ∧ (p5 → (p5 ∧ p3))) → ((True → (p1 ∨ p1)) ∨ p4)) ∧ p5) ∨ (p3 → (p3 ∧ ((p3 ∧ p3) → p4)))) ∨ (p1 ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178956447911353039688155369490 : (((False ∨ False) ∨ ((((p2 ∧ p2) ∨ (p4 ∨ (p2 ∨ p1))) → p2) ∧ p5)) ∨ ((False ∧ True) → (((p5 ∧ (p3 ∨ p2)) ∧ p3) ∨ (True → p4)))) := by
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
theorem thm_5_vars_680661621046591528067175495981 : ((((((((False ∨ p5) ∨ True) → p3) ∧ True) → (p5 → (((False ∨ p3) ∨ False) → ((p5 ∨ p3) ∨ True)))) → ((p3 → p4) → (p3 ∨ True))) ∨ p2) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_740577238653307337013958733017 : ((((p2 ∨ False) ∨ (p5 ∧ (((p2 ∨ False) ∨ (((p4 ∨ (False ∧ (False → (True → ((p5 ∧ True) → p2))))) ∨ (p3 ∨ p2)) ∧ p3)) ∧ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52170494576741075425088806795 : ((((False ∨ ((p1 ∨ (True ∨ (p1 ∨ p4))) ∨ False)) → (False ∧ (p4 → (True → p4)))) → ((((p2 → p4) → p4) ∨ p2) ∨ (p1 → p2))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (False ∨ ((p1 ∨ (True ∨ (p1 ∨ p4))) ∨ False)) := by
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
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the left conjuct of h3 based on <expert-advice>.
  let h4 := h3.left
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192176101446926790745924910055 : (((((p4 → (False ∨ (p5 ∨ p1))) ∧ True) ∨ p2) ∧ p1) → (p4 → ((((p4 ∨ p2) → (p4 ∧ p4)) → (True ∧ (p5 → p2))) ∨ (False ∨ True)))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324611198762975838477880608338 : (p5 ∨ ((True ∨ (p2 ∨ p2)) ∧ ((((False ∨ (p2 → p2)) ∧ (p5 ∨ (False ∨ p1))) ∨ True) ∧ ((p5 ∧ p5) → (((p5 ∨ p2) ∨ p5) → True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_330382613269504798861444727255 : (True → (p2 ∨ (((p3 ∧ p5) ∨ (p5 → (p5 → p5))) ∧ ((p2 ∧ ((True ∨ p2) ∧ p1)) ∨ (p4 ∨ ((p1 ∨ p1) → ((True ∨ False) → p1))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h7 =>
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h8 =>
      -- One of the premise coincides with the conclusion.
      exact h8
  case inr h9 =>
    -- False on the left can always be used.
    apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111569793346026210804121012574 : (((((False ∧ (p3 ∧ p2)) ∨ (((((p2 ∨ p1) ∨ p3) ∧ p5) ∨ (((False → True) ∨ p5) ∧ (p3 → p3))) ∨ p5)) ∧ True) ∨ True) ∨ (p4 ∨ p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_175303414632401436922140380983 : ((p3 ∨ (p5 ∨ (((((((p5 ∧ p5) → p5) → p5) ∨ True) ∧ False) ∨ p4) ∨ p5))) → ((p3 ∨ (p2 ∨ True)) ∨ (p1 ∧ ((False → True) ∨ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
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
          -- Disjunctions on the left can always be decomposed.
          cases h8
          case inl h10 =>
            -- False on the left can always be used.
            apply False.elim h9
          case inr h11 =>
            -- False on the left can always be used.
            apply False.elim h9
        case inr h12 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h13 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40094588254511790043229078691 : (((((False ∨ (p2 ∧ ((((p4 → p5) ∨ ((((True ∧ True) → p3) ∨ ((True ∧ True) ∧ False)) → p4)) ∧ p3) ∨ p3))) → False) ∧ False) ∨ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_763449592424514225179556995710 : (((p3 ∧ (False ∧ (p4 ∨ (((False ∨ (False ∨ ((p2 ∨ False) ∨ ((((True ∨ p5) ∨ p3) ∨ (p1 ∧ (p4 ∨ True))) → False)))) → p5) ∧ p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41057007117624974584270259125 : (((((p3 ∨ p4) → ((False ∨ ((True ∨ True) → ((((p3 ∧ p2) ∧ p4) ∨ p5) ∧ p5))) → ((p5 → True) ∨ p4))) → (p3 ∨ p2)) ∨ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2028820831497748822035161863 : ((p4 → ((False ∨ True) ∨ ((((((False → (p5 ∨ (p4 → p1))) ∨ False) ∨ p4) → p5) ∧ p3) ∧ p1))) → (((p2 → p3) ∧ p2) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246495527226354510040969342307 : ((p5 ∧ p1) ∨ (((((False ∧ p1) ∨ (((p5 ∨ p3) ∨ ((p1 → p1) ∧ p3)) ∨ ((p2 ∧ (True → p5)) → True))) ∨ (p5 ∨ p4)) ∨ p2) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303901421087475928086225688182 : (p1 ∨ ((((((False ∧ ((p5 ∧ ((p2 → p3) → p4)) → p4)) ∨ True) → p1) ∧ p4) ∨ ((p4 ∧ (p5 ∧ True)) ∧ ((False ∧ p3) ∧ p2))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_128378036803435443807572027774 : ((p4 → (((p3 ∧ p5) ∧ (True ∨ (p5 ∨ p1))) ∧ (False ∧ ((p1 ∧ (True → ((p3 ∧ True) ∧ (p2 → True)))) ∨ (p5 → True))))) → (p3 → p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_654135039823383599482541533665 : (((((((p5 ∨ p1) ∧ (p2 ∧ ((p5 → ((p5 → ((p1 ∧ p4) ∧ p5)) → p3)) ∧ ((p1 ∨ p1) ∧ p4)))) ∧ p1) ∨ p2) ∨ (True ∨ p1)) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_353937798220368649908503191179 : (p4 → (p2 → (p4 ∧ ((p3 → ((False → p5) → ((p2 ∧ False) ∨ (p1 ∨ ((p5 ∧ True) ∧ (True → (p2 → (p4 ∨ p3)))))))) ∨ (p3 ∨ p2))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60064382474766894881683226998 : (((p2 ∨ p2) → ((p3 → (((p4 ∨ (((p1 → ((p2 ∨ True) ∨ False)) ∧ (True ∨ True)) ∨ (p5 → (p2 → p3)))) → p1) ∨ p1)) ∧ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_646081884409885525456609917407 : ((((True → (p1 ∨ (False → ((p2 ∨ ((((((((True ∨ (True → p5)) ∨ p1) ∨ False) ∧ p2) ∧ p4) → p1) ∨ True) ∧ p5)) ∨ p3)))) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299362592317103326982942001555 : (False ∨ (((True → p1) ∧ ((((p3 → ((((True ∨ p3) ∨ False) ∨ p5) ∧ True)) → p5) ∧ (p5 ∧ ((p4 → p3) ∨ p5))) ∧ (p3 ∨ True))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50237336123208036981386326416 : (((((((p1 ∨ (((p2 → (p1 ∨ False)) → (p2 → p3)) → (p5 ∨ p3))) ∧ p1) ∨ True) → False) → p1) ∨ ((p3 ∧ (p1 ∨ p2)) ∧ p3)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p1 ∨ (((p2 → (p1 ∨ False)) → (p2 → p3)) → (p5 ∨ p3))) ∧ p1) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259331466263299587753022607089 : ((False → p2) → (((p3 ∧ ((p1 → p1) ∨ (p2 ∨ (((False ∨ False) ∧ p3) ∧ True)))) → False) ∨ ((p3 ∨ (False ∨ p3)) ∨ (p1 → (p1 ∨ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_590050939983052861356805876198 : ((((((p4 ∨ (((p4 → p4) → (((p2 ∨ True) ∧ p1) ∨ p2)) ∨ p5)) ∧ (((p2 → ((p5 ∨ p1) ∧ p4)) ∧ p2) ∧ p5)) → p4) ∧ True) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h3.left
      let h12 := h3.right
      -- Conjunctions on the left can always be decomposed.
      let h13 := h11.left
      let h14 := h11.right
      -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
      have h15 : p2 := by
        -- One of the premise coincides with the conclusion.
        exact h14
      -- We have shown the premise of h13, we can now drive its conclusion.
      let h16 := h13 h15
      -- We need to get the right conjuct of h16 based on <expert-advice>.
      let h17 := h16.right
      -- One of the premise coincides with the conclusion.
      exact h17
    case inr h18 =>
      -- Conjunctions on the left can always be decomposed.
      let h19 := h3.left
      let h20 := h3.right
      -- Conjunctions on the left can always be decomposed.
      let h21 := h19.left
      let h22 := h19.right
      -- We want to use the implication h21 based on <expert-advice>. So we show its premise.
      have h23 : p2 := by
        -- One of the premise coincides with the conclusion.
        exact h22
      -- We have shown the premise of h21, we can now drive its conclusion.
      let h24 := h21 h23
      -- We need to get the right conjuct of h24 based on <expert-advice>.
      let h25 := h24.right
      -- One of the premise coincides with the conclusion.
      exact h25
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313934826751818366186439939136 : (p3 ∨ (((((((p3 → (False ∧ False)) → p1) ∧ p5) ∧ (p1 ∧ p2)) ∧ ((((True ∨ p4) → False) ∨ (p1 ∨ p1)) ∧ p5)) ∨ False) ∨ (True ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_685438869796397367105054706498 : ((((((((p3 ∧ p2) → (((False ∧ (p1 → p4)) ∧ p3) ∧ False)) ∨ False) ∧ (p1 ∨ p3)) ∧ True) → ((p5 ∨ (False ∨ p5)) ∨ (False → True))) ∨ p5) ∧ True) := by
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
  let h4 := h2.left
  let h5 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h11 =>
    -- False on the left can always be used.
    apply False.elim h11
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59487760202011692804565829033 : (((p1 → p4) ∨ ((p4 → (p2 → ((p1 ∨ p3) ∨ True))) ∧ ((True → (p4 ∧ p3)) → (p2 → ((p1 ∨ (p4 ∨ False)) ∧ (p3 ∨ p1)))))) ∨ p5) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h5 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h5
  -- We need to get the left conjuct of h6 based on <expert-advice>.
  let h7 := h6.left
  -- One of the premise coincides with the conclusion.
  exact h7
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h8 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h9 := h3 h8
  -- We need to get the right conjuct of h9 based on <expert-advice>.
  let h10 := h9.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137450443669813582110349410963 : ((p4 ∧ ((False → (p5 ∨ (p5 ∧ p1))) → ((((p5 ∧ True) ∧ p1) ∧ False) ∧ ((True ∧ p2) ∨ (True ∨ (p2 → p2)))))) ∨ (False ∨ (True ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_247555529966024364281816607513 : ((False ∨ p4) ∨ ((p5 ∧ ((p3 ∧ p4) ∨ (p1 → p2))) ∨ ((True ∧ (((p5 ∨ (True → p1)) → p2) → False)) ∨ ((False ∧ (p5 ∧ p1)) → True)))) := by
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
theorem thm_5_vars_746499904955946759807479972395 : ((((p2 ∨ p4) → ((p3 ∨ ((p2 ∨ (p2 ∧ (True ∧ ((False ∧ False) ∨ p2)))) → (p3 ∨ ((((False ∨ p5) ∨ p3) ∨ True) ∨ p2)))) → p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43981017516443576543668734369 : (((((((((p1 ∨ ((p2 ∧ (p2 ∧ p2)) ∨ p2)) ∨ (p4 ∨ p5)) ∧ False) ∨ False) ∧ ((p2 ∧ p2) ∧ True)) ∧ True) → (p5 ∧ False)) → p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64155576715917799798034530552 : ((False ∨ ((False ∧ p2) ∧ (((((((p1 → p2) → p3) ∧ (p3 ∧ True)) → p1) → False) → ((p1 → ((p2 → p2) ∨ p2)) → p5)) → False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



