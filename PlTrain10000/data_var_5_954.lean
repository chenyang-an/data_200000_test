variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190908697066534033864175891828 : (((p1 → ((p1 ∨ p5) ∨ (p1 ∧ p3))) → (p5 → p3)) ∨ (p2 → (p3 → (((p1 ∨ ((True → (p2 ∧ p1)) → False)) ∨ p2) ∨ (p2 ∨ p2))))) := by
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
theorem thm_5_vars_63444794727646156014010568496 : ((p5 ∧ (p4 → (((((p3 ∨ p3) ∧ False) ∧ p4) ∨ (True → (p3 → ((p5 ∧ (p3 → ((True ∨ False) → (p5 ∨ False)))) ∨ False)))) ∧ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54266170249758972613659728352 : ((((p3 → ((False ∨ p4) → True)) → (p2 → False)) ∧ ((False → ((p2 → (p3 ∧ (p4 ∨ p5))) ∨ p4)) ∧ (((p4 ∨ p2) ∧ True) ∨ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43213707483376185503797160482 : ((((p3 ∧ (p3 ∨ (((p2 ∧ (p5 ∨ (p5 → ((p1 ∧ p4) → False)))) ∨ ((p1 → p2) ∨ p3)) ∧ ((p2 → True) ∧ p3)))) ∧ p3) → p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303811160405930433233684390131 : (p1 ∨ ((((p4 → p3) → (False ∧ ((p3 ∨ (True → p1)) ∧ ((p2 → (p5 ∧ ((False → False) → ((p1 ∨ p3) ∨ p3)))) ∨ p1)))) → p4) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_627046779483184323732835226 : ((((((p5 ∨ p2) → (p2 ∧ ((p2 ∧ p5) → (p3 ∧ (p2 ∨ ((p1 ∧ (p2 ∧ p2)) ∧ p1)))))) → p2) ∧ p4) → (False ∧ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_737743235529702343456892667892 : ((((p5 → p5) ∧ (p5 ∧ (((True ∧ p3) ∨ (((False → (False ∧ (p2 ∧ p3))) ∧ p5) ∨ ((p3 ∨ p1) ∧ ((True → True) → p1)))) ∨ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_124442617845953845506902807413 : (((((False ∨ False) → p3) ∨ (p1 → (False → p4))) → ((((p2 ∨ (p5 ∧ (((p5 → False) ∧ True) → p5))) ∧ p4) → False) ∧ False)) → (p3 → p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : (((False ∨ False) → p3) ∨ (p1 → (False → p4))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- False on the left can always be used.
    apply False.elim h5
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h3
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_698295400090844328851785394324 : (((((((p3 ∧ p5) ∨ p2) ∧ ((p1 ∧ p4) ∧ True)) ∧ (True ∨ p2)) ∨ (((p1 ∨ False) ∨ p5) → (p3 ∨ (((p4 ∨ p1) → p1) → True)))) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- False on the left can always be used.
      apply False.elim h5
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157667018052157198457937506361 : (((((p1 ∨ False) ∨ ((True ∨ p3) ∧ (p1 ∨ p3))) ∨ ((False ∨ p2) ∨ True)) ∨ (p3 ∧ (p3 → p1))) ∨ (p5 → ((p5 → False) → (p5 → p2)))) := by
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
theorem thm_5_vars_620137894744352408354955666642 : (((((p1 ∧ False) ∨ (p3 → (p1 ∨ ((p1 ∨ p1) ∨ ((False ∨ p4) ∧ ((p1 → (((p3 ∧ (p5 → p4)) ∧ p3) ∧ False)) → p5)))))) ∨ True) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_207617323632190781749580221218 : ((((p4 ∧ (p4 ∧ p4)) → False) → p3) → ((p4 ∨ (p3 ∨ p3)) → ((((p2 → ((p4 → p3) → True)) → (True → False)) ∧ p4) → (p4 → p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h7 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h8 : (p2 → ((p4 → p3) → True)) := by
      -- Implications on the right can always be decomposed.
      intro h9
      -- Implications on the right can always be decomposed.
      intro h10
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h11 := h5 h8
    -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
    have h12 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h11, we can now drive its conclusion.
    let h13 := h11 h12
    -- False on the left can always be used.
    apply False.elim h13
  case inr h14 =>
    -- Disjunctions on the left can always be decomposed.
    cases h14
    case inl h15 =>
      -- One of the premise coincides with the conclusion.
      exact h15
    case inr h16 =>
      -- One of the premise coincides with the conclusion.
      exact h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_163434128463435119615068809007 : (((True → ((p1 → p5) ∧ p2)) → (p4 ∨ ((p4 ∨ (p1 ∧ p1)) ∨ (p1 ∨ (True ∨ False))))) ∧ (((p2 ∧ False) ∧ p2) ∨ ((p3 → p3) ∨ p4))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157348772332173476127143405943 : (((p5 ∨ ((p2 ∧ ((p4 ∨ (p5 ∧ (True → p3))) ∧ (False → (False ∨ p2)))) ∨ (p3 ∨ p3))) → p2) ∨ ((p5 → ((p3 → p1) ∨ p5)) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57743159576609523813654417653 : ((((True → True) → False) → (False ∧ (((p1 ∨ ((False → p2) → p4)) ∨ (p1 → ((p5 ∧ p5) ∨ p3))) → (p3 ∨ (p4 → (True ∧ p1)))))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (True → True) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- False on the left can always be used.
  apply False.elim h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h8 : (True → True) := by
        -- Implications on the right can always be decomposed.
        intro h9
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h10 := h1 h8
      -- False on the left can always be used.
      apply False.elim h10
    case inr h11 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h12 : (True → True) := by
        -- Implications on the right can always be decomposed.
        intro h13
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h14 := h1 h12
      -- False on the left can always be used.
      apply False.elim h14
  case inr h15 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h16 : (True → True) := by
      -- Implications on the right can always be decomposed.
      intro h17
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h18 := h1 h16
    -- False on the left can always be used.
    apply False.elim h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191687159197153834505916925813 : ((p5 ∧ (False ∨ (p1 ∧ ((True ∨ False) → (True → p3))))) ∨ ((False ∧ (((p1 ∧ False) → (True → (p1 ∧ p1))) ∧ p1)) ∨ ((p1 ∨ False) → p1))) := by
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
    -- False on the left can always be used.
    apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47128170691717851413123394466 : ((((((p2 → True) → (p3 → (False ∨ p4))) → ((p1 ∧ ((p3 ∧ p2) ∧ (p3 ∨ p3))) ∨ False)) → ((p3 ∧ p5) ∧ p3)) ∨ (p5 ∧ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180571475451532996942894838831 : (((((p4 → (p1 ∨ True)) → False) ∨ (p1 ∨ True)) → (p5 ∧ (False ∧ p4))) → (((p5 → True) ∧ p5) ∧ (((p1 ∨ (p4 ∧ p4)) ∧ True) ∧ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : (((p4 → (p1 ∨ True)) → False) ∨ (p1 ∨ True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- One of the premise coincides with the conclusion.
  exact h5
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h6 : (((p4 → (p1 ∨ True)) → False) ∨ (p1 ∨ True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h7 := h1 h6
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- We need to get the left conjuct of h8 based on <expert-advice>.
  let h9 := h8.left
  -- False on the left can always be used.
  apply False.elim h9
  -- True on the right can always be proven directly.
  apply True.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h10 : (((p4 → (p1 ∨ True)) → False) ∨ (p1 ∨ True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h11 := h1 h10
  -- We need to get the left conjuct of h11 based on <expert-advice>.
  let h12 := h11.left
  -- One of the premise coincides with the conclusion.
  exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45067171936284114750949685079 : ((((p5 → p1) ∨ ((False → True) ∨ (((((False → (p2 ∨ ((p1 ∨ True) ∨ p5))) ∨ p2) ∧ (p3 ∧ p4)) → (p2 ∧ True)) ∨ True))) → p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_699194543943486239298421923781 : ((((p2 → ((p3 ∧ p1) ∧ ((p2 → (p1 ∧ p3)) ∨ (p5 ∧ p5)))) ∨ ((p1 → (p4 ∨ (p5 → ((True ∧ (p3 ∧ p1)) ∧ p5)))) ∨ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_247979057132658100816485793550 : ((p1 ∨ p4) ∨ (((p5 ∨ (p1 ∧ False)) ∨ ((p5 → p3) ∨ p4)) ∨ (p4 → ((((False → ((True → p2) → p2)) → False) ∧ (p5 ∨ p4)) → p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  cases h4
  case inl h5 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h6 : (False → ((True → p2) → p2)) := by
      -- Implications on the right can always be decomposed.
      intro h7
      -- Implications on the right can always be decomposed.
      intro h8
      -- False on the left can always be used.
      apply False.elim h7
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h9 := h3 h6
    -- False on the left can always be used.
    apply False.elim h9
  case inr h10 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h11 : (False → ((True → p2) → p2)) := by
      -- Implications on the right can always be decomposed.
      intro h12
      -- Implications on the right can always be decomposed.
      intro h13
      -- False on the left can always be used.
      apply False.elim h12
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h14 := h3 h11
    -- False on the left can always be used.
    apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136020751159200790521527511761 : ((((p1 ∨ (True ∨ ((p3 ∨ (p2 → p5)) ∧ True))) → True) → ((p5 ∧ ((p2 ∧ (p1 ∨ p5)) → (True ∨ p5))) → p5)) ∨ (p4 → (False ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354720493004646822744930135308 : (p5 → (((p3 ∨ ((p2 ∧ (p5 ∨ p3)) ∨ (False ∧ (p5 → ((((p4 ∧ p5) ∨ True) ∧ (p3 ∨ False)) → p2))))) ∨ ((p4 ∨ p5) ∨ False)) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177469643837464868151073695590 : ((False → (True ∧ (p4 ∧ (((((p5 → p5) ∨ p1) ∨ p3) ∧ p1) ∨ False)))) ∧ (p1 ∨ ((p2 → p1) → (((p5 ∨ p3) → p3) ∨ (p2 ∨ True))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172612287237549625653836853649 : (((p2 → (p3 ∨ p5)) → ((True ∨ p4) → (p3 ∨ (p1 ∧ ((p3 ∨ p5) ∧ True))))) ∨ (p2 → ((((False → p2) ∧ p3) ∧ (p4 → False)) → p3))) := by
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
  let h5 := h3.left
  let h6 := h3.right
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152401995030033009261548908628 : ((((True ∧ False) → (True ∨ p5)) → ((p1 → ((((p1 ∧ (p5 ∨ (p5 ∧ p1))) → p2) ∨ p4) ∨ p3)) ∧ p1)) → (((p3 → p4) → p2) → p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : ((True ∧ False) → (True ∨ p5)) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- False on the left can always be used.
    apply False.elim h6
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h7 := h1 h3
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199499971794365203292249615410 : (((False → (p4 ∨ (False ∨ (False ∨ p5)))) ∨ p5) → (((p3 → (((((p4 ∨ (p5 ∨ p3)) ∧ True) ∨ p5) ∨ p2) → p3)) → False) ∨ (p4 ∨ True))) := by
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
theorem thm_5_vars_111185266915425013774246026681 : ((((p2 ∧ (True → (p1 → p2))) → ((((p2 ∧ (p2 ∨ ((False ∨ p5) ∧ p5))) ∧ (True ∧ p2)) → (p5 ∧ True)) → p5)) ∧ True) ∨ (p3 ∧ p3)) := by
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
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h5 : ((p2 ∧ (p2 ∨ ((False ∨ p5) ∧ p5))) ∧ (True ∧ p2)) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h3
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h5
  -- We need to get the left conjuct of h6 based on <expert-advice>.
  let h7 := h6.left
  -- One of the premise coincides with the conclusion.
  exact h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_871362054153442259163912936619 : ((((p2 ∨ (((((True ∧ (p4 ∧ (p4 → p2))) → False) → (p5 ∨ False)) ∨ ((False ∧ ((p1 → p5) ∨ p1)) ∧ p3)) ∨ (False → p5))) → False) → p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p2 ∨ (((((True ∧ (p4 ∧ (p4 → p2))) → False) → (p5 ∨ False)) ∨ ((False ∧ ((p1 → p5) ∨ p1)) ∧ p3)) ∨ (False → p5))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- False on the left can always be used.
  apply False.elim h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49712626996416361051825171575 : (((True ∧ ((p5 → (p4 ∨ (p1 ∨ (True → (p5 → (True → (((p5 ∧ p4) → p3) ∨ (False → p3)))))))) → True)) → ((p2 → True) → p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351645770234207410368971471891 : (p4 → ((False ∧ ((True → (True ∧ ((((p5 → True) → True) ∨ True) → p5))) ∨ (p3 ∨ True))) ∨ (False → ((((p2 → p4) ∨ p4) ∨ True) ∧ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152225164334167100939754134325 : (((p3 ∧ (p2 ∨ ((p3 ∧ p1) ∨ p1))) ∧ ((p3 ∨ (p4 ∨ p4)) → (((False ∧ (False → p1)) ∧ False) ∧ p3))) → ((p3 ∧ (p4 ∧ p2)) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- One of the premise coincides with the conclusion.
      exact h9
    case inr h11 =>
      -- One of the premise coincides with the conclusion.
      exact h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h12 := h1.left
  let h13 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h14 := h12.left
  let h15 := h12.right
  -- Disjunctions on the left can always be decomposed.
  cases h15
  case inl h16 =>
    -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
    have h17 : (p3 ∨ (p4 ∨ p4)) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h14
    -- We have shown the premise of h13, we can now drive its conclusion.
    let h18 := h13 h17
    -- We need to get the left conjuct of h18 based on <expert-advice>.
    let h19 := h18.left
    -- We need to get the right conjuct of h19 based on <expert-advice>.
    let h20 := h19.right
    -- False on the left can always be used.
    apply False.elim h20
  case inr h21 =>
    -- Disjunctions on the left can always be decomposed.
    cases h21
    case inl h22 =>
      -- Conjunctions on the left can always be decomposed.
      let h23 := h22.left
      let h24 := h22.right
      -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
      have h25 : (p3 ∨ (p4 ∨ p4)) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h23
      -- We have shown the premise of h13, we can now drive its conclusion.
      let h26 := h13 h25
      -- We need to get the left conjuct of h26 based on <expert-advice>.
      let h27 := h26.left
      -- We need to get the right conjuct of h27 based on <expert-advice>.
      let h28 := h27.right
      -- False on the left can always be used.
      apply False.elim h28
    case inr h29 =>
      -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
      have h30 : (p3 ∨ (p4 ∨ p4)) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h14
      -- We have shown the premise of h13, we can now drive its conclusion.
      let h31 := h13 h30
      -- We need to get the left conjuct of h31 based on <expert-advice>.
      let h32 := h31.left
      -- We need to get the right conjuct of h32 based on <expert-advice>.
      let h33 := h32.right
      -- False on the left can always be used.
      apply False.elim h33
  -- Conjunctions on the left can always be decomposed.
  let h34 := h1.left
  let h35 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h36 := h34.left
  let h37 := h34.right
  -- Disjunctions on the left can always be decomposed.
  cases h37
  case inl h38 =>
    -- One of the premise coincides with the conclusion.
    exact h38
  case inr h39 =>
    -- Disjunctions on the left can always be decomposed.
    cases h39
    case inl h40 =>
      -- Conjunctions on the left can always be decomposed.
      let h41 := h40.left
      let h42 := h40.right
      -- We want to use the implication h35 based on <expert-advice>. So we show its premise.
      have h43 : (p3 ∨ (p4 ∨ p4)) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h41
      -- We have shown the premise of h35, we can now drive its conclusion.
      let h44 := h35 h43
      -- We need to get the left conjuct of h44 based on <expert-advice>.
      let h45 := h44.left
      -- We need to get the right conjuct of h45 based on <expert-advice>.
      let h46 := h45.right
      -- False on the left can always be used.
      apply False.elim h46
    case inr h47 =>
      -- We want to use the implication h35 based on <expert-advice>. So we show its premise.
      have h48 : (p3 ∨ (p4 ∨ p4)) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h36
      -- We have shown the premise of h35, we can now drive its conclusion.
      let h49 := h35 h48
      -- We need to get the left conjuct of h49 based on <expert-advice>.
      let h50 := h49.left
      -- We need to get the right conjuct of h50 based on <expert-advice>.
      let h51 := h50.right
      -- False on the left can always be used.
      apply False.elim h51
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_909163901547396413510067779653 : (((((False ∨ ((True → (p2 → p4)) → (p3 ∨ True))) → (((p3 ∨ False) ∨ False) ∧ (p3 → p4))) ∧ ((True ∨ (p1 → p4)) ∨ (p5 ∨ False))) → p3) ∧ True) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h6 : (False ∨ ((True → (p2 → p4)) → (p3 ∨ True))) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h7
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h8 := h2 h6
      -- We need to get the left conjuct of h8 based on <expert-advice>.
      let h9 := h8.left
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Disjunctions on the left can always be decomposed.
        cases h10
        case inl h11 =>
          -- One of the premise coincides with the conclusion.
          exact h11
        case inr h12 =>
          -- False on the left can always be used.
          apply False.elim h12
      case inr h13 =>
        -- False on the left can always be used.
        apply False.elim h13
    case inr h14 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h15 : (False ∨ ((True → (p2 → p4)) → (p3 ∨ True))) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h16
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h17 := h2 h15
      -- We need to get the left conjuct of h17 based on <expert-advice>.
      let h18 := h17.left
      -- Disjunctions on the left can always be decomposed.
      cases h18
      case inl h19 =>
        -- Disjunctions on the left can always be decomposed.
        cases h19
        case inl h20 =>
          -- One of the premise coincides with the conclusion.
          exact h20
        case inr h21 =>
          -- False on the left can always be used.
          apply False.elim h21
      case inr h22 =>
        -- False on the left can always be used.
        apply False.elim h22
  case inr h23 =>
    -- Disjunctions on the left can always be decomposed.
    cases h23
    case inl h24 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h25 : (False ∨ ((True → (p2 → p4)) → (p3 ∨ True))) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h26
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h27 := h2 h25
      -- We need to get the left conjuct of h27 based on <expert-advice>.
      let h28 := h27.left
      -- Disjunctions on the left can always be decomposed.
      cases h28
      case inl h29 =>
        -- Disjunctions on the left can always be decomposed.
        cases h29
        case inl h30 =>
          -- One of the premise coincides with the conclusion.
          exact h30
        case inr h31 =>
          -- False on the left can always be used.
          apply False.elim h31
      case inr h32 =>
        -- False on the left can always be used.
        apply False.elim h32
    case inr h33 =>
      -- False on the left can always be used.
      apply False.elim h33
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55421072450835077845043747261 : ((((p3 ∧ ((p5 ∧ p1) ∨ p2)) ∨ p2) → (((False ∨ (((p1 ∨ (p3 ∨ p1)) → True) ∧ p2)) ∧ (p3 → ((p1 → p5) ∧ True))) ∧ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186654673067991561402041662142 : ((((True ∧ ((p3 ∧ p4) ∧ False)) ∨ True) ∧ ((p5 ∧ p1) → p2)) → (p3 ∨ ((True → ((p3 ∨ False) → p5)) ∨ ((p2 ∧ p4) → (p2 ∨ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h7.left
    let h10 := h7.right
    -- False on the left can always be used.
    apply False.elim h8
  case inr h11 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h12
    -- Conjunctions on the left can always be decomposed.
    let h13 := h12.left
    let h14 := h12.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66470998966021639155816550943 : ((True → ((((((p3 → (((False ∨ (p5 ∨ (p3 ∨ (p4 ∨ p5)))) ∧ p4) ∧ p5)) ∧ p3) → ((p3 ∧ p2) ∧ p4)) ∧ p3) ∧ True) ∨ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_745416408323811178067622329317 : ((((p5 ∧ p4) → (False ∧ (((p2 → p2) → False) ∨ (False ∧ (True ∨ ((p2 ∧ ((p2 → ((p4 ∧ (p2 ∨ p5)) ∨ False)) → p2)) ∧ p3)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118619982619457588065440254845 : ((p4 ∨ ((((False ∨ (True ∨ (p3 ∨ True))) ∨ (p2 ∨ p5)) ∨ p2) → ((p3 ∨ p1) ∨ ((False → (p4 → (p3 ∨ p4))) ∨ p5)))) ∨ (p4 ∨ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h4 =>
        -- False on the left can always be used.
        apply False.elim h4
      case inr h5 =>
        -- Disjunctions on the left can always be decomposed.
        cases h5
        case inl h6 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Implications on the right can always be decomposed.
          intro h7
          -- Implications on the right can always be decomposed.
          intro h8
          -- False on the left can always be used.
          apply False.elim h7
        case inr h9 =>
          -- Disjunctions on the left can always be decomposed.
          cases h9
          case inl h10 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h10
          case inr h11 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Implications on the right can always be decomposed.
            intro h12
            -- Implications on the right can always be decomposed.
            intro h13
            -- False on the left can always be used.
            apply False.elim h12
    case inr h14 =>
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h15 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h16
        -- Implications on the right can always be decomposed.
        intro h17
        -- False on the left can always be used.
        apply False.elim h16
      case inr h18 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h18
  case inr h19 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h20
    -- Implications on the right can always be decomposed.
    intro h21
    -- False on the left can always be used.
    apply False.elim h20



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309615418463805381319037584799 : (p2 ∨ (((False ∨ ((False ∨ ((False ∧ (False → p4)) ∧ (False ∨ (((p4 ∨ (p1 → False)) ∧ p3) ∨ p1)))) → p1)) → False) ∨ (p3 → (p1 → True)))) := by
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
theorem thm_5_vars_41220723881320816343346028541 : (((((((True ∨ True) → (p3 ∧ (False ∨ ((p1 ∧ p2) ∧ p5)))) ∧ (True ∨ True)) ∨ (p1 ∧ p1)) ∧ ((p1 → p1) → (p2 → p5))) ∨ True) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_71150241897799842273830285383 : (((((p3 → True) → (p1 ∧ p4)) ∨ (p4 ∧ ((((p2 → (False ∧ p3)) ∨ p5) → (p3 → ((False ∨ (p5 → True)) ∧ p4))) ∨ True))) ∧ p2) → p4) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h5 : (p3 → True) := by
      -- Implications on the right can always be decomposed.
      intro h6
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h7 := h4 h5
    -- We need to get the right conjuct of h7 based on <expert-advice>.
    let h8 := h7.right
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- One of the premise coincides with the conclusion.
      exact h10
    case inr h13 =>
      -- One of the premise coincides with the conclusion.
      exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231143221705185325208343016918 : (((p1 ∨ p4) ∨ p3) → (p4 → (p1 ∨ (p5 → ((p1 ∨ (((((p2 ∧ (False → p2)) → ((False ∨ True) ∨ p4)) → False) ∧ p5) ∨ p1)) ∨ p4))))) := by
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172341053130240221521397813798 : (((p3 ∧ (p4 ∧ (p5 ∧ (p2 → p2)))) ∧ ((p3 → (p3 ∨ (p3 → p4))) ∧ p1)) ∨ (p4 ∨ (False → ((p2 ∧ p2) ∨ (p5 ∧ (True ∧ p3)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58329212950693932543037482027 : (((False ∨ p1) ∧ ((((((p2 ∨ False) ∨ True) ∧ p1) → False) ∧ p5) ∧ ((p5 ∨ False) → (p1 ∨ (((False ∨ False) ∧ (p4 → p3)) ∧ p5))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_252399110017686629139568020069 : ((p5 → False) ∨ (((p3 ∨ ((((p5 ∧ p2) → (False ∨ p5)) ∧ (p4 → (p3 ∨ p3))) ∧ p5)) ∨ (((False → p5) ∧ p5) ∧ p4)) ∨ (p5 → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225632485631676735528628974563 : (((p1 → p4) ∧ p3) ∨ (p4 ∨ ((((p1 ∧ p5) ∨ p5) → (((p2 ∧ p4) ∨ (p1 ∧ p5)) ∨ (p2 ∨ p5))) ∨ (p5 ∧ ((True ∨ True) ∧ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_759190181013192638275789540709 : (((p2 ∧ (((p5 → (((p1 ∨ (((p2 → p1) ∧ p1) ∨ p4)) ∧ p5) ∧ p5)) ∨ ((((p1 ∧ p2) ∧ False) → True) ∨ True)) ∨ (p5 ∧ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_640103830194175097541935737558 : ((((((p1 → p1) ∧ p2) → ((False ∧ ((((p2 ∨ ((p4 ∧ p2) → p5)) ∨ ((False ∨ False) → p5)) ∨ p4) ∧ (False → p4))) → p3)) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68290177609212135755911070131 : ((p3 → (((((p3 ∧ (((p2 → True) ∨ p2) ∧ p1)) ∧ False) ∧ ((True ∧ p1) ∨ ((p1 ∧ True) ∧ p3))) ∨ p1) ∨ (True ∨ (p2 ∨ p4)))) ∨ p2) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49287400703265920213233096182 : (((p5 ∧ (((True → True) → ((p5 → (p3 ∨ (((p5 → True) ∨ p2) → False))) → (p5 ∨ p4))) ∨ (p3 → False))) ∨ (p5 ∧ (p3 → p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_909358195778144682867886112041 : (((((p1 ∨ (True → p1)) ∨ (((False ∨ (p5 ∨ True)) ∧ ((False ∨ False) ∧ p5)) ∧ (p2 ∧ p1))) ∧ (((p5 ∨ p5) ∨ (True ∧ p3)) → True)) → p1) ∧ True) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h6 =>
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h7 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h8 := h6 h7
      -- One of the premise coincides with the conclusion.
      exact h8
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Conjunctions on the left can always be decomposed.
    let h12 := h10.left
    let h13 := h10.right
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h14 =>
      -- False on the left can always be used.
      apply False.elim h14
    case inr h15 =>
      -- Disjunctions on the left can always be decomposed.
      cases h15
      case inl h16 =>
        -- Conjunctions on the left can always be decomposed.
        let h17 := h13.left
        let h18 := h13.right
        -- Disjunctions on the left can always be decomposed.
        cases h17
        case inl h19 =>
          -- False on the left can always be used.
          apply False.elim h19
        case inr h20 =>
          -- False on the left can always be used.
          apply False.elim h20
      case inr h21 =>
        -- Conjunctions on the left can always be decomposed.
        let h22 := h13.left
        let h23 := h13.right
        -- Disjunctions on the left can always be decomposed.
        cases h22
        case inl h24 =>
          -- False on the left can always be used.
          apply False.elim h24
        case inr h25 =>
          -- False on the left can always be used.
          apply False.elim h25
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_789229575770061162470422627148 : (((p5 ∨ ((((p5 ∨ (False ∨ (p3 ∨ ((p1 ∨ False) → p1)))) ∧ ((p3 ∧ p2) ∨ (p3 → p2))) ∧ p5) ∨ (True → ((p5 ∧ p2) → True)))) ∨ False) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62284139048429165597103858386 : ((p3 ∧ (((p3 ∧ (True → p2)) → ((p4 → p2) ∨ (p2 → (True ∨ ((p4 → p3) ∧ (p3 ∧ (False → ((True → p4) → p2)))))))) → p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_196906630241570008021746628573 : ((((((p1 ∧ False) ∧ True) ∧ p2) ∧ p1) ∨ p1) ∨ ((p3 ∧ (p4 → False)) → (False → (True → (p1 ∨ (p3 ∨ (p2 ∨ (p1 → (True ∨ p1))))))))) := by
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
theorem thm_5_vars_118125438239059609113704720990 : ((False ∨ ((((((True ∧ (p1 ∧ (p1 → True))) ∧ p3) ∧ (True ∧ (True ∨ p2))) → p1) → ((False → p2) → False)) ∨ (True ∧ True))) ∨ (p3 → False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53882905036680108210957080288 : ((((p1 ∨ p2) → (((p3 ∨ p1) → p1) ∧ (False → p3))) ∨ (((True ∧ p1) ∧ (True → (((p4 → p4) ∨ False) → (p4 ∧ p5)))) ∨ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300042509425820992663360944250 : (False ∨ ((p1 → ((False ∧ (p3 ∧ p3)) ∨ (p5 → ((p3 ∨ ((True ∨ (p1 ∨ (True ∧ p4))) ∨ (p3 → (p5 ∨ True)))) ∨ p3)))) ∧ (p1 → p1))) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112946065561042520255177236739 : (((True ∧ ((p5 ∧ ((p4 → (False ∧ ((True ∨ p4) ∨ ((p3 ∨ p5) → True)))) ∨ ((p1 ∨ (p5 ∧ p1)) ∧ p3))) ∨ p5)) → False) ∨ (p1 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_348842496302626829962071867153 : (p3 → (p2 ∨ (((p5 ∨ (((False ∨ ((p5 ∧ (p2 ∨ p1)) → p2)) → p5) ∧ ((p3 ∨ True) ∧ (p4 ∧ ((p3 ∨ p3) ∨ p3))))) ∨ True) ∧ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336442898206522588894509868877 : (p1 → ((p4 ∨ (((False ∧ p5) → ((p3 ∨ (p4 → p3)) ∨ False)) ∧ (((p5 ∧ ((p5 ∨ (p5 ∧ p4)) → (p3 ∧ p5))) ∧ p1) ∨ False))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_679124282853562632634554644715 : ((((p3 ∨ (((p5 ∧ False) ∨ (((False ∨ ((True ∧ (p1 → p1)) ∨ p4)) → p5) → (p4 ∧ p1))) ∧ True)) ∨ ((p3 → p3) ∨ (p5 → p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_913628927207906976468327098579 : ((((p1 → (((False ∧ (p3 ∨ ((False → (False → (True ∨ p5))) → p4))) → p5) ∨ (False ∨ p1))) → ((p5 → ((p3 → p4) ∧ True)) ∧ p3)) → p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p1 → (((False ∧ (p3 ∨ ((False → (False → (True ∨ p5))) → p4))) → p5) ∨ (False ∨ p1))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- One of the premise coincides with the conclusion.
  exact h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_669584363403242721411912555803 : ((((((p1 → p5) ∧ ((True ∨ p5) → (p2 ∧ (p4 ∨ ((p5 ∨ (False → False)) → p4))))) ∧ (p5 ∧ (p3 → p4))) ∨ ((p1 → False) → p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313953794583017251935647403724 : (p3 ∨ ((((False ∨ p2) → (((p3 ∨ False) → (p2 → (False ∨ (((p5 ∧ False) → (p3 → p3)) ∨ p3)))) ∧ False)) ∧ (False ∧ p5)) ∨ (False → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178198142753278213761542593167 : (((True ∨ (((p2 ∨ True) → ((True ∧ p1) ∨ p1)) → (False → p4))) → p5) ∨ (p2 → (True ∨ ((p1 → False) ∨ ((False ∧ p3) ∨ (False → p4)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171599872262337836152250354576 : ((((p2 ∨ (p3 ∧ (p2 ∨ (p1 → p4)))) ∧ ((True → (True ∧ True)) ∧ p5)) ∨ p2) ∨ (False ∨ (p3 → ((p3 → (p1 ∧ p2)) → (p5 ∨ True))))) := by
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
theorem thm_5_vars_41354504274078224602750146403 : ((((((((((p2 ∨ p3) ∧ ((True ∧ False) → False)) ∧ p4) → p5) ∨ p5) ∧ p1) ∧ p5) → ((((p4 ∨ p3) ∧ True) ∨ False) ∨ True)) ∨ p2) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_184055072026618717935233741427 : (((((p3 ∨ (p3 → p5)) ∧ (p3 ∧ p1)) ∨ (p2 ∨ p5)) ∨ p4) ∨ (((p2 → True) ∧ ((p4 ∨ (p1 → p5)) → (False ∧ (p3 ∨ True)))) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_708051612675600721413532481051 : ((((p3 ∨ ((p2 ∧ p2) ∧ (p2 ∧ (p1 ∨ p5)))) ∨ (p5 ∨ (((p3 ∨ p1) ∨ (False ∧ ((False ∨ p3) → ((False ∨ p3) → True)))) → p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207401083778019443217054973999 : (((p3 ∧ (p5 ∧ (p5 → p4))) ∨ False) → ((((True ∧ ((p1 → True) ∧ ((p3 ∨ p2) ∨ True))) → (p4 ∨ p1)) ∧ p3) ∨ (p4 ∨ (p5 ∧ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h5
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h7 =>
    -- False on the left can always be used.
    apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_738883089850613018223880526888 : ((((p3 ∧ True) ∨ (p2 ∧ ((((p5 ∨ p1) ∧ ((True → ((p5 ∧ ((p3 → (p1 ∨ p2)) → False)) ∧ p5)) ∧ p4)) → (p2 → p1)) ∧ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42622653284773692343622463348 : (((p3 ∨ ((False ∨ (((False ∧ p1) ∨ ((p5 ∧ (False ∧ p5)) → p5)) ∧ p3)) ∨ (p1 ∧ ((p2 → p2) ∧ ((p5 ∧ p1) ∨ p2))))) ∨ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_634554186178733344997687173554 : ((((((p1 ∧ p5) ∨ ((p1 ∨ (p4 ∨ ((False ∨ ((True ∧ p3) → (True → p2))) → False))) ∨ (True ∧ p1))) ∧ ((p3 ∨ p1) ∧ True)) → False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56023922708881933503222269437 : ((((False ∧ (False ∧ False)) ∨ False) ∨ (p2 → (((p5 ∨ p3) ∨ (p2 ∧ ((p3 → p4) → True))) ∨ (((p4 → p3) → (True ∨ p2)) ∨ p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190815267827172682604911393114 : (((p1 ∧ (False ∨ (True ∧ (p2 ∨ p3)))) ∨ (p2 ∨ p5)) ∨ (False → (p2 → (p4 ∧ (p2 ∧ (p2 ∧ ((p2 ∧ ((p4 ∨ False) → p3)) ∧ False))))))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- False on the left can always be used.
    apply False.elim h1
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h5
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219651520898730823023858264188 : ((False → (p1 ∧ (p5 ∨ p2))) → (((((True ∧ p4) ∨ ((((p4 → False) ∨ p1) ∨ p4) ∧ (p1 ∨ (p3 ∨ False)))) ∨ p1) → False) ∨ (True ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_188870573697412725261373464924 : (((p3 ∨ ((p5 ∨ p5) → p3)) ∨ (False → (p5 ∨ p2))) ∧ ((p1 ∨ ((p3 → (p1 ∧ p3)) ∨ p4)) ∨ (False ∨ ((p2 → True) ∧ (True ∨ p3))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48074894707187530943992596281 : ((((p4 ∧ ((p4 → p4) ∨ (p5 ∨ p2))) ∧ ((False ∨ (p4 ∨ (((p2 ∨ p2) ∧ p3) → (False → p2)))) → (p5 → False))) → (p3 ∨ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214473819770527990375119769448 : (((False ∧ p3) ∧ (p1 ∧ p1)) ∨ (((p3 ∧ False) ∨ ((p3 ∧ p3) → False)) → (p1 ∨ ((False ∧ (((p5 → (p4 → p4)) ∧ p2) → p1)) → p4)))) := by
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
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- False on the left can always be used.
    apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51155803814954163727822932018 : ((((False ∨ ((p3 → p1) ∧ (((p5 → ((p1 ∧ p3) → False)) ∨ p2) ∨ (p3 → p3)))) → p4) ∨ (False ∨ (True ∨ ((p3 ∨ True) ∧ p5)))) ∨ p2) := by
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
theorem thm_5_vars_171642434632991606931100083251 : ((((p4 → p3) ∨ ((True → ((p5 ∨ (p2 ∨ (p5 ∧ False))) ∨ p3)) ∧ p5)) ∨ True) ∨ ((False ∧ (p4 ∨ ((p4 ∧ False) ∨ (False ∧ p5)))) ∧ p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137843337860605163597186256211 : ((p3 ∨ ((((False ∨ p4) ∨ p1) ∧ (p3 ∨ p3)) ∧ ((p1 ∧ p3) ∧ ((p4 ∨ (p1 ∧ (p2 → (p3 ∧ p2)))) → p5)))) ∨ (False → (False ∧ p1))) := by
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
theorem thm_5_vars_263553883633154532668593811763 : (True ∧ ((((True → False) → (False ∨ ((p3 ∨ (True ∧ (p3 → ((p1 → (p2 → False)) ∧ p2)))) → p2))) ∨ False) ∨ ((True → (False ∨ p4)) ∨ False))) := by
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
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_659258308532958228679804450476 : ((((p4 → (False ∨ (p2 ∧ (p5 ∧ (((True ∨ True) ∨ ((p3 ∧ (p2 → (True ∨ True))) ∧ False)) ∨ (False ∨ (False → p3))))))) ∨ (False ∨ True)) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_784082755804633816802663796677 : (((p3 ∨ ((False ∨ p2) ∨ (((p1 ∧ ((((True ∨ p1) ∨ (True → (True → p2))) → False) ∨ p3)) → p1) → (((False ∨ True) ∨ True) → p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_604107256981374034404724507180 : ((((p5 ∨ ((True → p5) → (p5 ∨ (p3 → (((p3 ∧ False) ∨ (False ∧ p2)) ∨ (p5 ∧ ((p3 → False) ∧ (True ∧ (p3 ∧ p4))))))))) ∧ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171294058951982096735523209135 : (((((p1 ∨ (((False → p4) ∧ (False ∨ (p4 ∧ p4))) → p5)) ∧ p3) ∧ p3) ∧ p5) ∨ (((p3 → p5) ∨ p5) → (((p3 → True) ∧ p4) → p4))) := by
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
  cases h1
  case inl h5 =>
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h6 =>
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157031201596908153825269525477 : ((((p4 → p5) ∨ ((p5 → ((False → p4) ∨ (p5 ∧ p5))) → (p5 ∨ (p5 → (p3 ∧ p5))))) ∨ True) ∨ ((p2 → ((p5 ∧ p4) ∨ p5)) → p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164824947162672641846235331928 : ((((p2 ∨ p5) → (((p3 ∧ p5) ∨ ((p5 ∨ p5) ∨ p4)) ∧ ((p4 ∧ p1) ∨ p4))) ∨ p2) ∨ (p2 ∨ ((p4 → True) ∨ (True ∧ (p2 → p4))))) := by
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
theorem thm_5_vars_58471605038517358016743792385 : (((p3 ∨ p5) ∧ (False ∨ (((p2 → p5) ∧ p1) ∧ ((p5 ∧ ((((p1 → p5) ∨ (p3 ∨ p1)) ∨ p5) ∨ p4)) → (p2 → (p2 ∨ p2)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_194121926638652428054509672347 : ((False → (p1 ∨ ((p3 → (p3 ∨ True)) ∧ (p2 ∧ p5)))) → (((p3 → p4) → (((p2 ∧ (False ∧ p1)) ∧ p5) ∨ p4)) ∨ ((p3 ∧ True) → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54575357006783256437265404905 : (((p1 ∨ ((False → ((True ∨ p4) → p4)) ∧ p4)) ∨ (((p5 ∧ p3) ∨ (((p1 ∧ p2) ∨ p4) ∨ (p5 ∨ p2))) ∨ ((p4 → p3) ∧ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307269225136447961839017022510 : (p1 ∨ (p2 ∨ ((p2 → ((p3 ∨ p5) ∨ p2)) ∧ ((True ∧ p2) ∨ ((p1 ∨ (((True ∨ p2) ∧ (p3 ∧ p2)) → p3)) → ((p5 → True) ∨ p3)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h4
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h6
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119609672912307878220890182501 : ((p5 → (p4 ∨ (((p3 ∧ ((p2 ∨ ((p1 ∨ p3) → (p3 ∧ p4))) ∧ p5)) ∨ p2) → (((p1 → (p2 → p4)) ∨ p2) ∨ p2)))) ∨ (False ∨ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h9 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h10
      -- Implications on the right can always be decomposed.
      intro h11
      -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
      have h12 : (p1 ∨ p3) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h10
      -- We have shown the premise of h9, we can now drive its conclusion.
      let h13 := h9 h12
      -- We need to get the right conjuct of h13 based on <expert-advice>.
      let h14 := h13.right
      -- One of the premise coincides with the conclusion.
      exact h14
  case inr h15 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_750237598543333645965310789237 : (((True ∧ (((((p4 ∧ p1) → ((((True → (p5 → p4)) → True) → False) ∨ p5)) ∨ (p5 → ((p3 ∨ p1) ∨ False))) ∨ False) ∨ (p2 ∧ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_735397796143321245699185383830 : ((((p4 ∨ p2) ∧ (((p2 → (p4 ∧ ((p4 ∧ ((p2 → p3) ∧ (p4 ∨ (((p3 ∧ p4) ∧ p2) ∨ p1)))) → p4))) ∧ (p1 → p3)) → p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_318694779464373970259996203592 : (p4 ∨ ((((True → False) ∧ (p2 → (True ∨ (((False ∧ ((p4 ∨ ((p5 → p2) → p2)) ∨ p2)) ∧ p4) → True)))) ∧ (p4 → p3)) → (p5 ∨ p5))) := by
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
  have h6 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h7 := h4 h6
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_614094509544577331674017884753 : (((((p3 ∨ (p3 → (((p5 ∨ p4) ∧ p5) ∨ (((((p5 → False) ∨ True) ∨ p5) → (True ∧ p1)) ∧ p4)))) ∨ ((p5 ∨ True) ∨ p2)) ∨ True) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_66048252642975289679139885761 : ((p5 ∨ ((((p5 ∨ p1) ∨ ((p5 ∧ (p4 ∨ p3)) ∨ ((False → p5) ∧ (p2 ∧ (((False ∨ p5) → p2) ∧ (True ∧ p3)))))) ∧ p3) ∨ True)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231773961290911192988264436706 : (((p3 ∧ p4) → p5) → ((p4 ∧ (p1 ∨ (p3 → ((p5 ∧ (p4 ∨ p2)) → ((((p3 ∨ (True ∨ p4)) → (p4 ∧ p5)) ∨ p5) → False))))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



