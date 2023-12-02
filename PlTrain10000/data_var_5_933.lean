variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_730050953374074831913327227958 : (((((p1 ∨ p3) → True) → (((((p2 ∧ (p1 → p2)) → ((False → p5) ∨ p2)) ∧ ((p3 ∧ (p4 ∧ p2)) → True)) → p4) ∧ (p3 ∨ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_358008132658999214954128101913 : (p5 → (False ∨ ((p2 → False) ∨ (((p2 ∧ ((p2 ∨ (p1 ∨ ((False ∧ p1) ∧ (p2 ∨ (((p5 ∧ False) → p3) ∧ True))))) ∨ True)) ∨ p3) ∨ True)))) := by
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
theorem thm_5_vars_115673231663933851944795122925 : ((((p4 → p5) → (True → (p4 ∨ p1))) ∨ ((p1 → (p3 ∧ (p3 ∧ ((False ∨ p2) ∨ ((p3 → (p2 ∧ p2)) → p3))))) → p4)) ∨ (True ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313594271277089906493281180137 : (p3 ∨ (((((p4 → ((p1 ∧ True) → (p3 ∨ p5))) ∧ p3) ∨ True) → (((((False ∧ p2) ∨ p5) → ((p5 ∨ p4) ∨ p4)) → True) → p1)) → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p4 → ((p1 ∧ True) → (p3 ∨ p5))) ∧ p3) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : ((((False ∧ p2) ∨ p5) → ((p5 ∨ p4) ∨ p4)) → True) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h4
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_209039441716893949653661805769 : ((p1 ∨ ((True ∨ (False ∧ p5)) ∧ p4)) → (p4 ∨ ((True → (p5 ∨ True)) ∧ (((p1 → ((True ∨ False) ∨ (True ∨ p3))) → (p3 ∧ p3)) ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- False on the left can always be used.
      apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231818504691223394691307617048 : (((p4 ∧ p5) → p4) → (((p3 → p2) → p4) ∨ (p1 → ((p4 ∨ ((True ∨ p1) ∨ p2)) ∨ (p4 → (((p3 ∨ (p3 ∧ p4)) ∨ p1) ∧ p5)))))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40843900847010155712390702641 : ((((p4 → (p5 ∧ (p1 ∨ (((((p2 ∧ True) ∧ (((p2 ∧ p4) ∨ p1) ∨ True)) ∧ (p4 ∨ (p2 ∧ False))) ∨ False) ∨ True)))) → False) ∨ True) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_175020020411152683811728921135 : ((p1 ∧ (((p4 ∨ (True ∧ False)) → ((p2 ∨ p3) ∨ True)) → ((True ∧ p1) ∧ p3))) → (((p3 ∨ ((True ∨ (p4 → p5)) ∧ p2)) ∧ p3) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : ((p4 ∨ (True ∧ False)) → ((p2 ∨ p3) ∨ True)) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- False on the left can always be used.
      apply False.elim h9
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h10 := h3 h4
  -- We need to get the right conjuct of h10 based on <expert-advice>.
  let h11 := h10.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h11
  -- One of the premise coincides with the conclusion.
  exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_88937264015496287456788609007 : (((False → ((False → p2) ∨ False)) → (((p5 ∧ p2) → (((p2 ∧ p4) → ((p5 ∨ (p3 → False)) ∨ (p3 ∧ (p2 ∧ p5)))) → p2)) ∧ p1)) → p1) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (False → ((False → p2) ∨ False)) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165887027860316557222099232107 : ((((False ∧ p4) → p4) → ((p5 ∨ (p4 ∧ (p1 ∨ p4))) ∧ (((p2 ∧ True) ∧ p3) ∨ p1))) ∨ (True ∨ ((False ∨ p2) ∧ ((False ∧ p3) ∧ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193192406914482999672628268559 : ((((p4 ∨ p4) ∨ (p5 ∨ p1)) → ((p1 ∨ p5) ∨ True)) → ((p2 → (False ∧ (False ∨ True))) ∨ ((False ∧ False) ∨ (p5 → (p3 → (p2 ∨ p3)))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51463086590081173360688580063 : (((((p4 → p1) ∨ (p3 → (((False → True) → p1) → p3))) ∨ ((False ∧ (p5 ∨ True)) → p3)) → (False ∧ ((True → True) → (True → p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119645660477036035426805012697 : ((((((((p4 → p1) → (p2 ∧ (False → p2))) ∨ (False ∨ ((p3 ∨ True) → p3))) → (p2 → False)) ∧ (p2 → True)) ∧ p4) ∧ p3) → (p2 → p5)) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
  have h9 : (((p4 → p1) → (p2 ∧ (False → p2))) ∨ (False ∨ ((p3 ∨ True) → p3))) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h10
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h2
    -- Implications on the right can always be decomposed.
    intro h11
    -- False on the left can always be used.
    apply False.elim h11
  -- We have shown the premise of h7, we can now drive its conclusion.
  let h12 := h7 h9
  -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
  have h13 : p2 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h12, we can now drive its conclusion.
  let h14 := h12 h13
  -- False on the left can always be used.
  apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300531814130298027517236392232 : (False ∨ (((((p2 → (False ∨ p5)) → (p2 ∧ ((p3 → p1) ∨ ((p2 ∨ (p3 ∧ p3)) ∨ p5)))) → p4) ∧ p3) ∨ ((True ∨ (p4 → True)) ∨ p3))) := by
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
theorem thm_5_vars_83011060476192483289261034313 : (((((p5 → False) ∨ ((p2 ∨ (False ∧ (p4 ∨ p4))) ∨ True)) ∨ (True ∨ ((True ∧ p5) → (True ∧ p4)))) → (True ∧ ((p2 → False) ∧ False))) → p3) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p5 → False) ∨ ((p2 ∨ (False ∧ (p4 ∨ p4))) ∨ True)) ∨ (True ∨ ((True ∧ p5) → (True ∧ p4)))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166138614274101802829774473602 : ((True ∧ (p3 ∧ ((False → (p1 ∧ (False ∧ (p4 ∨ p3)))) → (((p5 ∨ True) ∧ p1) ∧ False)))) ∨ ((p4 ∨ p4) → (False → (p4 → (p2 ∨ False))))) := by
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
theorem thm_5_vars_264932050456534566262570625709 : (True ∧ ((p4 ∧ p2) → (((p3 ∧ (p2 → (p4 → p3))) ∧ (p1 ∧ (((p2 ∧ (p1 ∧ p4)) ∧ p1) ∨ (p1 → (p5 ∧ False))))) ∨ (p5 → True)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
theorem thm_5_vars_156612263278988034863093670871 : ((((False ∨ ((p2 ∨ (False ∨ (((p4 ∧ True) ∧ p2) ∨ p1))) ∧ ((p3 ∧ p2) ∨ p3))) ∧ p4) ∧ p5) ∨ ((((True → p2) ∨ p2) ∧ p4) → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_624987736148932962469758206322 : ((((p5 ∨ (p5 ∨ (((((True ∧ p4) ∧ (((((False → p2) ∨ p4) → (p1 ∧ p3)) ∧ True) ∧ p1)) ∨ (p3 ∨ p2)) ∧ p5) ∨ True))) ∨ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305613686943479131198781238735 : (p1 ∨ (((p1 ∨ ((p2 ∧ p2) ∨ ((p3 → p4) ∨ (True → False)))) → False) → (p2 → (p3 ∧ (p1 ∧ ((((False ∨ p5) → True) ∧ False) ∧ p1)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : (p1 ∨ ((p2 ∧ p2) ∨ ((p3 → p4) ∨ (True → False)))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h2
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- False on the left can always be used.
  apply False.elim h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h5 : (p1 ∨ ((p2 ∧ p2) ∨ ((p3 → p4) ∨ (True → False)))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h2
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h5
  -- False on the left can always be used.
  apply False.elim h6
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h7
  -- True on the right can always be proven directly.
  apply True.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h8 : (p1 ∨ ((p2 ∧ p2) ∨ ((p3 → p4) ∨ (True → False)))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h2
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h9 := h1 h8
  -- False on the left can always be used.
  apply False.elim h9
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h10 : (p1 ∨ ((p2 ∧ p2) ∨ ((p3 → p4) ∨ (True → False)))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h2
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h11 := h1 h10
  -- False on the left can always be used.
  apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205685413809260465506567816507 : (((p4 ∨ p4) ∨ ((p5 ∨ False) ∨ p2)) ∨ (p2 ∨ ((True ∧ ((p4 ∧ ((p2 ∨ p5) ∧ (((p1 ∧ p2) ∧ True) ∨ True))) → p1)) → (True ∧ True)))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62731336403577471219079987266 : ((p4 ∧ (((False ∨ True) → ((((False → ((False ∧ p2) → p5)) ∨ (((p4 ∧ True) ∧ (p1 ∧ p5)) ∨ p1)) ∧ p2) ∨ p5)) ∧ (False ∧ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66221589258793099835893985775 : ((p5 ∨ ((p5 ∨ ((p2 ∧ ((False → (p5 ∧ p5)) → p3)) ∨ p1)) ∧ ((p2 ∨ (p2 ∨ ((False ∨ p2) ∨ ((p5 ∨ p4) ∨ True)))) ∨ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_716030194167570193248941051497 : ((((((p3 → True) ∧ True) → p1) ∧ (p2 ∨ (((((p3 ∨ p3) → (p3 → p2)) ∧ p1) ∧ (p1 ∧ (False ∨ p2))) ∧ (p5 ∨ (p4 ∨ True))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180492141413510660715225455819 : ((((p2 → (False ∧ (p4 → p3))) ∨ (p1 → True)) ∧ ((p4 → p4) ∨ p1)) → ((True ∧ ((True ∨ p5) → ((p1 ∨ p1) ∨ True))) ∨ (p2 ∨ p5))) := by
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- Implications on the right can always be decomposed.
      intro h6
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h9 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- Implications on the right can always be decomposed.
      intro h10
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
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
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h14 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- Implications on the right can always be decomposed.
      intro h15
      -- Disjunctions on the left can always be decomposed.
      cases h15
      case inl h16 =>
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- Implications on the right can always be decomposed.
      intro h19
      -- Disjunctions on the left can always be decomposed.
      cases h19
      case inl h20 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h21 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66564716974056873195146514688 : ((True → ((((p5 ∧ p3) ∧ ((((p2 → p3) ∨ ((p2 ∧ (False → False)) ∧ p5)) → p4) ∧ p3)) ∧ ((True ∨ p2) ∨ p5)) ∨ (False ∨ True))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184988308853301260689813108966 : (((False ∧ True) ∧ (((p5 → ((True ∧ False) ∧ p4)) ∨ False) ∨ True)) ∨ ((((p4 ∧ p4) ∨ p5) → ((((p2 ∧ True) ∧ p4) → p5) ∨ True)) ∨ False)) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_789326153785521593202871178507 : (((p5 ∨ ((((p5 → p3) ∧ (p1 ∨ (False ∧ (True ∨ (p3 ∨ p3))))) ∨ (p2 ∧ (p2 ∨ True))) ∨ (True ∨ ((True ∨ (p4 ∨ p5)) ∨ False)))) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_231802077490169130421492772883 : (((p4 ∧ p2) → p5) → ((p5 ∧ (((False ∧ p5) ∨ (p3 ∨ ((p2 ∨ p4) ∧ ((p5 ∧ p2) → p2)))) → (p3 ∧ ((p1 → False) ∨ p5)))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64747171700020425226202813053 : ((p2 ∨ (((((((p2 ∧ False) ∧ p3) ∨ (False ∧ p4)) → p3) ∧ (p5 ∨ (False → (p3 ∨ True)))) ∧ (p5 ∧ ((p4 ∧ p4) ∧ p5))) ∧ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159872367671199304476127712336 : (((((p2 ∧ ((((True → p1) ∧ p5) → (p3 → p3)) ∨ p4)) ∨ ((p1 ∨ p1) → p1)) ∧ True) → p4) → (True ∧ ((p2 ∧ p2) ∨ (p3 ∨ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p2 ∧ ((((True → p1) ∧ p5) → (p3 → p3)) ∨ p4)) ∨ ((p1 ∨ p1) → p1)) ∧ True) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h5 =>
      -- One of the premise coincides with the conclusion.
      exact h5
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157508303131698511687663805805 : (((p1 ∧ (((p1 ∨ p2) ∧ p4) ∨ ((((p5 ∨ True) → (True ∨ p2)) ∧ p5) ∨ p5))) ∨ (p2 → p2)) ∨ (((p2 ∨ p5) ∨ p5) → (p5 → p2))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40614184695632391017572419777 : (((((((p5 ∧ p5) → p1) ∨ ((p4 → p3) → ((p5 ∧ (p5 → (p2 ∧ ((p4 ∧ (p3 → p5)) ∧ p3)))) ∧ True))) ∨ p1) → p4) ∨ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118379063222412080626016222281 : ((p2 ∨ (((((((p1 → (p5 ∨ True)) → False) → p3) ∨ False) ∧ True) ∨ p2) ∧ (((p4 ∧ p2) ∧ p1) ∨ ((p4 → p5) ∨ p2)))) ∨ (False → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_766579668863825293902874980734 : (((p4 ∧ (p4 ∧ (p5 ∧ ((p1 ∧ ((p5 ∨ (((p2 ∧ (((True ∧ (p4 ∧ True)) ∨ (True ∨ p3)) ∨ p4)) → p5) → True)) → False)) ∧ p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_655086639267111210417190055018 : (((((True ∨ (p3 ∨ ((((p2 ∨ p2) → ((p5 ∨ p3) → p1)) ∧ (((p5 ∧ True) ∨ True) ∧ (p2 ∨ p3))) ∧ p4))) → p5) ∨ (p5 ∨ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166378504100489322550542390421 : ((False ∨ (((p5 ∨ False) ∧ ((p1 ∧ (p2 ∧ p5)) ∧ (p3 ∨ (p2 ∨ (p3 → p1))))) ∨ p5)) ∨ ((True ∨ (p1 ∨ (True ∧ (p1 → p4)))) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_251973827943419831983116942783 : ((p4 → False) ∨ ((((((((p3 → True) ∨ p4) ∨ (p5 ∨ p3)) ∧ p5) → (p2 ∧ False)) → ((p4 → p1) ∧ p3)) ∨ (p1 ∧ p3)) ∨ (False ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137177889250223372552377223765 : ((False ∧ (((((False ∧ p4) ∧ p1) ∧ ((p5 ∧ p4) ∨ p1)) ∨ (p5 ∨ True)) → (p2 ∨ ((p3 ∨ (p5 → False)) ∨ False)))) ∨ (False ∨ (False → False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168416869895694530102351761061 : (((p3 ∧ p4) → ((False ∨ p2) → (((p4 ∧ p2) ∧ (False ∨ (p4 ∧ (True ∧ p4)))) → False))) → ((p3 → p1) → (((p3 ∧ p5) ∨ False) → p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h7 : p3 := by
      -- One of the premise coincides with the conclusion.
      exact h5
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h8 := h2 h7
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- False on the left can always be used.
    apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51985516799028085841133575932 : ((((p3 ∨ False) ∨ ((p3 → p5) ∨ ((p3 ∨ ((p1 → (False ∧ p1)) ∨ p2)) ∧ p1))) ∨ (((p5 → True) ∧ False) → (p5 ∧ (False ∨ p3)))) ∨ p5) := by
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
  apply False.elim h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_143013962277104467110804874772 : ((True → (True ∧ (((p1 ∨ True) → ((((True → False) ∨ (False ∨ ((False ∧ p1) → p3))) ∧ p2) → p3)) ∧ (p5 ∨ p5)))) → ((p2 ∧ p3) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321061151248108869759237812129 : (p4 ∨ (p1 ∨ ((((((p4 ∧ (p1 ∨ True)) ∨ p4) ∨ (True ∨ p3)) ∧ (((((p2 → False) → True) → True) ∨ p1) ∨ p2)) ∨ False) ∨ (False ∨ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57459267152214885453493035318 : (((p5 ∨ (p4 → p1)) ∨ ((((p1 → (True ∨ p1)) ∧ (p5 ∨ True)) ∨ ((((True ∨ p1) → (p2 → False)) ∧ (False ∧ False)) → p4)) → p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119077351428081904459307784743 : ((p1 → (((p5 ∧ ((p3 ∨ p2) ∧ (p4 ∨ (False → ((((False ∧ False) → True) ∧ p2) → False))))) → False) ∨ (p1 ∧ (True ∨ p3)))) ∨ (p4 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149831789879824917349153361123 : ((p1 ∨ (((p4 ∧ True) → (p5 ∨ (p2 ∧ ((p4 → (p5 → p5)) → p2)))) ∧ (True ∨ (True ∨ (p5 → True))))) ∨ (((p1 ∧ p3) ∧ p5) → p3)) := by
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
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313979455118861746929622428556 : (p3 ∨ (((((p5 ∨ True) ∨ p1) ∨ ((p1 ∨ False) → p3)) ∧ (((p3 ∧ ((p3 → p1) ∧ ((p2 ∨ False) → p2))) ∧ True) ∨ False)) ∨ (p4 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_343593745442158636672401718355 : (p2 → ((p2 → p5) → ((p3 ∧ (((p3 ∨ p3) → ((p3 ∨ (p3 ∨ p1)) ∨ ((p5 ∨ (p5 ∧ (False → p1))) ∧ False))) → p1)) ∨ (False → False)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_758730551327150442333218655212 : (((p2 ∧ ((False ∧ (((p2 ∧ p3) ∨ p3) → (((p5 ∨ p3) ∧ True) → ((((p2 ∧ p5) → False) ∧ p2) ∨ (False ∧ (p2 ∧ p1)))))) ∨ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_716450417120151826436450435407 : (((((True ∧ p4) ∨ (p1 → True)) ∧ ((p2 ∨ ((((p2 ∨ p5) ∨ p1) ∨ False) → (p5 ∨ p5))) ∧ ((p2 ∧ p5) ∨ (p4 ∨ (p2 → p3))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_603739684876256434640428290241 : ((((p4 ∨ (((p5 ∨ (((((p3 ∨ p5) → ((p4 ∨ p2) ∧ (p1 ∨ p5))) → p1) → p3) ∨ True)) → p2) ∨ (True ∨ (False ∧ True)))) ∧ True) ∨ p1) ∧ True) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_21951143654407841662216105538 : ((((True → p1) → (p5 ∨ (True ∨ (p5 ∨ True)))) ∧ (p2 ∨ ((((False ∧ p3) ∨ (p3 → p5)) ∨ p5) → ((p3 → p2) ∨ (p1 → True))))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
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
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- False on the left can always be used.
      apply False.elim h5
    case inr h7 =>
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225900666098402757652300837915 : (((p1 ∧ p3) ∨ p1) ∨ (True ∧ (p4 → (((p5 → (p2 ∨ p5)) ∧ (p3 ∨ (((p2 ∨ True) ∧ p3) → (p4 → p4)))) ∨ (p5 ∨ (p1 ∨ p5)))))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h7 =>
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h8 =>
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190306175029516702713388648824 : ((((False → ((p4 ∧ (p1 ∧ p3)) → p3)) → False) ∨ True) ∨ ((p3 → (p2 ∨ (p1 → p2))) ∧ (p2 ∨ ((p2 → False) ∨ ((p1 ∨ p1) ∨ True))))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_216727812196126363681931595538 : ((((p1 ∨ p1) → True) ∧ p3) → (((False → p4) → ((p5 ∧ p1) ∧ p4)) → ((p4 ∨ (False ∧ p1)) ∨ (p3 → (p4 → (True → (p1 ∨ p2))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h5 : (False → p4) := by
    -- Implications on the right can always be decomposed.
    intro h6
    -- False on the left can always be used.
    apply False.elim h6
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h7 := h2 h5
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345314422828468897658407763844 : (p3 → ((((p3 ∧ ((((p4 → p5) → True) ∧ (((True ∨ (((p4 ∨ p4) ∨ False) ∨ p1)) ∧ (p5 → p4)) → p1)) ∧ True)) ∧ False) ∧ True) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_702630536337982933453603114529 : (((((p3 → ((p4 ∨ (p4 → (p3 → False))) ∧ False)) → p2) ∨ (((True ∨ p1) → ((p5 ∨ p1) → False)) ∨ ((False ∧ False) → (True ∨ False)))) ∨ p1) ∧ True) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193260265108075155860817068620 : (((p2 ∨ (p5 → p4)) ∧ (True ∧ (p1 ∧ (p5 ∨ p5)))) → (p3 ∨ (p3 ∨ ((((p2 ∧ (p4 ∧ p4)) → ((False ∧ p5) → True)) ∧ p5) ∨ p1)))) := by
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
    let h7 := h6.left
    let h8 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h7
  case inr h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h3.left
    let h13 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h14 := h13.left
    let h15 := h13.right
    -- Disjunctions on the left can always be decomposed.
    cases h15
    case inl h16 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h14
    case inr h17 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156648828565081824791527976012 : (((((p4 ∧ (((((p3 → p3) ∧ (True → True)) → (False → True)) → p3) → p4)) → False) → False) ∧ p3) ∨ (True ∨ ((p3 ∧ (False ∨ p1)) ∧ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112649779374525046651810591981 : (((((p3 ∧ (p2 → ((p5 ∧ (False ∧ p3)) ∨ ((p3 → True) ∨ (p1 ∧ p3))))) ∧ (p3 ∨ p2)) ∧ (p4 → (p3 ∨ False))) → p1) ∨ (False → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_774035459124098418397085854149 : (((False ∨ ((((p3 → (p1 ∧ ((((p4 ∧ p2) ∧ True) → p1) → (((p1 ∨ p4) ∨ p5) ∨ p2)))) ∧ (True ∧ p1)) ∧ p5) ∨ (True ∨ p1))) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_224234565382054410115871639713 : ((True → (p1 → True)) ∧ ((False ∧ p5) ∨ ((p2 ∧ (((p1 → p2) ∧ p2) → p4)) → ((True → p4) → ((False ∧ (p3 ∧ (p3 ∧ p5))) ∨ p4))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h7 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h8 := h4 h7
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_705095796795681115364990047360 : ((((p5 → (((p4 → (True → True)) → p3) ∧ (False → True))) → ((((p1 ∨ (((p5 → p4) ∧ (p3 → p3)) → False)) → False) ∧ p3) ∨ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_685798819308721913488287958000 : (((((((True ∨ ((p1 ∧ (p2 → p4)) → p2)) ∧ ((p3 ∧ False) → False)) ∨ (p4 ∨ p1)) → p4) → ((False ∨ p1) ∧ ((False → p2) → p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184560661179921687816983767210 : (((((False ∨ p1) → (False ∧ p2)) → (p3 ∧ p5)) → (p2 ∧ p5)) ∨ (((p2 → p2) ∨ (True → (p5 → (p4 ∧ (True ∨ (p3 ∧ p2)))))) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65811032249841846860294555912 : ((p4 ∨ (((True → p3) ∧ ((p3 → (p1 → p5)) ∨ p1)) → (((p2 → p3) ∨ p4) ∧ (p2 → (((p1 ∧ (p1 ∨ p4)) ∧ False) ∨ p3))))) ∨ p2) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h6 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h7 := h2 h6
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h8 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h9
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h10 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h11 := h2 h10
    -- One of the premise coincides with the conclusion.
    exact h11
  -- Implications on the right can always be decomposed.
  intro h12
  -- Conjunctions on the left can always be decomposed.
  let h13 := h1.left
  let h14 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h14
  case inl h15 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
    have h16 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h13, we can now drive its conclusion.
    let h17 := h13 h16
    -- One of the premise coincides with the conclusion.
    exact h17
  case inr h18 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
    have h19 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h13, we can now drive its conclusion.
    let h20 := h13 h19
    -- One of the premise coincides with the conclusion.
    exact h20



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137502140478813604495996130212 : ((p5 ∧ (((False ∧ ((p5 → False) ∨ (True ∨ (p3 ∧ p3)))) ∨ (p1 → (p3 → (p2 ∨ p2)))) ∧ ((p3 → p1) ∨ p2))) ∨ (False → (True ∧ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218766881255829472939794080225 : ((p1 ∧ ((p1 ∧ p1) ∨ p1)) → (((False ∨ True) → (p3 ∨ (((False ∧ (p5 ∧ p1)) ∧ ((p2 ∧ p5) ∨ (p1 ∧ p3))) ∧ p3))) ∨ (True ∨ p5))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300225619604446794591155055472 : (False ∨ ((((p3 → (False → (p5 ∨ p2))) → ((p5 → p2) ∧ False)) ∧ (((True ∧ p4) ∨ (False ∨ p1)) ∧ (False ∨ (p3 → p2)))) → (p2 → False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h10 =>
      -- False on the left can always be used.
      apply False.elim h10
    case inr h11 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h12 : (p3 → (False → (p5 ∨ p2))) := by
        -- Implications on the right can always be decomposed.
        intro h13
        -- Implications on the right can always be decomposed.
        intro h14
        -- False on the left can always be used.
        apply False.elim h14
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h15 := h3 h12
      -- We need to get the right conjuct of h15 based on <expert-advice>.
      let h16 := h15.right
      -- False on the left can always be used.
      apply False.elim h16
  case inr h17 =>
    -- Disjunctions on the left can always be decomposed.
    cases h17
    case inl h18 =>
      -- False on the left can always be used.
      apply False.elim h18
    case inr h19 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h20 =>
        -- False on the left can always be used.
        apply False.elim h20
      case inr h21 =>
        -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
        have h22 : (p3 → (False → (p5 ∨ p2))) := by
          -- Implications on the right can always be decomposed.
          intro h23
          -- Implications on the right can always be decomposed.
          intro h24
          -- False on the left can always be used.
          apply False.elim h24
        -- We have shown the premise of h3, we can now drive its conclusion.
        let h25 := h3 h22
        -- We need to get the right conjuct of h25 based on <expert-advice>.
        let h26 := h25.right
        -- False on the left can always be used.
        apply False.elim h26



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_723981809925500457750462049748 : ((((False ∧ (p3 ∨ True)) ∧ ((((p5 ∨ True) ∨ (p3 → True)) → (((False ∧ p4) ∨ ((False ∧ (p4 ∧ p3)) ∨ (p2 ∨ p1))) → p5)) ∨ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_141640856165727780356685224596 : (((p1 → (p5 → p3)) → (((((((p1 ∧ p1) ∧ False) ∨ True) ∧ p4) → p5) → p2) ∧ (False ∧ ((p2 ∨ p5) ∨ False)))) → (p3 → (p5 ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : (p1 → (p5 → p3)) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h3
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- We need to get the left conjuct of h7 based on <expert-advice>.
  let h8 := h7.left
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160163506304423296116605467829 : (((((p3 ∨ p5) ∨ (p3 → p5)) ∧ (p2 ∧ ((p3 → (p2 ∧ (p2 ∨ p1))) ∧ p2))) ∧ (p3 → p1)) → ((p2 ∨ (p1 ∨ p4)) → (p5 ∨ True))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Conjunctions on the left can always be decomposed.
        let h10 := h7.left
        let h11 := h7.right
        -- Conjunctions on the left can always be decomposed.
        let h12 := h11.left
        let h13 := h11.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h14 =>
        -- Conjunctions on the left can always be decomposed.
        let h15 := h7.left
        let h16 := h7.right
        -- Conjunctions on the left can always be decomposed.
        let h17 := h16.left
        let h18 := h16.right
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h14
    case inr h19 =>
      -- Conjunctions on the left can always be decomposed.
      let h20 := h7.left
      let h21 := h7.right
      -- Conjunctions on the left can always be decomposed.
      let h22 := h21.left
      let h23 := h21.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h24 =>
    -- Disjunctions on the left can always be decomposed.
    cases h24
    case inl h25 =>
      -- Conjunctions on the left can always be decomposed.
      let h26 := h1.left
      let h27 := h1.right
      -- Conjunctions on the left can always be decomposed.
      let h28 := h26.left
      let h29 := h26.right
      -- Disjunctions on the left can always be decomposed.
      cases h28
      case inl h30 =>
        -- Disjunctions on the left can always be decomposed.
        cases h30
        case inl h31 =>
          -- Conjunctions on the left can always be decomposed.
          let h32 := h29.left
          let h33 := h29.right
          -- Conjunctions on the left can always be decomposed.
          let h34 := h33.left
          let h35 := h33.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h36 =>
          -- Conjunctions on the left can always be decomposed.
          let h37 := h29.left
          let h38 := h29.right
          -- Conjunctions on the left can always be decomposed.
          let h39 := h38.left
          let h40 := h38.right
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h36
      case inr h41 =>
        -- Conjunctions on the left can always be decomposed.
        let h42 := h29.left
        let h43 := h29.right
        -- Conjunctions on the left can always be decomposed.
        let h44 := h43.left
        let h45 := h43.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h46 =>
      -- Conjunctions on the left can always be decomposed.
      let h47 := h1.left
      let h48 := h1.right
      -- Conjunctions on the left can always be decomposed.
      let h49 := h47.left
      let h50 := h47.right
      -- Disjunctions on the left can always be decomposed.
      cases h49
      case inl h51 =>
        -- Disjunctions on the left can always be decomposed.
        cases h51
        case inl h52 =>
          -- Conjunctions on the left can always be decomposed.
          let h53 := h50.left
          let h54 := h50.right
          -- Conjunctions on the left can always be decomposed.
          let h55 := h54.left
          let h56 := h54.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h57 =>
          -- Conjunctions on the left can always be decomposed.
          let h58 := h50.left
          let h59 := h50.right
          -- Conjunctions on the left can always be decomposed.
          let h60 := h59.left
          let h61 := h59.right
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h57
      case inr h62 =>
        -- Conjunctions on the left can always be decomposed.
        let h63 := h50.left
        let h64 := h50.right
        -- Conjunctions on the left can always be decomposed.
        let h65 := h64.left
        let h66 := h64.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_242803390075726334406313466901 : ((p3 → p3) ∧ ((((p2 → False) ∨ ((p4 ∨ ((p1 → True) ∧ ((p5 ∨ p5) → (False ∨ ((p2 → p4) → p4))))) ∨ p4)) ∨ p5) ∨ (p5 → True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137659490888273835322127241657 : ((False ∨ (p1 ∧ (((p2 ∨ False) ∨ (p2 → (p5 → ((True ∨ True) ∨ (p2 → p3))))) ∧ (True → ((p1 ∨ p4) → False))))) ∨ (p5 ∨ (False → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_801320738942117548424494289891 : (((p2 → (((((False ∨ p2) ∧ ((p1 ∨ p3) ∨ p1)) ∧ (p5 ∧ p2)) ∧ (p3 ∨ p5)) → ((p1 → (p1 ∧ p3)) → ((p2 → p4) → p3)))) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Conjunctions on the left can always be decomposed.
  let h5 := h2.left
  let h6 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- Conjunctions on the left can always be decomposed.
  let h9 := h7.left
  let h10 := h7.right
  -- Disjunctions on the left can always be decomposed.
  cases h9
  case inl h11 =>
    -- False on the left can always be used.
    apply False.elim h11
  case inr h12 =>
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h13 =>
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h14 =>
        -- Conjunctions on the left can always be decomposed.
        let h15 := h8.left
        let h16 := h8.right
        -- Disjunctions on the left can always be decomposed.
        cases h6
        case inl h17 =>
          -- One of the premise coincides with the conclusion.
          exact h17
        case inr h18 =>
          -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
          have h19 : p1 := by
            -- One of the premise coincides with the conclusion.
            exact h14
          -- We have shown the premise of h3, we can now drive its conclusion.
          let h20 := h3 h19
          -- We need to get the right conjuct of h20 based on <expert-advice>.
          let h21 := h20.right
          -- One of the premise coincides with the conclusion.
          exact h21
      case inr h22 =>
        -- Conjunctions on the left can always be decomposed.
        let h23 := h8.left
        let h24 := h8.right
        -- Disjunctions on the left can always be decomposed.
        cases h6
        case inl h25 =>
          -- One of the premise coincides with the conclusion.
          exact h25
        case inr h26 =>
          -- One of the premise coincides with the conclusion.
          exact h22
    case inr h27 =>
      -- Conjunctions on the left can always be decomposed.
      let h28 := h8.left
      let h29 := h8.right
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h30 =>
        -- One of the premise coincides with the conclusion.
        exact h30
      case inr h31 =>
        -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
        have h32 : p1 := by
          -- One of the premise coincides with the conclusion.
          exact h27
        -- We have shown the premise of h3, we can now drive its conclusion.
        let h33 := h3 h32
        -- We need to get the right conjuct of h33 based on <expert-advice>.
        let h34 := h33.right
        -- One of the premise coincides with the conclusion.
        exact h34
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_594892331080068033922405511505 : ((((((p5 ∧ p4) ∨ (((p1 ∨ ((p1 → False) → p4)) → (p3 ∧ p3)) → p2)) ∧ (((p5 ∧ p2) ∨ True) ∨ ((p3 ∧ p3) ∧ False))) ∧ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_779820429090952724108289290635 : (((p2 ∨ (((p5 ∨ False) ∨ ((p1 ∨ (((((((p3 ∨ p5) → p4) ∨ p5) → p1) ∨ p3) → (p5 ∨ p4)) → p1)) ∨ (p4 ∧ False))) → p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319298224292382229312955810399 : (p4 ∨ (((((p1 → p3) → (True ∧ True)) ∨ ((False → (p4 ∨ (True ∨ p5))) → p5)) ∨ p1) → (p5 ∨ (((p3 ∧ p3) ∨ (p1 → True)) ∧ True)))) := by
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
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h4
      -- True on the right can always be proven directly.
      apply True.intro
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- True on the right can always be proven directly.
      apply True.intro
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45336039133629849769257643172 : (((p3 ∧ (p5 ∧ (p4 → ((p1 ∨ p2) ∨ ((((p1 ∧ p3) ∨ False) ∧ False) → (p2 → ((p4 ∨ ((p3 ∨ p1) → p1)) → True))))))) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341678903774838740382797404306 : (p2 → ((((((((p4 ∧ ((True ∧ p2) ∨ p1)) ∨ (p3 → (p5 ∧ ((p4 → p3) ∧ False)))) ∨ False) → p4) ∧ p5) ∧ p3) → False) ∨ (p1 ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184690335117101490378898492565 : (((((p4 → p4) ∨ (p5 ∨ p2)) ∧ True) → ((p3 ∨ p2) → p5)) ∨ (True ∨ (p4 ∧ ((p3 ∨ (True ∨ ((p5 ∨ True) ∨ p1))) → (p2 ∨ p2))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45948104778798412857168387361 : (((p5 → (((((p4 → (p4 ∨ p4)) ∧ p1) ∨ ((p5 ∧ True) ∨ (p3 → ((p2 ∨ p2) → p4)))) → p1) ∧ ((p4 → True) → p2))) → p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215152461192486190031822904251 : ((True ∧ ((p2 ∧ p1) ∧ p5)) ∨ (((p2 ∧ p2) ∧ True) ∨ ((((True ∨ (p2 ∧ (p1 ∨ p4))) ∨ p4) ∨ (p1 ∧ p2)) ∨ (True → (p4 → True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40080542915302365801339986323 : (((((((((p3 → p4) ∨ ((p4 ∧ False) → p2)) ∧ ((p3 ∧ p3) → (True → (p1 ∨ p5)))) → p4) ∧ (p2 ∨ p2)) → p3) ∧ p4) ∨ True) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192295538753754420004438820991 : ((((p4 ∨ True) → ((p2 ∧ (True ∧ p1)) ∧ p5)) ∧ p4) → (((p3 → False) ∨ True) ∧ (((p1 ∨ p1) ∨ (False → (p2 ∨ (p5 ∧ p3)))) ∨ False))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h6
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_195482219206360556139038022100 : (((False ∨ (p3 ∧ p5)) ∨ (p4 ∨ (p4 ∨ True))) ∧ (False → ((True ∨ p2) ∨ (p1 → ((p4 ∨ p1) ∨ ((p4 ∨ p5) → (p4 ∧ (p3 → p5)))))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198714938739420288888138777078 : ((p5 ∨ ((False ∧ (p2 ∨ True)) ∧ (p4 ∧ p1))) ∨ ((p4 ∧ (p3 → (p4 ∨ (False ∨ p1)))) → (((p3 ∨ p3) ∧ p4) → (p2 → (False ∨ p2))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h1.left
    let h8 := h1.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h1.left
    let h11 := h1.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45898849854380951673419746887 : (((p4 → (((((True → p4) ∨ (p1 → ((p3 ∧ (((False → p5) ∧ (p4 ∧ True)) ∧ (p1 → p1))) ∨ False))) ∧ p3) → p2) ∨ p3)) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134592629339967369895627201386 : (((((p2 → (((((True ∧ ((p4 → p4) ∨ (p4 → p3))) ∧ p1) ∨ p5) ∧ p1) → p4)) ∧ p1) → (True ∨ True)) → p1) ∨ ((p3 ∧ p4) → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167606524090634340918996269641 : (((p1 → (p3 ∧ ((((p1 → p3) ∧ p5) → p4) → (p4 → (p1 ∧ True))))) ∨ (p2 ∧ p3)) → (((p5 ∨ False) → ((p5 ∨ p5) ∧ p4)) ∨ True)) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52720698684561037318196500703 : ((((((p2 ∨ True) → False) ∧ (p1 ∨ (p5 ∨ (p4 → (False → p4))))) ∧ p4) → (((p3 → p4) → (p3 ∧ ((False → p5) ∨ p1))) → False)) ∨ False) := by
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
  cases h6
  case inl h7 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h8 : (p2 ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h9 := h5 h8
    -- False on the left can always be used.
    apply False.elim h9
  case inr h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h12 : (p2 ∨ True) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h13 := h5 h12
      -- False on the left can always be used.
      apply False.elim h13
    case inr h14 =>
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h15 : (p2 ∨ True) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h16 := h5 h15
      -- False on the left can always be used.
      apply False.elim h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_32993483442352132946341059433 : ((p3 ∨ (((((False → p1) → (p1 ∨ p1)) → p3) ∧ (True ∨ ((p1 ∨ p1) ∧ p5))) ∨ (((((p3 → p2) → False) → p2) → p1) → True))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_175339689453276374153058234008 : ((p5 ∨ ((p3 → (((True ∨ p3) ∨ False) ∧ ((p1 ∧ (p1 ∧ p1)) → p2))) ∧ p4)) → ((((p3 → p4) ∨ True) → (p1 ∧ (p2 ∧ False))) → p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h7 : ((p3 → p4) ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h8 := h2 h7
    -- We need to get the right conjuct of h8 based on <expert-advice>.
    let h9 := h8.right
    -- We need to get the right conjuct of h9 based on <expert-advice>.
    let h10 := h9.right
    -- False on the left can always be used.
    apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60032795068054481394078036932 : (((p1 ∨ p3) → ((((((((p4 → p5) → True) ∧ p2) ∨ False) → p2) → p2) ∧ p2) ∨ (((p1 ∨ p3) ∧ (p3 → (False ∨ p3))) ∧ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234448907781574940295135932364 : ((p2 → (p4 ∧ p3)) → (((((p5 ∨ p3) ∧ ((False → p4) → (((False → True) ∨ (p4 ∨ ((p3 ∨ p3) → p2))) ∧ p1))) ∨ p2) ∨ True) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_254845719112081653569775200609 : ((p3 ∧ p5) → (((p2 ∨ p5) ∧ p5) ∧ (((((p1 ∧ (False ∧ False)) ∧ (p5 ∧ (True → (True → p5)))) ∨ p2) ∨ p5) ∧ ((p1 ∧ p2) → p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h5
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h6 := h1.left
  let h7 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h7
  -- Implications on the right can always be decomposed.
  intro h8
  -- Conjunctions on the left can always be decomposed.
  let h9 := h8.left
  let h10 := h8.right
  -- Conjunctions on the left can always be decomposed.
  let h11 := h1.left
  let h12 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_730154811719844803640059768385 : (((((p5 ∨ p3) → p1) → ((True → (p3 ∨ (p3 ∨ ((((p5 → False) ∧ ((p4 → p3) ∧ (p1 → p5))) ∨ p1) ∧ (p1 ∧ p5))))) ∨ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317745374967445555245874997154 : (p4 ∨ ((((((p5 → False) ∧ (False → False)) ∨ p4) ∧ (((p4 ∧ (p3 → False)) ∧ (p2 → False)) → True)) ∧ ((p3 ∨ p4) ∨ (True ∧ p4))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_17306245046157866653013527305 : (((((p1 ∧ True) ∨ True) → (((p2 ∧ True) ∨ (False → True)) ∧ (((False ∨ (False ∨ False)) ∧ p2) ∧ (p4 ∧ True)))) → ((p3 → p1) → p5)) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : ((p1 ∧ True) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- We need to get the left conjuct of h6 based on <expert-advice>.
  let h7 := h6.left
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- False on the left can always be used.
      apply False.elim h10
    case inr h11 =>
      -- False on the left can always be used.
      apply False.elim h11
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56417735140128115350090164629 : ((((p1 ∧ p1) ∧ (p3 ∨ p2)) → (True ∧ ((((True ∨ True) ∧ ((p3 ∨ p5) → ((p1 ∧ (p2 ∧ p4)) ∨ p4))) ∧ (p1 → False)) ∧ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



