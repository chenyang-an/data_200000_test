variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_685156636570438402886292584766 : ((((p3 ∨ (True → (p4 ∨ (((True → p5) ∨ ((p3 ∨ p5) → p5)) ∨ ((p3 ∧ p1) ∧ p1))))) ∨ ((True ∧ True) ∨ ((True → p2) ∧ False))) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42910169737622396132763128982 : (((p3 → (p3 ∧ (False ∧ (((p3 ∨ ((p4 ∧ (p4 ∧ False)) ∨ p3)) ∧ ((p4 ∧ (((p3 ∧ True) ∨ p2) → False)) ∨ p2)) ∨ p3)))) ∨ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58352879529276263385077451933 : (((False ∨ p5) ∧ (True ∧ (((p1 ∧ (p4 ∨ p4)) ∧ (p2 → ((p3 ∧ (True ∧ (True ∨ (p5 ∨ (p3 ∨ p3))))) ∨ (p3 ∨ p2)))) ∧ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_69170554527834262661504151127 : ((p5 → (((p1 ∨ ((((False → True) → p1) ∨ p1) ∧ p2)) ∧ (((False → p1) ∨ p4) ∧ p5)) ∨ (p5 ∧ ((p5 ∧ p3) ∨ (False ∧ p4))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_302058285655172470828229850061 : (False ∨ (True ∧ (p5 ∨ (((p3 ∨ ((p5 → p4) ∨ ((False → (p2 ∧ ((False ∧ False) ∨ p5))) ∧ (False ∨ (False → False))))) → p3) ∨ (p1 → p1))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150884727593724513346309104818 : ((((True ∧ ((p5 ∨ True) → False)) ∨ ((((p1 → ((p5 → True) ∨ p5)) → (p3 → p3)) ∨ p1) → p1)) ∨ p1) → (p4 ∨ (p1 ∨ (True → p1)))) := by
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
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h6 : (p5 ∨ True) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h7 := h5 h6
      -- False on the left can always be used.
      apply False.elim h7
    case inr h8 =>
      -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
      have h9 : (((p1 → ((p5 → True) ∨ p5)) → (p3 → p3)) ∨ p1) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h10
        -- Implications on the right can always be decomposed.
        intro h11
        -- One of the premise coincides with the conclusion.
        exact h11
      -- We have shown the premise of h8, we can now drive its conclusion.
      let h12 := h8 h9
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h12
  case inr h13 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322284481462967121265077794646 : (p5 ∨ ((((((True → p2) ∧ (p5 ∨ p3)) ∧ ((p4 → True) → (p2 ∧ (((False ∧ p3) ∧ (True → p3)) → (p4 ∧ True))))) → p1) → p3) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61079182945952515188447503117 : ((False ∧ ((p2 → (False ∧ (((((False ∧ p5) ∧ (p5 → p4)) ∧ p4) → (True ∧ (p3 ∨ True))) → p5))) ∧ (p1 ∨ (True ∧ (p1 → True))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300471498727511047196036459899 : (False ∨ ((p5 ∧ (p4 → (p3 → (((True → p1) ∨ (p4 ∧ (True ∨ False))) ∨ (False → ((p4 ∧ p2) ∨ (p2 ∨ p3))))))) → (p3 ∨ (p1 ∨ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165949048274477983549696070871 : (((p3 ∨ False) ∧ (True → ((p2 ∨ (p4 ∨ (p5 → (p2 ∨ p3)))) ∧ ((p2 ∧ p1) ∨ p4)))) ∨ ((p1 ∧ ((False ∨ p3) ∧ (p2 ∨ p3))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58273886483994130768664971293 : (((p5 ∧ p5) ∧ ((p3 ∧ p2) ∨ (((p2 ∨ False) → (((p1 → (p1 → p2)) ∨ p5) → (((p1 ∨ (p2 ∧ False)) ∧ p3) ∧ p3))) ∨ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115654399268840841731396822629 : ((((p1 ∨ (p5 ∨ p2)) ∧ (False ∨ False)) ∨ (((p4 → False) ∨ (p5 ∨ (((True ∨ (p3 ∧ True)) → p1) ∧ (True → True)))) ∧ True)) ∨ (p3 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299449163568750238765598878883 : (False ∨ ((p2 ∨ (p1 ∨ (p3 → (((((p2 ∨ p5) ∨ p2) ∧ p1) ∧ (((p2 → p3) → p2) → (p3 ∨ (p3 ∨ True)))) ∧ (False → False))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_717254378761804335212329217803 : ((((p3 ∨ (p2 ∧ (p1 ∧ p2))) ∧ ((((p5 ∨ (((((p1 → p2) ∧ p5) → True) → p1) ∧ p2)) ∧ ((False → p1) ∨ p1)) → p3) ∧ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165394102679422593723768088399 : (((p5 ∧ ((False ∨ (True ∧ ((p2 → (p5 → p1)) → p2))) ∧ p4)) ∨ ((False ∧ p5) → p3)) ∨ (((((False ∨ p2) ∧ p2) ∨ p4) ∨ p1) → p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_324400094514504373060600611720 : (p5 ∨ ((((p1 ∧ p2) → (p2 ∧ p1)) → p5) → (((((p3 ∨ (False ∧ ((p1 → False) ∧ p1))) → ((p2 ∨ p5) ∧ p4)) ∨ p5) ∨ p1) ∧ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p1 ∧ p2) → (p2 ∧ p1)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- One of the premise coincides with the conclusion.
    exact h5
    -- Conjunctions on the left can always be decomposed.
    let h6 := h3.left
    let h7 := h3.right
    -- One of the premise coincides with the conclusion.
    exact h6
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h8 := h1 h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h8
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h9 : ((p1 ∧ p2) → (p2 ∧ p1)) := by
    -- Implications on the right can always be decomposed.
    intro h10
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- One of the premise coincides with the conclusion.
    exact h12
    -- Conjunctions on the left can always be decomposed.
    let h13 := h10.left
    let h14 := h10.right
    -- One of the premise coincides with the conclusion.
    exact h13
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h15 := h1 h9
  -- One of the premise coincides with the conclusion.
  exact h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_264897985652298808396388249808 : (True ∧ ((p5 → p1) ∨ (True → ((p3 ∧ (p2 → p4)) → (((False → True) → p5) ∨ ((((True ∨ (p3 ∧ False)) → p5) ∨ p1) ∨ (p3 ∨ p2))))))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50828681348359921163090003021 : (((((((p4 ∧ ((p5 ∨ p5) ∧ p2)) ∧ ((False → True) ∨ p5)) → (p5 ∨ p5)) → p2) ∧ p1) ∧ ((p3 ∨ True) ∨ ((p4 ∧ p3) ∨ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137700193436159382835973362296 : ((p1 ∨ ((((p5 ∨ ((p5 ∧ ((True ∧ p4) ∧ False)) ∧ p4)) ∨ ((p3 ∨ p2) ∨ p2)) ∨ p5) ∧ (p5 → (p2 ∧ p3)))) ∨ (p4 ∨ (False → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_591287018393501398835215908895 : ((((((((((p3 ∨ p1) ∧ p4) ∨ (p3 ∧ p4)) → ((p4 ∨ True) ∧ True)) ∨ (True ∨ p5)) → ((p1 ∨ p5) → p1)) ∧ (p4 → p4)) ∧ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_4525813205102081902615376398 : (p3 → ((((((p2 → ((False → (p1 ∧ p5)) ∧ p4)) ∨ p5) → p4) → ((p1 ∨ True) ∨ (p2 ∧ p1))) ∧ p4) → (True ∧ (p5 ∨ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134713692281410620235365454907 : ((((True ∨ (False ∨ False)) ∧ ((p3 ∧ (p2 ∨ (p5 ∨ (p4 ∨ p5)))) ∨ ((p3 ∧ ((True ∧ p4) → p2)) ∧ p2))) → False) ∨ (True ∨ (p4 ∧ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_618192740747711778203785469316 : (((((((p1 ∧ False) ∨ p1) ∧ p3) ∨ (p1 ∨ (True ∧ ((p5 → (True → p2)) ∧ (True ∧ (p1 → ((False ∧ (p4 → p2)) ∨ p5))))))) ∨ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_747844244122307038839247597433 : ((((False → p3) → ((((p4 ∨ p2) ∨ True) ∧ (((((p2 → p2) ∧ p4) ∧ p1) → (p2 → p3)) ∧ p2)) ∨ ((p1 → p4) ∨ (False → False)))) ∨ p5) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213222575398090228046170119924 : ((((True ∧ False) → False) ∧ p2) ∨ ((p2 ∨ False) ∨ (p4 ∨ (p1 ∨ (p4 ∨ (p2 → ((((p4 → True) ∨ ((p4 → p4) ∨ False)) ∨ p3) → p2))))))) := by
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
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- One of the premise coincides with the conclusion.
        exact h1
      case inr h7 =>
        -- False on the left can always be used.
        apply False.elim h7
  case inr h8 =>
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179648587773542268794108731989 : ((p5 → ((p1 ∨ (p4 ∨ ((p3 ∧ (p4 ∨ p3)) ∨ (p3 → True)))) ∨ p5)) ∨ ((((False ∧ p3) → p1) ∨ p4) ∨ ((p1 ∨ (p5 ∧ p2)) ∨ p1))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64299209617823911841406618069 : ((False ∨ (p4 → (p4 ∧ (p4 → ((((p1 → (p2 ∨ ((p2 → p1) ∧ p5))) ∨ p2) ∨ p1) ∨ ((p2 ∧ True) ∨ (p3 → (p3 → p4)))))))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231402654927803715061663773257 : (((p1 → p1) ∨ p4) → (p1 → (True ∧ (((((p1 ∨ p4) ∧ (True → p2)) ∧ (p3 ∧ True)) → ((((p5 ∧ False) ∨ False) ∧ p1) ∨ p1)) ∨ False)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h6.left
      let h11 := h6.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h9
    case inr h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h6.left
      let h14 := h6.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
  case inr h15 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h16
    -- Conjunctions on the left can always be decomposed.
    let h17 := h16.left
    let h18 := h16.right
    -- Conjunctions on the left can always be decomposed.
    let h19 := h17.left
    let h20 := h17.right
    -- Disjunctions on the left can always be decomposed.
    cases h19
    case inl h21 =>
      -- Conjunctions on the left can always be decomposed.
      let h22 := h18.left
      let h23 := h18.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h21
    case inr h24 =>
      -- Conjunctions on the left can always be decomposed.
      let h25 := h18.left
      let h26 := h18.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178237761225018844693163504510 : (((p5 → ((p1 ∧ p2) ∨ ((p4 ∨ ((False → p4) → p1)) ∧ p4))) → p2) ∨ (((p4 ∨ p5) ∧ ((p3 ∨ (p5 → False)) ∧ (p4 ∧ p4))) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57818374453370851727530662830 : (((p3 ∧ (p2 ∨ p2)) → (p1 → ((((((False ∨ p4) ∧ ((False → (p3 → (p4 ∧ False))) ∧ p4)) ∧ False) ∨ p2) → False) → (False ∧ p4)))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h7 : ((((False ∨ p4) ∧ ((False → (p3 → (p4 ∧ False))) ∧ p4)) ∧ False) ∨ p2) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h6
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h8 := h3 h7
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h10 : ((((False ∨ p4) ∧ ((False → (p3 → (p4 ∧ False))) ∧ p4)) ∧ False) ∨ p2) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h9
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h11 := h3 h10
    -- False on the left can always be used.
    apply False.elim h11
  -- Conjunctions on the left can always be decomposed.
  let h12 := h1.left
  let h13 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h13
  case inl h14 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h15 : ((((False ∨ p4) ∧ ((False → (p3 → (p4 ∧ False))) ∧ p4)) ∧ False) ∨ p2) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h14
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h16 := h3 h15
    -- False on the left can always be used.
    apply False.elim h16
  case inr h17 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h18 : ((((False ∨ p4) ∧ ((False → (p3 → (p4 ∧ False))) ∧ p4)) ∧ False) ∨ p2) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h17
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h19 := h3 h18
    -- False on the left can always be used.
    apply False.elim h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185221514473682610541924112723 : ((False ∧ ((p5 ∨ ((((p4 ∨ False) ∨ p3) ∧ False) ∨ p5)) ∨ p2)) ∨ (True ∧ (((p2 ∨ ((True → ((p1 ∨ p2) ∧ p1)) → p1)) ∨ p2) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- One of the premise coincides with the conclusion.
  exact h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_209550935036169032310940778423 : ((p5 → (((True → True) ∨ False) ∧ False)) → (((True → (((True ∨ p1) ∧ p3) ∨ p5)) ∨ (p4 → True)) ∨ ((False ∨ ((True ∨ False) → p4)) ∧ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49995830238052399485543734542 : ((((False ∧ (((p2 → ((p1 ∨ p3) → p4)) → False) → False)) ∨ (((p5 ∧ (False → False)) → p2) ∨ p3)) ∧ (((p4 ∨ p3) → False) ∧ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_330403748184875784213768923831 : (True → (p2 ∨ (p5 ∨ ((p4 ∧ ((((p1 ∨ (False → p3)) ∨ (p1 ∧ p5)) → ((p4 → (True ∨ (p1 ∨ p5))) ∨ p4)) → (p2 ∧ p3))) ∨ True)))) := by
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
theorem thm_5_vars_354863741552272420511633424940 : (p5 → (((p4 → False) → ((p4 ∧ (p3 ∧ (((p3 ∧ p5) → p4) ∧ (p3 ∧ (False ∨ ((((p5 → True) ∧ p1) ∧ True) → False)))))) ∨ p3)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322379809800496217258706690837 : (p5 ∨ ((((p3 ∧ (p4 → ((p1 ∨ ((p5 ∨ p4) → p2)) → ((True ∨ p4) ∧ p1)))) ∧ p3) ∧ ((p2 → p5) → ((p4 → False) ∨ p5))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_676864190749311326537952036651 : ((((p4 ∨ ((((True ∧ ((False ∧ (((p2 ∨ p2) ∧ p3) → (p4 ∨ p5))) ∧ p5)) ∨ True) ∧ True) ∧ p4)) ∧ (((p2 ∨ p4) ∨ p1) ∨ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345594556650758477134808421427 : (p3 → (((p2 → False) ∧ ((((p5 → (p5 ∨ (p5 ∨ p4))) → (((False ∧ ((True ∧ p3) ∧ p3)) ∧ p5) ∨ (False → p5))) ∧ True) → p2)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184643642127112643693059171118 : (((((p3 → (p4 ∨ p2)) ∧ False) ∧ True) ∨ ((True ∧ p1) ∧ False)) ∨ (False ∨ ((False → (p3 → p4)) ∨ ((((p4 ∧ p2) → True) ∨ p2) ∧ p4)))) := by
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
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300087483132480047163008590186 : (False ∨ (((((True → p5) → p1) ∨ ((((p1 ∧ (True → p5)) → p1) → (p5 ∨ ((p1 ∧ True) → p3))) ∧ True)) ∨ (p1 ∨ p2)) ∨ (True ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60762502379226619988420296964 : ((True ∧ ((p1 → p1) ∧ ((((p3 ∨ ((False ∨ True) → p1)) ∧ ((((p1 ∧ (False → p4)) ∨ True) ∨ p1) → (p5 ∨ p2))) ∨ True) ∨ p1))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_631770235480654630167778642658 : ((((((True ∧ (p3 ∧ (p5 → (((p3 → False) → p1) ∨ p4)))) ∨ (p1 ∧ (p5 → (((p2 ∧ p3) ∧ (p2 → False)) → False)))) → p2) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_888294971549615953152472841324 : (((((((p1 ∧ (p5 ∧ (((True ∧ p2) ∧ p3) ∧ (True ∨ True)))) → (p5 ∨ p3)) → p5) ∨ (p1 → ((p2 ∧ False) → True))) → (p5 ∧ False)) → p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((((p1 ∧ (p5 ∧ (((True ∧ p2) ∧ p3) ∧ (True ∨ True)))) → (p5 ∨ p3)) → p5) ∨ (p1 → ((p2 ∧ False) → True))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h2
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- False on the left can always be used.
  apply False.elim h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156959452096871839705189416286 : ((((p4 ∨ (((p5 ∨ p2) ∧ (p3 ∨ (p1 ∨ (p1 → p1)))) ∨ p5)) ∨ ((p2 → p2) ∧ True)) ∨ p2) ∨ (True ∨ (p5 ∨ ((False → p5) → True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207141642062956666576401046746 : (((False → (True ∧ (p1 → p2))) ∧ p1) → ((((p2 ∨ True) ∧ (p4 ∧ (p4 ∧ (p3 → (p4 ∧ p1))))) → (p2 ∨ p5)) ∨ ((p2 ∧ p2) → p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181401932484612197542222018814 : ((p2 ∨ (((p2 → (((False ∨ (p1 ∨ p5)) ∧ True) ∨ p2)) ∨ p4) ∨ False)) → ((((p3 → p3) ∧ p5) ∨ (p1 ∨ True)) ∧ (p2 ∨ (False → False)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h5 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h6 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h7 =>
      -- False on the left can always be used.
      apply False.elim h7
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h8 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h12
        -- False on the left can always be used.
        apply False.elim h12
      case inr h13 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h14
        -- False on the left can always be used.
        apply False.elim h14
    case inr h15 =>
      -- False on the left can always be used.
      apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313405392147830828173217307143 : (p3 ∨ (((p2 ∧ ((((False ∧ (((p1 ∧ (p2 ∨ p4)) ∨ ((p5 → (False ∨ p1)) ∨ p2)) ∧ p3)) ∨ True) ∧ (p3 → p3)) → False)) ∧ True) → p4)) := by
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
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h6 : (((False ∧ (((p1 ∧ (p2 ∨ p4)) ∨ ((p5 → (False ∨ p1)) ∨ p2)) ∧ p3)) ∨ True) ∧ (p3 → p3)) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
    -- Implications on the right can always be decomposed.
    intro h7
    -- One of the premise coincides with the conclusion.
    exact h7
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h8 := h5 h6
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61552361400113064488418977755 : ((p1 ∧ (((p2 ∧ ((True → p1) ∨ (p4 ∧ False))) ∨ p5) ∧ (((p3 ∨ p3) ∨ (((True ∨ p4) ∨ (p3 ∨ p1)) ∧ p5)) → (True → False)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_964342105683585447703213720615 : ((((True ∧ False) ∨ (((p4 ∨ True) → (p3 ∨ p2)) ∧ (((p3 ∧ (((p2 ∧ True) ∧ p2) ∧ p3)) ∨ (True ∧ ((False ∨ p2) → p3))) ∧ p4))) → p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- Conjunctions on the left can always be decomposed.
      let h13 := h12.left
      let h14 := h12.right
      -- Conjunctions on the left can always be decomposed.
      let h15 := h13.left
      let h16 := h13.right
      -- Conjunctions on the left can always be decomposed.
      let h17 := h15.left
      let h18 := h15.right
      -- One of the premise coincides with the conclusion.
      exact h14
    case inr h19 =>
      -- Conjunctions on the left can always be decomposed.
      let h20 := h19.left
      let h21 := h19.right
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h22 : (p4 ∨ True) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h9
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h23 := h6 h22
      -- Disjunctions on the left can always be decomposed.
      cases h23
      case inl h24 =>
        -- One of the premise coincides with the conclusion.
        exact h24
      case inr h25 =>
        -- We want to use the implication h21 based on <expert-advice>. So we show its premise.
        have h26 : (False ∨ p2) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h25
        -- We have shown the premise of h21, we can now drive its conclusion.
        let h27 := h21 h26
        -- One of the premise coincides with the conclusion.
        exact h27
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_777848341366240700397809007061 : (((p1 ∨ (((p4 → p3) → (p3 ∧ p1)) ∨ ((((p3 → p4) → (p5 ∧ (p2 ∧ (((p3 ∨ p2) ∧ p5) ∨ True)))) → (True ∨ p1)) ∨ p2))) ∨ p2) ∧ True) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_732885397478217942728220559255 : ((((p2 ∧ p1) ∧ ((p2 ∨ (p3 ∧ ((((p3 ∨ p3) ∧ p4) ∨ (p1 ∧ ((False ∧ (True → p3)) ∨ p3))) → p1))) ∨ (False → (True → p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138938451575248524667078211531 : (((((((p3 ∧ ((p4 ∧ p4) ∧ p3)) ∨ (p2 → (p2 ∨ True))) ∨ ((p5 → True) ∧ (False ∨ False))) ∨ True) ∧ p1) ∨ p2) → ((p2 ∨ p5) ∨ True)) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Disjunctions on the left can always be decomposed.
        cases h6
        case inl h7 =>
          -- Conjunctions on the left can always be decomposed.
          let h8 := h7.left
          let h9 := h7.right
          -- Conjunctions on the left can always be decomposed.
          let h10 := h9.left
          let h11 := h9.right
          -- Conjunctions on the left can always be decomposed.
          let h12 := h10.left
          let h13 := h10.right
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
        -- Conjunctions on the left can always be decomposed.
        let h16 := h15.left
        let h17 := h15.right
        -- Disjunctions on the left can always be decomposed.
        cases h17
        case inl h18 =>
          -- False on the left can always be used.
          apply False.elim h18
        case inr h19 =>
          -- False on the left can always be used.
          apply False.elim h19
    case inr h20 =>
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
theorem thm_5_vars_261351785093218180717318175350 : ((p5 → False) → (True ∧ (False ∨ (p1 → ((p5 ∧ p1) → (((p1 ∧ ((p1 ∧ True) ∨ p4)) ∨ ((p1 → p2) ∨ (p4 ∧ p4))) → (False ∨ p3))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
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
      -- Conjunctions on the left can always be decomposed.
      let h11 := h3.left
      let h12 := h3.right
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h13 : p5 := by
        -- One of the premise coincides with the conclusion.
        exact h11
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h14 := h1 h13
      -- False on the left can always be used.
      apply False.elim h14
    case inr h15 =>
      -- Conjunctions on the left can always be decomposed.
      let h16 := h3.left
      let h17 := h3.right
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h18 : p5 := by
        -- One of the premise coincides with the conclusion.
        exact h16
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h19 := h1 h18
      -- False on the left can always be used.
      apply False.elim h19
  case inr h20 =>
    -- Disjunctions on the left can always be decomposed.
    cases h20
    case inl h21 =>
      -- Conjunctions on the left can always be decomposed.
      let h22 := h3.left
      let h23 := h3.right
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h24 : p5 := by
        -- One of the premise coincides with the conclusion.
        exact h22
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h25 := h1 h24
      -- False on the left can always be used.
      apply False.elim h25
    case inr h26 =>
      -- Conjunctions on the left can always be decomposed.
      let h27 := h26.left
      let h28 := h26.right
      -- Conjunctions on the left can always be decomposed.
      let h29 := h3.left
      let h30 := h3.right
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h31 : p5 := by
        -- One of the premise coincides with the conclusion.
        exact h29
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h32 := h1 h31
      -- False on the left can always be used.
      apply False.elim h32



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263420259864479274849063335401 : (True ∧ ((p5 ∧ (((False → False) → ((p4 → p2) ∧ (((p2 ∧ True) ∧ ((p2 → p2) ∧ True)) ∧ (p3 ∧ True)))) ∨ True)) ∨ (p2 ∨ (True ∨ p4)))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_751884684959593926713320442542 : (((True ∧ (p2 ∨ ((p3 ∧ (((p2 ∧ p5) ∨ p2) ∧ (p2 ∧ ((p1 → p3) → p4)))) ∧ ((((p4 → p1) → p3) ∨ (p2 → p3)) → True)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135706475122993110951167124719 : ((((p4 ∧ p4) ∨ ((((((p4 → True) ∧ False) ∨ p2) → p3) ∧ p3) ∧ p3)) ∧ (p5 → ((True ∧ (p2 ∨ p3)) ∨ p4))) ∨ ((p1 → p5) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346393702153495622927667873592 : (p3 → ((p3 → (((p3 ∧ ((p5 ∨ p2) ∧ (((p2 ∧ (p2 → p5)) ∧ (p5 ∧ False)) ∧ (p2 ∨ False)))) ∨ p3) ∧ (p3 → False))) ∨ (p3 ∨ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2078977083664485528553029620 : ((((((p1 → (p5 ∧ p1)) ∨ p2) ∧ ((p3 ∨ p3) ∧ (p4 ∧ p5))) ∧ False) ∨ (p3 → p2)) ∨ ((p1 → (True → p3)) ∨ (p3 → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_761177696229222584462755794252 : (((p2 ∧ (p4 → (p2 ∧ (((False ∧ p1) ∨ ((p1 ∨ True) ∧ ((((False ∨ p5) ∧ p2) → (False → p3)) ∨ (p1 ∨ (p1 → p1))))) ∨ p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_123917137296890181082494087196 : ((((((((p3 → p5) ∨ p2) ∨ p4) ∨ p3) ∧ p5) ∧ (p3 ∨ p1)) ∧ (((((True ∨ p2) ∧ (p1 ∨ p5)) → p4) → p4) ∧ p3)) → (p5 ∨ p1)) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Disjunctions on the left can always be decomposed.
        cases h5
        case inl h11 =>
          -- Conjunctions on the left can always be decomposed.
          let h12 := h3.left
          let h13 := h3.right
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h7
        case inr h14 =>
          -- Conjunctions on the left can always be decomposed.
          let h15 := h3.left
          let h16 := h3.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h14
      case inr h17 =>
        -- Disjunctions on the left can always be decomposed.
        cases h5
        case inl h18 =>
          -- Conjunctions on the left can always be decomposed.
          let h19 := h3.left
          let h20 := h3.right
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h7
        case inr h21 =>
          -- Conjunctions on the left can always be decomposed.
          let h22 := h3.left
          let h23 := h3.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h21
    case inr h24 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h25 =>
        -- Conjunctions on the left can always be decomposed.
        let h26 := h3.left
        let h27 := h3.right
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h7
      case inr h28 =>
        -- Conjunctions on the left can always be decomposed.
        let h29 := h3.left
        let h30 := h3.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h28
  case inr h31 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h32 =>
      -- Conjunctions on the left can always be decomposed.
      let h33 := h3.left
      let h34 := h3.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h35 =>
      -- Conjunctions on the left can always be decomposed.
      let h36 := h3.left
      let h37 := h3.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h35



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_643871547887671439637571929715 : ((((p5 ∧ (False ∨ ((p1 ∨ (p1 ∨ ((p5 ∧ True) ∨ (True → ((p1 ∧ (((p4 → False) ∨ (p2 → p4)) → p4)) ∧ True))))) → p4))) → False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51223206947859815242064020550 : (((((p2 ∧ p4) → ((p2 ∨ False) ∨ False)) → (p2 ∨ (p3 ∧ ((p3 ∨ p4) → (True ∧ True))))) ∨ (p4 ∨ ((p5 ∨ p4) → (False → False)))) ∨ p2) := by
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
theorem thm_5_vars_116698233786523658031111070305 : (((False ∧ p3) ∨ (((p1 ∨ (((p3 → p1) ∧ ((p4 ∨ (False → (p4 ∨ p5))) → (p4 → p3))) → p3)) ∨ p5) ∨ (True ∧ True))) ∨ (p4 ∧ p2)) := by
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
theorem thm_5_vars_116995576440441616068420582484 : (((True ∨ p3) → ((p2 ∧ (p2 ∨ ((p4 → ((False ∧ (True ∨ p4)) ∧ p5)) ∧ ((p3 → (p3 ∧ p5)) ∨ (p4 ∨ True))))) ∨ False)) ∨ (False → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_694207852330486258061226397146 : ((((((p3 ∨ p3) → (p4 → False)) ∧ (p1 → (((p4 ∨ p1) ∨ p4) → p3))) ∨ (((((p2 ∧ True) ∨ p3) → False) → True) → (True ∨ False))) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_654143915325151774849984279335 : ((((((False ∨ (((p5 ∧ (p3 ∨ ((False → (p4 ∨ p2)) ∨ (p3 ∧ (True ∨ p4))))) → (p4 ∧ p1)) ∧ False)) ∧ True) ∨ p1) ∨ (False ∨ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340761224285315670975562081274 : (p2 → (((p1 ∨ ((((False ∨ ((False ∧ False) → p3)) → (p1 → p1)) → p1) → (p3 ∨ (True → (False ∨ ((p4 ∨ False) ∨ p1)))))) ∨ p5) ∨ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : ((False ∨ ((False ∧ False) → p3)) → (p1 → p1)) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- Implications on the right can always be decomposed.
    intro h6
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- False on the left can always be used.
      apply False.elim h7
    case inr h8 =>
      -- One of the premise coincides with the conclusion.
      exact h6
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h9 := h2 h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179147082254642047795448254999 : ((p2 ∧ ((((False → (p3 ∨ False)) → p4) ∧ (p4 ∧ (p3 ∨ p1))) ∧ True)) ∨ (p5 → ((p2 → (p1 ∧ True)) ∨ (True ∨ (p3 ∨ (True ∧ p5)))))) := by
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
theorem thm_5_vars_62932944956253436852731426959 : ((p4 ∧ (p2 ∧ (((p1 ∨ p5) ∧ True) → ((True ∧ (((True ∧ (p2 → False)) ∧ ((p4 ∨ (p1 ∧ False)) ∧ False)) ∨ (p5 ∨ p1))) ∨ p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315780060633393521063894900061 : (p3 ∨ ((p3 ∧ p2) → ((p1 ∨ ((True → (False ∨ (p3 ∧ ((p3 ∨ p3) → p2)))) ∨ (p1 ∨ p4))) → (((True ∨ p5) → p5) ∨ (p5 → p2))))) := by
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
    -- Implications on the right can always be decomposed.
    intro h6
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h1.left
      let h10 := h1.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h11
      -- One of the premise coincides with the conclusion.
      exact h10
    case inr h12 =>
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- Conjunctions on the left can always be decomposed.
        let h14 := h1.left
        let h15 := h1.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h16
        -- One of the premise coincides with the conclusion.
        exact h15
      case inr h17 =>
        -- Conjunctions on the left can always be decomposed.
        let h18 := h1.left
        let h19 := h1.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h20
        -- One of the premise coincides with the conclusion.
        exact h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51614474006665666746607735855 : (((((((p3 ∨ ((False ∧ (p2 ∧ p5)) ∨ p3)) ∧ p1) ∨ p1) ∧ (p2 ∧ p2)) ∧ p1) ∧ (p4 → ((False ∧ ((p3 ∧ p1) ∧ p3)) ∨ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112308849761206503179667530810 : (((p2 → (((p1 ∧ (p3 → p2)) → (p3 → ((p4 ∨ p5) ∨ ((True ∧ (p2 → (p2 → p3))) ∧ True)))) → (p2 ∧ p4))) ∨ p2) ∨ (p3 → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_648693942579611233761639503915 : ((((((True ∨ p2) → (p4 ∨ (p3 → (((p5 ∨ ((((p3 → p1) ∨ False) ∧ p1) ∧ True)) → (True → p4)) ∨ p5)))) ∨ True) ∧ (p2 → True)) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164604646079442897748152932166 : (((False ∧ (((False ∧ p3) ∨ (((p3 → ((True ∨ p2) ∧ False)) → p1) → p4)) ∨ p4)) ∧ p2) ∨ (True ∨ (p2 ∨ ((p5 ∨ p5) → (p3 → p1))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_327847051725068740340643411797 : (True → (((p2 ∨ (((False → (p5 ∧ False)) → (True ∧ p3)) ∨ p5)) ∨ ((True ∨ p2) → ((p2 → ((p2 ∧ p4) ∨ p2)) ∧ p1))) ∨ (p1 → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_670035549299076698743660130329 : (((((((False → (p5 → p2)) ∧ p2) → (p5 → p1)) ∨ ((p1 → p2) ∧ ((p4 ∧ (True ∧ (p2 ∨ p2))) ∧ p2))) ∨ (True ∨ (p4 ∧ p3))) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_166281369055067785273979844629 : ((p4 ∧ ((True ∧ ((p5 ∨ ((False → (p5 ∨ (p1 ∧ (p2 → p2)))) → False)) ∨ True)) ∨ p5)) ∨ (p3 → (p2 ∨ ((p5 ∧ (p2 ∧ p1)) → p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_615304187306543401981644797397 : (((((((p2 ∨ (((p3 ∧ ((False ∨ p4) ∨ (p3 → p1))) ∨ p2) → p2)) ∧ p5) → p4) ∨ (True ∧ ((p2 → (False ∧ p3)) ∨ p1))) ∨ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57004260903753180398983411215 : (((True → (p5 ∨ p1)) ∧ ((((False ∨ (p5 ∧ True)) ∨ p3) ∨ (False ∧ ((p3 ∧ p4) ∨ p1))) ∨ ((p2 → (True ∨ (p4 ∨ p3))) ∨ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_650215139507679707375416715363 : ((((((p2 → (p2 → p3)) ∧ (((((True ∧ p4) ∨ p1) ∨ p1) → p5) → (p2 ∨ p2))) ∨ (((True → p4) ∨ True) → True)) ∧ (p3 ∨ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_658970327258337852461030059887 : ((((p1 → (((p1 → (((p1 ∧ p4) ∧ (((p1 → (p1 ∨ p3)) → (p2 → (True ∧ False))) ∧ p4)) ∨ p3)) ∧ p3) ∨ True)) ∨ (False → False)) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184397641567062705426660509885 : (((p5 → (False → ((((p4 → p1) ∧ True) ∧ p2) ∧ p1))) → p4) ∨ ((False → (((p3 → (p3 ∨ p4)) ∨ (p1 ∨ False)) → p4)) ∨ (False ∧ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- False on the left can always be used.
    apply False.elim h1
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- False on the left can always be used.
      apply False.elim h1
    case inr h6 =>
      -- False on the left can always be used.
      apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135314317778182174328178145681 : ((((p1 ∧ (p1 → (((p3 → (p3 ∨ p2)) ∧ (p1 ∧ (p3 ∨ False))) ∧ p3))) ∧ (False ∧ p4)) ∧ ((True → p2) ∨ p1)) ∨ (p4 ∨ (False → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_654043837674542456027599664497 : (((((p4 ∨ (p5 → ((p4 ∨ True) ∧ (((((p3 → p1) ∧ (p2 → (p2 ∧ p1))) ∨ (p2 → p2)) → False) ∨ p5)))) ∧ True) ∨ (p5 ∨ False)) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148685768166974125727646229379 : ((((False ∧ p3) ∨ ((p5 → (False ∧ True)) ∨ p4)) ∨ (p4 ∨ ((p1 ∧ p3) ∨ ((p5 ∧ p1) ∧ (p3 ∧ False))))) ∨ (True ∧ (p1 → (True → p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179075622665698086460018979708 : ((True ∧ ((p3 ∧ p4) ∧ ((p3 ∧ ((False ∨ (p3 ∧ False)) ∧ False)) ∧ p2))) ∨ ((False ∨ (p3 → (((p1 ∨ p2) ∧ (p2 ∨ p3)) → p4))) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116450644959729341295113947742 : (((True ∧ False) ∧ (((p1 ∧ p5) ∨ ((((((p2 → p4) ∧ p3) ∧ p3) ∨ (p2 ∨ (True ∧ False))) ∧ (p1 ∧ p4)) ∨ p2)) ∧ p1)) ∨ (p4 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_78717845479812354626526970642 : ((((p3 → (p2 ∨ ((p2 ∧ p5) ∨ (p3 ∨ ((True → p2) → (p3 ∨ True)))))) → ((p2 → True) → ((p1 ∧ p2) ∧ False))) ∧ (False → True)) → p2) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (p3 → (p2 ∨ ((p2 ∧ p5) ∨ (p3 ∨ ((True → p2) → (p3 ∨ True)))))) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h4
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h7 : (p2 → True) := by
    -- Implications on the right can always be decomposed.
    intro h8
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h9 := h6 h7
  -- We need to get the right conjuct of h9 based on <expert-advice>.
  let h10 := h9.right
  -- False on the left can always be used.
  apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157776646193822033525044789536 : ((((p3 ∧ ((p1 ∨ ((False ∧ True) ∨ True)) ∧ (p1 ∨ p5))) ∨ p2) ∨ (True ∨ (p2 ∨ (p1 → False)))) ∨ (p4 ∧ (False ∧ (p3 ∧ (False ∧ False))))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168893569628285850163099476043 : ((p5 ∨ ((((((False ∧ ((p5 → False) ∧ (p1 → False))) ∨ True) → p5) ∨ False) ∧ p1) ∨ p4)) → (p5 ∨ (p2 ∨ ((False ∨ False) ∨ (p5 ∨ p4))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h7 =>
        -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
        have h8 : ((False ∧ ((p5 → False) ∧ (p1 → False))) ∨ True) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h7, we can now drive its conclusion.
        let h9 := h7 h8
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h9
      case inr h10 =>
        -- False on the left can always be used.
        apply False.elim h10
    case inr h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_694047490892390145864481307879 : ((((((p2 ∨ ((p4 → p5) → p5)) ∨ (p5 ∨ p4)) ∧ (True ∨ (p4 ∧ p2))) ∨ ((((p2 ∨ ((p1 ∨ True) → p1)) → p4) ∨ p4) ∨ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_327201903694949292804955402942 : (True → ((p5 ∨ ((p4 ∧ (((True → ((False ∨ False) ∧ p1)) ∨ True) ∧ (((p4 → True) ∧ p5) → p4))) ∨ ((p2 ∧ p3) ∧ (p2 ∨ p4)))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_23748171825995824695836134521 : ((((p5 → p2) ∧ (False ∨ False)) ∨ (((((p1 → ((True ∧ True) → p4)) → (p3 → p4)) → (p4 → p3)) ∧ ((p4 ∧ p2) ∨ p5)) ∨ True)) ∧ True) := by
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
theorem thm_5_vars_719890160886100518268484356883 : ((((p4 → (True ∧ (p2 → False))) ∨ ((p2 → (p3 → ((False → (((p4 ∨ (False → p4)) ∧ (p2 ∧ p5)) → p4)) → p1))) → (p4 ∧ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118153760756434229336181048328 : ((False ∨ (((False ∨ (False ∧ (True → p5))) → True) → (p5 → (((p1 ∨ ((p1 → p4) ∧ (p1 → (p2 ∧ p3)))) ∨ p2) ∨ True)))) ∨ (p1 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303936960577067724659997142395 : (p1 ∨ (((((p5 ∧ False) → p2) → (p4 ∧ False)) ∧ ((True ∨ ((p2 → p1) ∨ (p1 ∨ (((p1 → p3) → False) ∧ (True ∧ p2))))) ∧ p1)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_132104876920165981433143182846 : (((p3 → p1) → ((p3 ∨ ((False → p3) → p3)) ∨ (p3 → (p1 ∨ (p1 ∧ (p2 → ((p1 → (p5 ∨ True)) → p5))))))) ∧ ((p3 ∧ p1) → p1)) := by
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
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : p3 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- One of the premise coincides with the conclusion.
  exact h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321243747378951470363198830649 : (p4 ∨ (p4 ∨ ((((True ∨ ((((p5 ∨ (True → (p4 → (True ∧ p4)))) ∧ p2) ∧ p4) ∨ p2)) → p5) → ((False → p1) → p1)) ∨ (p4 → True)))) := by
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
theorem thm_5_vars_66159991771630373070074669794 : ((p5 ∨ (((((p2 ∧ p5) → p5) ∧ ((p3 ∧ p2) ∨ (((p5 ∧ p2) ∧ p4) ∧ p1))) ∨ (True ∨ (p1 → p5))) ∧ (True ∨ (p2 ∧ p1)))) ∨ p3) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208050991957370389015696902846 : (((True ∨ (p5 → p4)) ∨ (p2 ∨ p3)) → ((((((p5 → False) ∧ (p1 → p1)) ∨ False) ∨ ((True ∧ p1) → True)) ∨ p2) ∨ ((False ∨ p1) ∧ p3))) := by
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h4
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h9 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- True on the right can always be proven directly.
      apply True.intro



