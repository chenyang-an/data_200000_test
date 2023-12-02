variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_705793512003138652475763811633 : ((((((True ∨ p5) ∧ (p5 ∧ p2)) → (False ∧ p2)) ∧ (((((p5 ∧ (p4 ∨ p3)) ∨ p2) ∧ (p2 → ((p4 → False) → p4))) ∨ p2) → p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_720250386760663269986719617723 : (((((p4 → (True → p1)) ∧ p1) → ((((((p3 ∨ p1) ∨ p2) ∨ p4) ∧ False) ∨ ((((p3 ∨ True) → p5) ∨ p5) ∧ (p1 → p1))) → p5)) ∨ p4) ∧ True) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Disjunctions on the left can always be decomposed.
        cases h7
        case inl h8 =>
          -- False on the left can always be used.
          apply False.elim h5
        case inr h9 =>
          -- False on the left can always be used.
          apply False.elim h5
      case inr h10 =>
        -- False on the left can always be used.
        apply False.elim h5
    case inr h11 =>
      -- False on the left can always be used.
      apply False.elim h5
  case inr h12 =>
    -- Conjunctions on the left can always be decomposed.
    let h13 := h12.left
    let h14 := h12.right
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h15 =>
      -- Conjunctions on the left can always be decomposed.
      let h16 := h1.left
      let h17 := h1.right
      -- We want to use the implication h15 based on <expert-advice>. So we show its premise.
      have h18 : (p3 ∨ True) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h15, we can now drive its conclusion.
      let h19 := h15 h18
      -- One of the premise coincides with the conclusion.
      exact h19
    case inr h20 =>
      -- Conjunctions on the left can always be decomposed.
      let h21 := h1.left
      let h22 := h1.right
      -- One of the premise coincides with the conclusion.
      exact h20
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135635978728511110445718271191 : ((((((p4 ∨ ((p1 ∧ (p1 → p4)) → p4)) ∧ (p4 ∧ False)) ∨ (p5 ∧ p2)) → p2) → ((p2 → p3) ∨ (p2 ∧ p4))) ∨ (p1 ∨ (p3 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54770601270819288698927555297 : (((True ∧ ((((p1 → p4) ∨ p4) ∧ False) → p4)) → ((p3 → p1) ∨ ((p3 → (p3 ∧ (((p1 ∧ False) ∨ p2) ∧ (p1 ∧ p5)))) ∧ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57031983375398605610899804312 : (((p2 → (p2 ∧ False)) ∧ (((((p5 → (p3 ∧ True)) ∧ ((False → p2) ∧ (p3 ∧ ((True ∨ p2) ∧ p5)))) ∧ p4) ∧ (False ∨ p4)) → p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159897351966480329253154138097 : ((((((((False → p3) ∧ p2) ∨ (p5 → (p4 → p5))) ∨ True) ∨ ((p2 ∧ p1) ∨ p1)) ∨ True) → False) → (((p1 ∧ False) ∧ (p5 ∧ p1)) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((((((False → p3) ∧ p2) ∨ (p5 → (p4 → p5))) ∨ True) ∨ ((p2 ∧ p1) ∨ p1)) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116273379453813863197696484341 : (((p5 ∧ (p5 ∨ True)) ∨ (p2 ∨ ((((((True ∨ (p5 → p2)) ∨ (p5 → p2)) ∧ p2) ∧ p1) ∧ (p4 ∧ p4)) ∨ (True → p2)))) ∨ (p1 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118727572365013873055288125300 : ((p5 ∨ (((p4 ∨ (((p5 ∧ True) → (((p4 ∧ p1) → False) ∧ (p1 ∧ True))) ∨ p3)) ∧ p3) ∨ (True ∨ (False ∨ (p1 → False))))) ∨ (p3 ∨ p3)) := by
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
theorem thm_5_vars_301414651523994195017032808778 : (False ∨ (((p5 ∧ (p5 ∧ p4)) ∨ p2) → ((((False ∧ p2) → p4) → (False ∨ (((p2 ∨ p3) ∨ p2) ∨ (((True → p1) ∨ p5) → True)))) ∨ p3))) := by
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
    let h5 := h4.left
    let h6 := h4.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h7
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h9 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h10
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_599243703462904043588317667842 : (((((p5 → p4) ∧ ((p3 ∧ (p2 ∧ (True → p5))) ∨ ((p4 → ((p2 ∧ p3) → p3)) → (p3 ∧ (((p2 → p2) → p1) ∧ p1))))) ∧ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156850818065159738195864415524 : (((p5 → ((((((p3 ∧ p2) ∨ p4) ∧ False) ∨ p5) ∨ (p4 ∨ (p5 → p2))) → (p4 ∧ p2))) ∧ p2) ∨ (p2 → (((False ∧ p1) ∨ False) → p2))) := by
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
    let h4 := h3.left
    let h5 := h3.right
    -- False on the left can always be used.
    apply False.elim h4
  case inr h6 =>
    -- False on the left can always be used.
    apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_87459873744432744992274525518 : (((p4 → ((p2 ∧ (p5 ∧ p5)) ∧ False)) ∧ (((False ∨ (((p4 → p4) ∧ (True ∧ p3)) ∨ (False ∨ (True ∨ False)))) → (p4 ∨ p4)) ∧ p5)) → p4) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h6 : (False ∨ (((p4 → p4) ∧ (True ∧ p3)) ∨ (False ∨ (True ∨ False)))) := by
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
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h7 := h4 h6
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- One of the premise coincides with the conclusion.
    exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_792786109706672010682234874994 : (((True → (((p1 ∧ True) → p2) ∧ (((((False ∧ p1) ∨ p3) → ((p4 ∨ True) ∧ (p2 ∧ p4))) → (p1 → (p3 ∨ p4))) → (p4 ∧ True)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_242326342098807785212396034835 : ((p2 → p2) ∧ (((p5 → (p2 → (False → True))) ∨ ((True ∧ (p4 ∨ p3)) → ((p4 ∨ p1) → p1))) → ((True ∧ ((False → p4) → False)) → p4))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h6 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h7 : (False → p4) := by
      -- Implications on the right can always be decomposed.
      intro h8
      -- False on the left can always be used.
      apply False.elim h8
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h9 := h5 h7
    -- False on the left can always be used.
    apply False.elim h9
  case inr h10 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h11 : (False → p4) := by
      -- Implications on the right can always be decomposed.
      intro h12
      -- False on the left can always be used.
      apply False.elim h12
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h13 := h5 h11
    -- False on the left can always be used.
    apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65053800620044615001259450793 : ((p2 ∨ (p1 ∧ (p4 ∧ (((p1 → (p5 ∧ p2)) ∨ p1) ∧ (((p2 → False) ∨ p3) ∧ (p4 ∧ (True ∧ (((p3 → p5) ∧ False) ∨ p4)))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65130645897369411641317039291 : ((p2 ∨ (p1 → (((p1 ∧ (p2 ∧ p5)) ∧ (p3 → (False → (p2 ∧ ((True ∧ p4) ∨ p1))))) → (False ∧ ((p4 ∨ False) → (p3 → p2)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_766060821344415156417004948500 : (((p4 ∧ ((p5 ∧ (p1 ∧ p1)) ∨ ((p3 ∨ (((((True ∨ True) ∨ p2) → p2) ∨ (True → (p1 → p2))) → (True ∨ p5))) ∧ (p3 ∧ False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_102702294567139598270976248865 : (((((((p5 ∧ p3) → p5) → ((p5 → (True ∨ (p4 ∨ p2))) → (p3 → (p5 ∧ p4)))) ∨ ((False → p5) ∧ p3)) ∨ p4) ∨ True) ∧ (False → p1)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152975642001669357010838040790 : ((p1 ∧ ((((False ∨ p4) ∨ ((p3 → p5) ∧ (False ∧ p5))) ∨ (p1 ∨ (p2 → True))) → (False ∧ (False → p3)))) → ((p5 ∧ (p1 ∨ p2)) ∧ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : (((False ∨ p4) ∨ ((p3 → p5) ∧ (False ∧ p5))) ∨ (p1 ∨ (p2 → True))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- False on the left can always be used.
  apply False.elim h6
  -- Conjunctions on the left can always be decomposed.
  let h7 := h1.left
  let h8 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h7
  -- Conjunctions on the left can always be decomposed.
  let h9 := h1.left
  let h10 := h1.right
  -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
  have h11 : (((False ∨ p4) ∨ ((p3 → p5) ∧ (False ∧ p5))) ∨ (p1 ∨ (p2 → True))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h9
  -- We have shown the premise of h10, we can now drive its conclusion.
  let h12 := h10 h11
  -- We need to get the left conjuct of h12 based on <expert-advice>.
  let h13 := h12.left
  -- False on the left can always be used.
  apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313962956946900999209216016678 : (p3 ∨ (((((((p2 ∧ True) ∧ ((((p4 → p4) → p1) ∨ p4) → False)) → (p4 ∧ False)) → p4) ∨ p1) ∨ ((p1 ∧ p1) ∧ p1)) ∨ (p2 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_398297195976611019296926421781 : ((((p5 ∨ ((((((p1 ∨ False) ∨ (((p4 ∧ False) ∧ True) ∨ p2)) → ((p4 ∨ p5) ∨ (p3 → p1))) → False) ∨ True) ∨ (p2 ∧ p4))) ∨ p5) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309931899930719297701074554208 : (p2 ∨ (((p3 → False) ∧ (True ∧ ((p3 ∧ ((p3 → (p2 ∨ (True → False))) ∨ (p4 → False))) ∨ False))) ∨ ((p3 ∨ (p4 ∨ p4)) ∨ (True → True)))) := by
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
theorem thm_5_vars_174856205768072427244023563276 : (((p3 ∨ p4) ∨ (p3 ∧ ((p4 → (True ∧ (p5 ∨ p3))) → (p5 → (False ∨ p5))))) → ((p1 → (((p1 ∧ (p2 ∧ p5)) → p2) → False)) ∨ True)) := by
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
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149460271428252887747170006603 : ((False ∧ ((p5 ∨ (((p1 → False) → (p5 → p4)) ∧ (p2 ∧ p1))) ∨ (p5 → (((p1 ∧ True) ∧ p3) ∨ p3)))) ∨ (((True → False) → p2) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_227721252850458498411751422669 : ((p1 ∧ (p5 ∧ False)) ∨ (((p5 ∨ (((p1 ∨ p4) ∧ ((p4 ∨ (p5 ∧ p1)) ∧ (False → False))) ∨ ((p3 ∧ (p5 ∧ True)) → p3))) ∨ True) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53096416021606827374633056054 : (((p3 ∨ (p2 ∧ (p3 ∨ ((True ∧ (p1 ∨ p3)) → (False ∧ p3))))) ∧ ((True ∨ p5) ∨ ((p3 ∨ (((p3 ∨ True) ∨ False) ∨ p2)) ∨ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200803075168955721283224455566 : ((p5 ∧ (((p2 ∨ (True → False)) ∧ p2) → p2)) → (p3 → ((p3 → (p2 ∧ (p1 ∧ (((p1 → p2) ∨ p3) ∨ ((p1 → p1) → p5))))) → p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h6 : p3 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h7 := h3 h6
  -- We need to get the left conjuct of h7 based on <expert-advice>.
  let h8 := h7.left
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40567212067608405970061871187 : ((((p4 → ((((p5 ∨ p2) → ((p3 ∧ p5) ∨ p1)) → (p5 ∧ False)) → (((p2 → (p1 → (p3 ∧ True))) ∨ False) → False))) ∨ False) ∨ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_806669837416056964473113927433 : (((p4 → ((False → ((True ∧ p4) → (p5 ∨ ((((True → p1) ∨ p2) ∧ (True → ((False ∨ False) ∨ ((p4 ∧ p1) ∨ True)))) ∨ p2)))) → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198896774863636552305005207529 : ((p3 → (((p3 ∧ (p1 ∧ p5)) ∧ p4) → False)) ∨ (p3 → ((((p5 → ((True → (p4 → p1)) ∧ p5)) ∧ (p4 → (p3 → p4))) → p1) ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_648916716387469279569060066595 : ((((((((((p3 → False) ∨ False) → ((True → (p3 ∧ (False ∨ (p3 → p2)))) ∧ (True → False))) ∧ p1) → p4) ∨ p2) → p3) ∧ (False ∧ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_766075496635068851869156421448 : (((p4 ∧ ((p5 → (p4 ∧ False)) ∨ (((p3 → ((p5 ∨ (False → (p4 → (((False ∧ False) ∧ p1) → p2)))) → (p1 → p5))) → p4) ∨ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42823118866549259651804787092 : (((p1 → ((p1 ∨ (p5 → (False ∨ p3))) ∧ (p4 ∨ (p2 ∧ (((p2 ∧ p4) ∧ (((False → True) ∨ (p5 → False)) → p4)) ∧ p3))))) ∨ True) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158299683301339682172266587181 : ((((False ∨ True) → p2) → ((((False → (False ∧ (p2 ∨ (p2 → p4)))) → p5) ∧ (p1 ∨ p2)) → p1)) ∨ (((p3 → True) ∨ (p5 ∨ p5)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_162280166916461466850341618345 : (((p2 ∨ ((p5 → p1) ∨ (False → ((p3 ∨ (p3 ∧ (p4 ∨ (True ∧ True)))) ∧ False)))) ∧ True) ∧ ((p4 ∧ ((p3 → p2) → (p2 ∨ p3))) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147594064767370475878316997488 : ((((((p1 ∧ p2) ∨ (p1 ∨ ((p3 ∧ False) → (p5 ∨ (p2 ∧ ((p2 → p4) ∧ p5)))))) → p4) ∨ True) → p1) ∨ (p1 → (p4 → (p3 ∨ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_617179224059362355129046896770 : ((((((p5 → (p3 ∧ ((p4 ∨ True) ∧ False))) → p1) ∨ (p3 ∨ ((p1 ∨ (p2 ∧ (p5 → (p3 → p2)))) ∧ ((True ∨ p3) ∧ True)))) ∨ True) ∨ False) ∧ True) := by
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
theorem thm_5_vars_125023581279175512428205730245 : ((((p2 → p1) ∨ p1) ∧ (((p4 ∨ ((p2 → p2) → (p4 → (p2 → False)))) ∧ ((p1 ∧ p3) ∧ True)) ∧ ((p2 → True) ∧ True))) → (p3 → p1)) := by
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
    let h6 := h4.left
    let h7 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h6.left
    let h9 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h9.left
      let h12 := h9.right
      -- Conjunctions on the left can always be decomposed.
      let h13 := h11.left
      let h14 := h11.right
      -- Conjunctions on the left can always be decomposed.
      let h15 := h7.left
      let h16 := h7.right
      -- One of the premise coincides with the conclusion.
      exact h13
    case inr h17 =>
      -- Conjunctions on the left can always be decomposed.
      let h18 := h9.left
      let h19 := h9.right
      -- Conjunctions on the left can always be decomposed.
      let h20 := h18.left
      let h21 := h18.right
      -- Conjunctions on the left can always be decomposed.
      let h22 := h7.left
      let h23 := h7.right
      -- One of the premise coincides with the conclusion.
      exact h20
  case inr h24 =>
    -- Conjunctions on the left can always be decomposed.
    let h25 := h4.left
    let h26 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h27 := h25.left
    let h28 := h25.right
    -- Disjunctions on the left can always be decomposed.
    cases h27
    case inl h29 =>
      -- Conjunctions on the left can always be decomposed.
      let h30 := h28.left
      let h31 := h28.right
      -- Conjunctions on the left can always be decomposed.
      let h32 := h30.left
      let h33 := h30.right
      -- Conjunctions on the left can always be decomposed.
      let h34 := h26.left
      let h35 := h26.right
      -- One of the premise coincides with the conclusion.
      exact h32
    case inr h36 =>
      -- Conjunctions on the left can always be decomposed.
      let h37 := h28.left
      let h38 := h28.right
      -- Conjunctions on the left can always be decomposed.
      let h39 := h37.left
      let h40 := h37.right
      -- Conjunctions on the left can always be decomposed.
      let h41 := h26.left
      let h42 := h26.right
      -- One of the premise coincides with the conclusion.
      exact h39



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45278617477816595764288573750 : (((p2 ∧ ((True ∨ ((((p1 ∧ False) ∧ p4) ∨ ((p1 ∨ p5) → p4)) ∨ ((((p1 → p2) → False) → p4) → p2))) → (p1 → p3))) → p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347385469252155543505991556897 : (p3 → (((p4 ∨ p2) → (((p1 → p1) ∨ True) → p1)) ∨ (((p5 ∨ (((p5 ∨ True) ∨ True) ∨ (((p2 → p1) → p1) ∨ p1))) → p5) → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_718757099135497968462233572038 : (((((p2 ∧ False) ∨ (p2 ∨ False)) ∨ (p5 ∨ (True ∨ (p4 ∨ (((p5 → ((p5 ∧ ((p5 ∨ p3) → p4)) ∨ False)) ∧ p1) → (p5 → False)))))) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_134378869985917118645686128204 : (((p3 ∨ (p3 ∨ ((((False ∧ ((p2 ∧ p4) ∧ (p5 ∧ p5))) ∨ ((False ∨ p2) ∧ p5)) ∨ p1) ∨ (p4 ∨ p5)))) ∨ p4) ∨ (p4 → (False ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246462145657415335902845953957 : ((p5 ∧ False) ∨ ((((False → (p2 → p2)) ∨ p2) → p5) ∨ ((p3 ∧ False) → (((((p3 ∨ p2) ∨ p2) ∧ (False → p3)) → (p4 → p1)) ∧ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h1.left
      let h9 := h1.right
      -- False on the left can always be used.
      apply False.elim h9
    case inr h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h1.left
      let h12 := h1.right
      -- False on the left can always be used.
      apply False.elim h12
  case inr h13 =>
    -- Conjunctions on the left can always be decomposed.
    let h14 := h1.left
    let h15 := h1.right
    -- False on the left can always be used.
    apply False.elim h15
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40206038758389497596638254051 : (((((False ∧ p2) ∨ ((p3 → ((False ∧ ((((p5 ∨ (p3 ∧ p4)) ∧ False) ∧ p5) → p3)) ∨ p5)) ∨ ((p5 ∧ p3) ∧ True))) ∧ p4) ∨ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138139757689358434063455540921 : ((p1 → (((((p5 → (p4 ∧ p4)) ∧ ((p5 → p3) ∨ ((False → True) ∨ True))) → ((p1 ∧ p5) → False)) ∨ p1) ∧ True)) ∨ (p1 ∧ (p1 ∨ p4))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197483032385220566988759366912 : ((((p3 ∨ p1) → (False ∨ p2)) ∧ (True ∧ p3)) ∨ ((True → (p4 → ((p3 → p3) ∧ p5))) → (((p4 → p2) → p4) ∨ ((p5 → True) ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340924126171351031180759954473 : (p2 → ((((((False ∧ p1) → p3) ∧ p2) → p5) ∨ (p4 → ((((False ∨ (p1 ∨ False)) ∨ p3) ∨ False) ∨ ((p3 → p2) → (p2 ∨ p3))))) ∨ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309919383136574638710960202216 : (p2 ∨ (((True → (((p2 ∨ (p2 ∨ (p3 → p2))) ∧ (p2 ∨ p5)) ∨ (p2 → True))) ∧ (p5 → p1)) ∨ (p5 → ((p3 ∧ p3) ∨ (True ∨ p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_178682887732635269695870265571 : (((((True ∨ p2) ∨ p1) ∧ p1) ∨ (p5 → (((p1 ∧ p5) ∧ False) ∧ p3))) ∨ (((((p4 ∧ (p2 ∧ p4)) ∨ False) ∨ p4) ∨ (True ∨ p1)) ∨ p1)) := by
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
theorem thm_5_vars_174702963091344302130537944958 : (((p2 ∧ (True → p1)) ∨ ((True ∨ ((False ∨ ((p1 ∧ p2) ∧ p4)) ∨ p2)) ∨ False)) → ((p4 → p4) → (((True → (p3 ∨ p3)) ∨ p4) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h9 =>
        -- Disjunctions on the left can always be decomposed.
        cases h9
        case inl h10 =>
          -- Disjunctions on the left can always be decomposed.
          cases h10
          case inl h11 =>
            -- False on the left can always be used.
            apply False.elim h11
          case inr h12 =>
            -- Conjunctions on the left can always be decomposed.
            let h13 := h12.left
            let h14 := h12.right
            -- Conjunctions on the left can always be decomposed.
            let h15 := h13.left
            let h16 := h13.right
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
      -- False on the left can always be used.
      apply False.elim h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321061475948646607010891330176 : (p4 ∨ (p1 ∨ ((((p2 → (((p2 ∧ (p2 ∨ p5)) ∧ ((False ∧ p5) → (p1 ∧ p3))) ∧ False)) → (False ∧ False)) → (False ∨ p2)) ∨ (p4 → p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165774007658347069809989695075 : ((((p2 → (p2 ∧ p1)) → p3) → ((((False → p4) ∨ True) ∨ (True → p3)) → (p3 ∧ p3))) ∨ (p4 ∨ (True ∨ (p5 → (p3 ∨ (False → p2)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134497498043192051955609717411 : (((((p1 → (((p4 ∨ (((p3 → p2) ∨ True) ∧ False)) → (p5 → p3)) ∧ p2)) → ((True ∨ True) ∧ p1)) ∨ p3) → p1) ∨ ((False → False) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67954274833082343267506284445 : ((p2 → (((p5 ∨ (p5 ∨ p3)) ∨ p3) ∨ ((False ∨ (((False → ((p4 ∧ p3) ∧ p4)) → p5) ∧ False)) ∨ ((p2 ∧ p4) → (p4 → p2))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_624185386727141814062492593036 : ((((p2 ∨ (p4 → ((p4 ∧ p4) → (((False ∧ (((p5 → (p2 → True)) → ((p4 → False) ∨ p2)) → (p3 ∨ False))) ∧ True) ∧ p1)))) ∨ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231323273432798351162837438190 : (((True → p1) ∨ p4) → (((True ∧ ((((((True → p1) → ((False → False) → p5)) ∨ False) → p3) → p4) ∧ (p3 ∨ p2))) ∨ (p3 ∧ False)) ∨ True)) := by
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
theorem thm_5_vars_68171891646629035273802962550 : ((p3 → ((((False ∧ (((True ∨ True) ∧ False) ∨ ((((p5 ∧ (p5 ∨ p2)) ∧ p1) ∧ (p3 ∨ p3)) ∧ (True ∧ p5)))) ∨ p3) ∧ True) ∨ p4)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322405528885064270851900588135 : (p5 ∨ (((p4 ∨ (((p3 → p4) → (p4 ∨ p3)) ∨ ((True ∧ p4) → p4))) ∨ ((p4 ∨ p2) → ((p1 ∨ (p3 → (False ∨ True))) ∨ p2))) ∨ p3)) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_154901419989701752548780111485 : (((((((p4 ∨ (p5 → (p3 ∧ (False ∨ True)))) ∧ False) ∧ p2) ∨ p3) ∧ p3) ∨ ((p3 ∧ False) → p1)) ∧ (((p3 → False) ∨ (True ∨ p2)) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_216465845395873897878382462237 : ((p4 → (p1 → (p5 ∧ p3))) ∨ (((((p3 ∨ ((False → (p2 ∧ True)) ∨ True)) ∧ p4) → False) ∨ ((p2 ∨ (p1 ∧ (p1 → p5))) ∨ True)) ∨ p4)) := by
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
theorem thm_5_vars_148913661308503926002194260047 : ((((False → (p4 ∨ False)) ∧ p2) → (p1 ∨ ((((p5 → (p4 ∧ (False → (p2 ∨ False)))) ∧ p4) → p3) ∨ True))) ∨ (p5 ∨ (p4 ∧ (False ∨ p1)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_70569886964955660480333134971 : (((((p2 ∨ (p4 ∧ (((True ∧ p5) ∨ ((p3 ∨ (p1 ∧ p4)) ∧ p5)) → p2))) ∨ (False → (True ∨ p3))) → (False ∧ (True ∧ True))) ∧ True) → p5) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : ((p2 ∨ (p4 ∧ (((True ∧ p5) ∨ ((p3 ∨ (p1 ∧ p4)) ∧ p5)) → p2))) ∨ (False → (True ∨ p3))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- False on the left can always be used.
    apply False.elim h5
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h4
  -- We need to get the left conjuct of h6 based on <expert-advice>.
  let h7 := h6.left
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41940213841133687386894632266 : ((((True ∧ False) ∧ (((p5 ∨ (p5 ∨ p3)) ∧ p3) → ((False ∨ p5) ∨ (p3 → ((p5 ∧ (p5 → (p2 ∨ (True ∨ p5)))) → p4))))) ∨ True) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_755491868562330388194048164626 : (((p1 ∧ ((p4 ∧ ((((True → False) ∧ p4) ∧ (((p5 → p3) ∨ False) ∨ ((((True → (p4 ∨ p4)) ∨ p3) → False) ∧ True))) ∧ p5)) ∧ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309324832818583809964282153366 : (p2 ∨ ((((p3 → p3) ∧ ((True ∧ (p3 → True)) ∨ (False ∨ (p1 ∧ (((((p4 → p3) ∨ False) ∧ False) ∧ p3) ∧ p5))))) → p1) ∨ (False → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_627266570191514252979159768035 : ((((((p3 ∧ (False → ((((((((p2 → p4) ∨ (p1 ∧ p5)) → True) → (p2 ∨ True)) ∨ p5) ∨ True) ∨ p3) ∧ p1))) ∨ p1) ∧ True) → False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110726103430761696848113512390 : (((((p2 ∨ ((((((p4 ∧ False) → p2) ∧ (p5 ∧ True)) ∨ p2) ∨ p4) ∧ (True → True))) ∨ ((p1 ∧ p4) → p3)) ∧ False) ∧ p1) ∨ (False ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111016546101035819217192825538 : ((((True → (p1 ∧ (((False → (p1 → p4)) ∧ (False ∨ p3)) ∧ (False ∨ (p1 ∧ (True → p1)))))) ∨ (p4 ∨ (p4 ∧ False))) ∧ p5) ∨ (True ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_809752996445741290919251098880 : (((p5 → ((((((p5 ∧ p1) ∧ (p2 ∨ False)) → (p3 ∨ (p3 → p3))) → (p3 → (True → ((p4 → p5) → p1)))) ∨ True) ∨ (p5 → p2))) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_357513261516206574806330688534 : (p5 → (True ∧ ((True → ((((False ∨ p1) → True) ∨ True) ∧ False)) → ((False → ((((True ∧ (p2 ∧ (p5 ∨ p2))) ∨ False) ∧ False) → p5)) ∧ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- False on the left can always be used.
      apply False.elim h6
    case inr h13 =>
      -- False on the left can always be used.
      apply False.elim h6
  case inr h14 =>
    -- False on the left can always be used.
    apply False.elim h14
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h15 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h16 := h2 h15
  -- We need to get the right conjuct of h16 based on <expert-advice>.
  let h17 := h16.right
  -- False on the left can always be used.
  apply False.elim h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191478891792131671155107303210 : ((True ∧ (((False → (p2 ∧ p1)) → p4) ∨ (p2 → p3))) ∨ ((True → ((((p5 ∨ p1) → p4) → (p2 ∨ ((p3 ∨ p3) ∨ p3))) ∧ p5)) → p5)) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41599449057304201552220717926 : (((((p4 ∨ (p4 → ((p3 ∨ p3) ∨ p5))) ∨ p1) ∨ (((True ∨ p3) ∨ p3) ∧ ((False ∧ (p4 ∨ ((p2 ∨ True) → False))) → p4))) ∨ p4) ∨ p2) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_318726927907518387667497464082 : (p4 ∨ ((((p3 → p5) → (p4 ∧ True)) ∧ ((p3 ∧ (((p3 → (False → False)) → (p4 ∧ p5)) ∨ (p5 → p4))) → (p2 ∨ p4))) → (p5 → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_3392059278121222133878378338 : ((p2 → p5) → (((p4 ∨ (p1 ∨ p1)) → p4) ∨ ((p1 → (p4 → True)) → ((p3 ∨ (p2 → (p1 ∨ (p3 ∨ (False ∧ p3))))) → True)))) := by
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
theorem thm_5_vars_172390972189319937257164984533 : (((((p4 ∨ False) ∧ p4) → (p1 → p4)) → ((p4 ∨ (True → True)) ∧ (False ∧ p5))) ∨ (True ∧ ((True ∨ p5) ∨ ((True → p3) ∧ (p5 → p5))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_19548763563234637586210239926 : ((((((((p5 ∧ p2) → True) ∧ p4) ∧ (p3 → (p2 ∨ False))) → p5) ∨ (p3 → False)) ∨ (p4 → (((True ∨ False) → p4) ∨ (p3 ∧ False)))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h4 =>
    -- False on the left can always be used.
    apply False.elim h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190071400224641322201473617588 : (((((p2 ∧ p5) → (p2 → (p1 ∧ p1))) → p1) ∧ True) ∨ (((p1 → (p3 ∧ False)) ∧ p3) ∨ ((False → p5) → (p1 ∨ ((p3 ∧ p4) ∨ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117585578124765932110555839940 : ((p2 ∧ (False ∧ (p5 ∨ ((p1 ∨ (p1 → (p4 ∨ (p2 ∨ ((p3 → (True ∨ (False ∨ ((p3 ∧ p5) ∧ p2)))) ∧ True))))) → False)))) ∨ (False → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_739046608634932019629368466746 : ((((p3 ∧ p3) ∨ (True → ((p4 ∨ (p1 ∨ False)) ∧ ((p5 → (((((p3 ∧ True) ∨ p1) ∨ True) ∨ p2) ∧ True)) ∧ ((p5 ∧ p2) ∧ p4))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_893619914485147549099563321242 : (((((p1 → (p4 ∧ p5)) ∧ (True ∨ ((((False ∧ p3) ∧ False) → ((p4 → p4) ∨ ((True ∧ p4) → False))) ∧ True))) ∧ (p1 ∨ (p4 ∧ p2))) → p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    cases h3
    case inl h7 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h8 : p1 := by
        -- One of the premise coincides with the conclusion.
        exact h7
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h9 := h4 h8
      -- We need to get the left conjuct of h9 based on <expert-advice>.
      let h10 := h9.left
      -- One of the premise coincides with the conclusion.
      exact h10
    case inr h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- One of the premise coincides with the conclusion.
      exact h12
  case inr h14 =>
    -- Conjunctions on the left can always be decomposed.
    let h15 := h14.left
    let h16 := h14.right
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h17 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h18 : p1 := by
        -- One of the premise coincides with the conclusion.
        exact h17
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h19 := h4 h18
      -- We need to get the left conjuct of h19 based on <expert-advice>.
      let h20 := h19.left
      -- One of the premise coincides with the conclusion.
      exact h20
    case inr h21 =>
      -- Conjunctions on the left can always be decomposed.
      let h22 := h21.left
      let h23 := h21.right
      -- One of the premise coincides with the conclusion.
      exact h22
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_949713716998582925757430686176 : (((((False → p2) ∨ p5) ∧ (p2 ∧ (False ∨ (((False ∨ (p4 ∨ ((True → ((p5 ∨ p1) ∧ p5)) → p4))) → (p4 ∨ (p4 ∧ p4))) ∨ p2)))) → p2) ∧ True) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- False on the left can always be used.
      apply False.elim h7
    case inr h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- One of the premise coincides with the conclusion.
        exact h5
      case inr h10 =>
        -- One of the premise coincides with the conclusion.
        exact h10
  case inr h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h3.left
    let h13 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h14 =>
      -- False on the left can always be used.
      apply False.elim h14
    case inr h15 =>
      -- Disjunctions on the left can always be decomposed.
      cases h15
      case inl h16 =>
        -- One of the premise coincides with the conclusion.
        exact h12
      case inr h17 =>
        -- One of the premise coincides with the conclusion.
        exact h17
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171395811309047597392624925954 : (((((True ∨ p4) ∨ (p5 → (p4 ∨ p4))) → (False ∨ ((True ∧ True) ∨ False))) ∧ False) ∨ ((p1 ∨ (p4 → ((p1 → p3) → p4))) ∨ (p1 ∨ False))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49983115581515649743652032514 : ((((((p5 ∧ p4) ∨ (False → ((p1 → p4) ∨ (p5 → p4)))) → p1) ∨ (p4 → (p3 ∨ (p4 ∧ p2)))) ∧ (((p2 ∨ p2) ∨ False) ∧ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136692689366064984965412994136 : (((True ∧ p3) ∧ (p5 ∧ ((((p4 → ((p4 ∨ p4) ∨ p2)) → p4) ∧ p4) ∧ (((p4 ∨ p3) ∧ (p3 ∨ p5)) ∨ p4)))) ∨ (False → (p1 ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111897762639430846852642491411 : ((((p5 ∨ ((((((p4 ∧ p1) ∧ p3) ∧ p1) → p5) → p4) ∧ (p1 ∨ p3))) ∨ (p3 ∨ ((p4 → (p2 → p1)) → p3))) ∨ p1) ∨ (False → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198434820743079623524327331160 : ((p4 ∧ (True → ((True ∨ p2) ∧ (p5 ∧ True)))) ∨ (p3 ∨ ((p5 ∧ (p1 → p5)) → (((False ∧ (p4 ∨ ((p4 → p5) ∨ p1))) ∧ p1) ∨ p5)))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110713452734503119123911993116 : (((((((False → (p1 ∧ (False → (True → p1)))) ∨ ((p2 → p1) ∧ p3)) ∧ (((True → p5) ∧ p2) ∨ True)) → p3) ∧ p2) ∧ p5) ∨ (False → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_90469310868958730748177638762 : (((p1 ∧ p4) ∧ ((p5 ∧ (((p2 → True) → (False ∧ p1)) ∧ (False ∨ (((((p3 ∨ p5) → (False ∨ False)) ∧ True) ∧ p2) → p2)))) ∨ False)) → p2) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- False on the left can always be used.
      apply False.elim h11
    case inr h12 =>
      -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
      have h13 : (p2 → True) := by
        -- Implications on the right can always be decomposed.
        intro h14
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h9, we can now drive its conclusion.
      let h15 := h9 h13
      -- We need to get the left conjuct of h15 based on <expert-advice>.
      let h16 := h15.left
      -- False on the left can always be used.
      apply False.elim h16
  case inr h17 =>
    -- False on the left can always be used.
    apply False.elim h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_700691157160540758363603071879 : ((((p5 → ((p1 ∨ False) ∧ (True → (False ∨ (p3 ∧ (p2 ∧ p1)))))) → (((p2 ∨ p2) → True) ∧ ((((False ∧ p3) ∧ p3) ∧ p2) ∧ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_25389333628317835892324994889 : ((((p1 → True) → p2) → (False ∨ ((p2 ∧ (False ∧ p5)) ∨ (((True → ((False ∨ (((p3 ∨ True) ∨ p2) ∧ p4)) ∧ False)) ∧ p3) ∨ True)))) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115940796419283537324858883708 : (((False ∨ ((p3 → p4) → p1)) ∨ (((True ∧ (((p2 ∧ (p2 → p4)) ∨ (p5 ∨ False)) ∧ p4)) ∧ p4) ∨ (False → (True → True)))) ∨ (False ∨ p3)) := by
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
theorem thm_5_vars_240872730236069953839670300231 : ((True → True) ∧ ((((p4 → p3) → (False → (False → p4))) ∨ (p1 ∨ p1)) → (((p4 ∧ p2) → p2) → (((p2 ∧ p3) ∧ (p3 ∨ False)) ∨ True)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h2
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_757244244889109909963431805545 : (((p1 ∧ ((True → True) ∧ ((p1 → (p4 → ((p4 ∧ True) ∧ ((((True ∨ (p2 ∧ (p3 ∧ p4))) ∨ p2) → False) ∧ p5)))) → (False ∨ p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_732018286274255102148687193743 : ((((True ∧ False) ∧ ((p2 → ((True ∧ (True → p1)) ∨ ((p4 ∧ (((p4 ∧ p4) ∨ p4) → p3)) ∨ (p1 ∧ (p2 ∧ p3))))) → (p2 ∨ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_788549590393105946583132511305 : (((p5 ∨ ((p3 → ((p4 → (((p2 ∨ True) ∧ ((True ∧ (False ∨ (p1 ∨ p2))) ∨ ((p1 ∨ True) ∨ True))) ∨ False)) → (False ∧ p1))) ∨ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113280212116666778463461016480 : ((((p3 ∧ (p4 ∧ ((((p5 ∧ False) ∧ (False → p3)) ∨ p4) ∧ p4))) ∧ (p3 → (False ∨ (p2 ∧ (p2 ∨ p1))))) ∧ (p2 ∧ p4)) ∨ (True ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199261727367109827030433633048 : ((((((p5 ∨ p1) ∧ p2) ∧ p5) ∧ p4) ∨ p2) → ((((True → p1) ∨ (p1 → (((p1 ∨ p3) → (p1 ∨ (p2 ∨ p3))) ∨ p1))) → p1) ∨ True)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54751772804263643383640505482 : ((((True ∧ False) ∨ (((True → p2) ∨ p1) → p5)) → (p5 ∨ (((p2 ∨ p1) → (p5 ∧ (p2 ∨ p3))) ∨ (False ∨ ((True ∨ p3) ∨ p4))))) ∨ p5) := by
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
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
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
theorem thm_5_vars_40003145892402490304680457830 : (((p5 → ((((True ∨ (True ∧ p1)) → (p2 ∧ p5)) ∨ p3) → (p2 → (p3 → ((True → p4) ∧ (p5 ∧ (p2 ∨ (p5 ∧ p2)))))))) ∧ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245418758047814476851005749161 : ((p2 ∧ p4) ∨ ((((((p5 ∧ p2) → p4) → ((False ∧ p2) → ((False ∨ p2) → p1))) ∧ (p1 ∨ (p1 → p2))) → p3) ∨ ((p4 ∧ p5) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



