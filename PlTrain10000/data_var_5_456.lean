variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321196184506937079633736604605 : (p4 ∨ (p3 ∨ ((((p3 → p3) → ((p1 → p1) ∧ p4)) → p3) ∨ (((((p3 ∧ ((p2 ∨ p3) ∧ p2)) ∧ p2) ∧ p5) ∧ (p4 → p4)) → p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- Conjunctions on the left can always be decomposed.
  let h10 := h9.left
  let h11 := h9.right
  -- Disjunctions on the left can always be decomposed.
  cases h10
  case inl h12 =>
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h13 =>
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61158763207414775583206730358 : ((False ∧ ((p1 ∧ ((p2 ∨ p1) ∧ True)) → (((p4 → p4) ∧ ((p3 ∧ (p3 ∨ (p5 ∨ (p1 ∨ p5)))) → p1)) ∧ ((p4 ∧ p4) ∨ p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41310287640131692752900004857 : ((((((p1 → (p1 ∨ (p1 → p5))) → (p2 ∨ (p2 ∨ (p5 ∨ (True ∨ False))))) → p3) ∧ ((False ∧ (False ∧ (True ∧ p1))) ∧ p1)) ∨ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60178195974163248521599239163 : (((p5 ∨ p1) → ((p5 ∨ (((p4 ∨ (p3 → ((((p1 ∧ (p4 → p1)) → p2) → False) ∨ p2))) ∧ p4) ∨ (False ∨ p2))) ∨ (p2 → p2))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_751397326886207902380105089198 : (((True ∧ ((True ∧ p2) → ((p2 ∨ True) ∧ (p3 ∨ (((p4 ∨ p3) → (((((True ∨ p2) ∨ False) → False) ∧ False) ∧ (False ∨ p3))) ∨ p2))))) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_316866903120502394208748856249 : (p3 ∨ (p1 → ((p2 ∨ ((p4 ∨ (p2 ∨ (p4 ∧ (p1 ∨ p4)))) → ((p2 ∧ (p2 ∨ (p1 ∧ p3))) ∨ (True ∨ p2)))) ∧ (p1 ∨ (True → p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
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
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59384620868360494321886246024 : (((True → False) ∨ (((False ∨ (p1 ∧ ((((False → False) ∧ (((p1 ∧ ((False → p3) ∨ p3)) → True) ∨ True)) ∨ p5) ∧ True))) ∨ p3) → p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166758514781517177910734512359 : ((p4 → (p3 ∨ (((p4 ∨ p3) ∧ (p5 ∧ p3)) ∧ (((p5 → (p3 ∧ p3)) ∨ p2) → p3)))) ∨ ((((p4 ∨ False) → p4) → False) → (p3 ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p4 ∨ False) → p4) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h5 =>
      -- False on the left can always be used.
      apply False.elim h5
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h2
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206055862090563886986514815258 : ((p3 ∧ (((p5 ∧ p4) ∨ p2) ∧ True)) ∨ (((p2 ∧ p3) → True) → ((p5 → ((False ∧ True) ∨ p2)) → ((True → (True ∧ p1)) ∨ (False → p1))))) := by
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
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_202152835744991915342747560172 : ((((p5 ∨ True) ∧ (True ∨ p1)) → True) ∧ (((p5 ∨ (p5 → p2)) ∧ p2) → ((((False ∧ p4) → p1) → ((True → False) ∨ True)) ∧ (True ∨ p2)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
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
  -- Conjunctions on the left can always be decomposed.
  let h8 := h2.left
  let h9 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h10 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h11 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_699903355419361153180515550617 : (((((False ∨ ((False ∧ (p1 ∧ p2)) → p4)) ∨ ((p2 → p4) ∧ p1)) → (((((False ∧ p3) ∧ True) ∨ ((p2 → False) → p1)) → p5) ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40948898530969680615226512653 : (((((p5 ∧ (p2 ∨ ((p1 ∧ ((p3 → False) ∨ (False → p3))) ∧ ((True → p1) → (True ∧ p1))))) ∧ (False → p4)) ∨ (p1 → p1)) ∨ False) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193677667374705810381844930214 : ((p1 ∧ ((((p4 ∧ (False ∨ False)) → p3) ∨ True) ∨ p4)) → ((p5 ∧ (p3 ∨ (p4 ∧ p5))) ∨ (((p1 ∨ (p5 → True)) → p1) ∨ (p2 ∧ False)))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h6
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- One of the premise coincides with the conclusion.
        exact h7
      case inr h8 =>
        -- One of the premise coincides with the conclusion.
        exact h2
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h10
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- One of the premise coincides with the conclusion.
        exact h11
      case inr h12 =>
        -- One of the premise coincides with the conclusion.
        exact h2
  case inr h13 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h14
    -- Disjunctions on the left can always be decomposed.
    cases h14
    case inl h15 =>
      -- One of the premise coincides with the conclusion.
      exact h15
    case inr h16 =>
      -- One of the premise coincides with the conclusion.
      exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_329376826492481860578961303877 : (True → ((True → (False ∧ False)) → (((((p4 → p2) → True) ∧ True) ∨ ((True → (p3 ∧ (p4 → p3))) → p3)) → ((p5 ∨ p4) ∧ (p3 ∧ p5))))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h7 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h8 := h2 h7
    -- We need to get the left conjuct of h8 based on <expert-advice>.
    let h9 := h8.left
    -- False on the left can always be used.
    apply False.elim h9
  case inr h10 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h11 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h12 := h2 h11
    -- We need to get the left conjuct of h12 based on <expert-advice>.
    let h13 := h12.left
    -- False on the left can always be used.
    apply False.elim h13
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h14 =>
    -- Conjunctions on the left can always be decomposed.
    let h15 := h14.left
    let h16 := h14.right
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h17 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h18 := h2 h17
    -- We need to get the left conjuct of h18 based on <expert-advice>.
    let h19 := h18.left
    -- False on the left can always be used.
    apply False.elim h19
  case inr h20 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h21 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h22 := h2 h21
    -- We need to get the left conjuct of h22 based on <expert-advice>.
    let h23 := h22.left
    -- False on the left can always be used.
    apply False.elim h23
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h24 =>
    -- Conjunctions on the left can always be decomposed.
    let h25 := h24.left
    let h26 := h24.right
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h27 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h28 := h2 h27
    -- We need to get the left conjuct of h28 based on <expert-advice>.
    let h29 := h28.left
    -- False on the left can always be used.
    apply False.elim h29
  case inr h30 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h31 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h32 := h2 h31
    -- We need to get the left conjuct of h32 based on <expert-advice>.
    let h33 := h32.left
    -- False on the left can always be used.
    apply False.elim h33



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164776234418223015723649991302 : ((((p2 ∨ ((((p5 → p4) ∨ p2) → p3) ∨ False)) → (p1 ∨ ((p1 → True) ∧ p3))) ∨ False) ∨ ((p1 → p2) ∨ (((p3 ∨ True) ∧ p3) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54211488890362081609495879442 : ((((True → ((True ∧ p2) ∧ (p3 → p1))) ∨ True) ∧ ((((p4 ∨ (p5 ∧ p1)) ∨ (True ∧ p5)) ∨ (p2 ∧ p4)) ∨ (p5 ∨ (p1 → p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159406213120091533085263516793 : (((((p5 → p4) ∨ ((((p4 ∧ True) ∨ (p4 ∧ p1)) ∨ p5) → ((False ∨ p1) → p3))) → False) ∧ p4) → ((p1 ∧ p5) ∨ ((p4 → p1) ∧ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : ((p5 → p4) ∨ ((((p4 ∧ True) ∨ (p4 ∧ p1)) ∨ p5) → ((False ∨ p1) → p3))) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h4
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157653507625277622640891282196 : (((((p5 → (p3 ∧ (((False ∨ p4) ∧ (p2 ∨ p1)) ∨ p2))) ∨ True) ∨ p1) ∨ ((p2 → p3) ∧ True)) ∨ ((p4 → ((p5 ∨ p3) ∧ p3)) ∧ p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_155204810593216583992080228661 : (((((p4 ∨ (p3 → (False ∨ p5))) ∨ p5) ∧ False) ∨ ((p2 → (p3 ∨ (p2 ∧ (p5 ∨ p2)))) ∨ p2)) ∧ ((False ∨ (False ∧ (p1 → p4))) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_669271593713832816674930017391 : (((((p1 → ((p4 ∧ ((p3 ∨ p5) ∧ (False ∨ (p5 ∨ p2)))) ∨ ((p2 → p3) → (True ∧ (True ∧ p5))))) → p5) ∨ (False → (p2 → p5))) ∨ p1) ∧ True) := by
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
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346960535557877449349085622138 : (p3 → ((False ∨ (p3 → (True ∧ (((p1 ∧ (p2 ∧ ((p5 → p2) ∨ p4))) ∧ (True ∨ p2)) ∨ p5)))) → (p1 ∨ ((p4 ∨ p4) ∨ (p3 → p5))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h5 : p3 := by
      -- One of the premise coincides with the conclusion.
      exact h1
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h6 := h4 h5
    -- We need to get the right conjuct of h6 based on <expert-advice>.
    let h7 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Conjunctions on the left can always be decomposed.
      let h11 := h9.left
      let h12 := h9.right
      -- Conjunctions on the left can always be decomposed.
      let h13 := h12.left
      let h14 := h12.right
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h15 =>
        -- Disjunctions on the left can always be decomposed.
        cases h10
        case inl h16 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h11
        case inr h17 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h11
      case inr h18 =>
        -- Disjunctions on the left can always be decomposed.
        cases h10
        case inl h19 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h11
        case inr h20 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h11
    case inr h21 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h22
      -- One of the premise coincides with the conclusion.
      exact h21



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_22913169658073683562443769410 : ((((p4 → p3) → (p4 ∧ (p5 → False))) ∨ ((False → p4) ∨ (True ∧ (((p3 ∨ p3) ∨ (((False ∧ p5) → (p1 ∨ p1)) → p4)) ∧ p1)))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_320412241021405108905650638799 : (p4 ∨ ((p5 ∧ True) → (False ∨ ((((p4 ∨ (p2 → (p2 ∧ p4))) ∧ p4) ∧ ((p1 ∨ ((p1 ∧ p4) → True)) → p1)) → ((p2 ∨ p2) ∨ p5))))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h10 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227228038321829726505171460998 : (((False → p1) → p2) ∨ (((p1 ∧ ((p4 → p5) ∨ ((p3 → p1) ∧ (True ∨ (((p2 ∧ (p1 ∨ p4)) → p3) ∨ p5))))) → (p2 → p5)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_690435240512035548046351433781 : ((((((((False → p1) → (True ∧ (p4 ∧ (p1 ∨ p5)))) ∨ (p1 ∨ True)) → True) ∧ p2) → (((p1 ∨ True) ∨ (p5 → False)) ∧ (p3 ∨ p2))) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180359255056103613156909398728 : ((((((p1 ∨ p3) ∨ (False ∨ p3)) → (False → p2)) ∨ p3) ∨ (True ∨ True)) → (((p5 → p1) → p2) ∨ ((True ∨ p3) ∨ ((True ∧ False) ∧ p4)))) := by
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_252803918003133847098352314888 : ((True ∧ True) → (p4 → ((True → ((((p2 ∧ False) ∨ p4) → p4) ∧ False)) → (p5 ∨ ((p3 → (p3 ∨ False)) ∧ (p2 ∨ (p5 ∧ (p5 ∧ p1)))))))) := by
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
  have h6 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h7 := h3 h6
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47466567526955963605659829340 : (((p5 ∧ ((p2 → ((p1 → (False → (p2 → (p1 ∨ p3)))) ∧ p5)) → (False ∧ (p4 ∨ (p1 ∧ (p5 → (p4 → False))))))) ∨ (True → p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110481708591839669681456614162 : ((p4 → ((p5 → (p1 → ((p2 ∧ ((p4 ∧ ((p3 ∨ (p1 → p5)) ∧ (((False ∨ p3) ∨ True) ∧ p1))) ∨ True)) ∨ p2))) ∨ p4)) ∧ (True ∨ p1)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263051981107153451985200851940 : (True ∧ ((p4 ∨ ((p5 ∨ False) → (((p5 ∨ p5) ∧ ((p1 → p4) → ((p1 ∧ (True ∧ p1)) ∧ False))) ∨ ((p2 → True) ∨ True)))) ∧ (p2 ∨ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- False on the left can always be used.
    apply False.elim h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_261070903617487560465955116986 : ((p4 → p3) → (((p5 ∧ ((True ∨ p2) → (((((p3 ∧ p2) ∨ ((p5 ∨ ((False ∧ p3) → False)) → p1)) ∨ True) ∧ p1) ∧ p4))) ∨ True) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317647303546326441636331266604 : (p4 ∨ (((p3 ∨ (p5 → (p5 → (((p2 ∧ ((p5 ∧ True) → (False ∨ (((p2 ∧ p1) → False) ∨ p5)))) ∨ p4) ∨ (p4 ∧ p2))))) ∨ p3) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38994890741262122408816615205 : ((((False ∨ p2) ∧ ((p5 ∧ ((True ∧ p3) ∨ p3)) ∧ ((p5 ∨ (((((p2 ∨ True) ∧ False) → p1) ∨ (p3 ∨ p1)) ∨ True)) ∨ p5))) ∧ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55158045259186723515699320409 : ((((False ∧ (False → (p5 ∨ p4))) ∨ p5) ∨ (p1 ∨ ((((p3 ∧ p3) → (p4 → (((p1 ∨ p4) → p2) ∧ p1))) ∧ (False ∨ p1)) ∨ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174066573104285908512090731715 : (((((p1 ∨ (True → (((p5 → p4) ∨ p4) ∧ False))) → False) ∧ p2) ∧ (p5 ∨ p1)) → (((p2 → p5) → False) ∨ (((False ∨ True) ∨ p5) ∨ True))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_265524590734979020260376268891 : (True ∧ (False ∨ ((((p3 → False) ∧ True) ∨ ((p5 ∧ ((p3 ∨ p3) ∨ ((False ∧ (p2 → False)) ∨ ((True ∨ p1) ∨ p1)))) ∨ p4)) ∨ (False → False)))) := by
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
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260920692240429918550315850700 : ((p4 → False) → (((True ∧ p4) → p4) → ((p3 → (p3 → (p5 ∨ ((p5 → (p2 ∧ (True → p1))) ∨ (True ∧ (p5 ∨ (False → p3))))))) ∨ p3))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h5
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52444384259989610092918593271 : (((p1 ∧ ((p1 ∨ True) → (((p3 → (False → p3)) → (p4 ∨ p4)) ∨ True))) ∧ ((p4 ∨ (((True ∨ False) ∧ (p4 ∨ False)) ∧ p5)) ∨ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190045973637683190845517260640 : (((((True ∧ p4) → (p3 ∨ (True → p3))) ∨ p5) ∧ p5) ∨ ((False ∧ (p5 ∧ (p3 ∧ (((True ∨ (p1 → p2)) ∨ True) ∨ p2)))) ∨ (False → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158184494374257092770228894916 : (((True ∨ (p5 ∨ (True → p3))) → (((p4 ∧ p2) ∧ True) → ((True ∧ (p1 ∧ p1)) ∨ (True ∨ p1)))) ∨ (((False ∨ (p5 ∧ p1)) ∧ p2) ∨ p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_747313486581312218890797307805 : ((((p5 ∨ p3) → (p1 → ((p5 ∧ (((p5 → True) → ((True ∧ (False → (p3 → False))) → (False ∨ (p1 ∧ p3)))) ∨ p1)) ∧ (p5 ∧ p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45052520759661295592844105435 : ((((p1 → p1) ∨ (p2 ∧ ((p3 ∨ p4) ∧ ((((p2 ∨ p4) ∨ (True ∨ (p3 ∨ p1))) ∧ p1) → (p4 → (p5 ∨ (False → True))))))) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148590001361323926065838261292 : (((((p5 ∧ p2) ∧ (p5 ∨ p4)) → ((False ∨ p3) ∨ p4)) ∨ (p1 ∨ (((p3 → p4) ∨ p3) → (False ∧ p4)))) ∨ (p4 → (p3 → (p2 → p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119642288674772506892267907326 : ((((((p4 ∧ p2) ∧ (p4 ∧ (False ∧ (p2 → ((p3 ∧ p1) ∧ (p1 ∧ (True ∧ (p4 ∨ (p5 → p2))))))))) → p1) ∧ p1) ∧ p4) → (p3 → p3)) := by
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
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_344289504880345847057419130299 : (p2 → (p3 ∨ ((False ∨ ((True → p3) ∨ (True ∧ (((p5 ∨ p2) ∨ (((p1 ∨ True) ∨ (p5 → p1)) → p4)) ∧ (p3 ∨ (p1 → p4)))))) ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48682230436423061266554793867 : (((((False ∧ (p5 ∨ (p3 → p1))) ∨ ((True ∨ p4) ∨ True)) → (((((p2 ∨ False) → p1) → True) → True) → p3)) ∧ (False ∨ (False ∨ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47072719487048529384712735014 : ((((p5 ∨ (p2 ∨ (p1 ∨ ((p5 ∨ p1) → (p4 → ((((p4 ∧ p4) ∨ p2) ∨ True) → (True ∧ p3))))))) ∨ (p4 ∧ p2)) ∨ (p2 → True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_810691517957049140389414385221 : (((p5 → ((True ∧ (True → p3)) ∨ (((p2 ∧ True) ∧ (((p4 → ((p4 ∧ True) ∧ (True ∧ False))) ∧ p1) → p1)) ∧ (p5 → (p5 ∨ p1))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_778389506402456259396795891300 : (((p1 ∨ (p2 ∧ (((True ∨ False) → (((p4 ∨ (p2 ∧ p1)) → (p4 ∧ p5)) → ((True ∧ p4) ∧ False))) → (((p5 ∨ p2) → p2) ∧ False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_103006135566460225080478416038 : (((((((p1 → p4) → ((p5 ∧ False) → p5)) → p1) ∨ p5) ∨ (p3 ∧ (p2 ∨ (p2 ∨ ((p5 ∧ (p5 ∧ False)) → p1))))) ∨ True) ∧ (True ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_548121452751603161711151294129 : (((False ∨ (((p2 ∨ True) ∧ ((p4 ∨ ((p1 → p5) → p2)) ∧ p1)) ∨ ((True ∨ (((p4 → p3) ∨ p4) ∧ ((p5 → p2) ∧ p4))) ∨ p3))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116710756186488875202967677509 : (((p1 ∧ p4) ∨ ((p1 ∨ ((((((False ∨ p1) → p3) → ((p5 → p4) ∧ p4)) ∧ (p2 ∧ p5)) → p3) → (p3 ∨ p5))) → False)) ∨ (True ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165760299443893846799487861733 : (((p3 → ((p2 ∧ p1) ∧ p1)) ∨ (((p3 ∧ p2) ∧ (p1 ∧ p2)) ∧ (p4 ∧ (p5 ∨ False)))) ∨ ((True ∧ True) → (p2 ∨ (p4 ∨ (p4 ∨ True))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_196810223689831872957315865144 : ((((p1 → True) → (True → (p3 → True))) ∧ p2) ∨ ((p3 ∨ ((p2 ∧ True) → ((((p3 → p1) ∨ True) → False) ∨ (True ∨ (True ∧ True))))) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_46927571104779893021574761509 : (((((False → p1) ∧ ((p4 ∨ p3) → (((p5 ∨ True) → (True ∧ (((p5 → p5) → p1) → p5))) ∨ (p4 ∧ p5)))) ∨ p2) ∨ (True ∧ True)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137677910772941854379987545293 : ((p1 ∨ ((((False → True) ∧ ((p3 ∧ ((p3 ∧ (p1 ∨ p5)) ∨ (p1 ∨ (p4 ∨ p5)))) → p1)) ∧ (p2 → p5)) ∧ p3)) ∨ (p2 ∨ (p5 → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65485864354514412957105688703 : ((p3 ∨ (p3 ∧ (((p5 ∨ ((p5 → ((False → p5) → (p1 → (p3 ∨ (p5 → True))))) ∧ (True ∧ (p1 ∨ p4)))) ∨ (p4 → p2)) ∧ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2280880807913346445128503169 : (((p1 → (((p4 → (p5 → p3)) ∨ (True ∧ False)) ∧ p4)) → (p2 ∨ p3)) ∨ (p4 → ((p2 ∧ (p1 ∧ (p5 → p2))) → (True ∧ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_344505897065523148730807410491 : (p2 → (True → (True ∧ (False ∨ (((p1 ∨ ((False ∨ True) ∨ (p5 ∨ ((p4 ∧ (p3 → p4)) → p5)))) → ((p2 ∧ (p2 → False)) → p3)) ∨ False))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h7 =>
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h8 : p2 := by
      -- One of the premise coincides with the conclusion.
      exact h5
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h9 := h6 h8
    -- False on the left can always be used.
    apply False.elim h9
  case inr h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- False on the left can always be used.
        apply False.elim h12
      case inr h13 =>
        -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
        have h14 : p2 := by
          -- One of the premise coincides with the conclusion.
          exact h5
        -- We have shown the premise of h6, we can now drive its conclusion.
        let h15 := h6 h14
        -- False on the left can always be used.
        apply False.elim h15
    case inr h16 =>
      -- Disjunctions on the left can always be decomposed.
      cases h16
      case inl h17 =>
        -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
        have h18 : p2 := by
          -- One of the premise coincides with the conclusion.
          exact h5
        -- We have shown the premise of h6, we can now drive its conclusion.
        let h19 := h6 h18
        -- False on the left can always be used.
        apply False.elim h19
      case inr h20 =>
        -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
        have h21 : p2 := by
          -- One of the premise coincides with the conclusion.
          exact h5
        -- We have shown the premise of h6, we can now drive its conclusion.
        let h22 := h6 h21
        -- False on the left can always be used.
        apply False.elim h22



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346590312405661240256301325899 : (p3 → (((((True ∧ p4) → (p5 ∨ (((p5 → p5) ∨ True) → (((p1 ∧ p4) → p2) ∨ False)))) ∧ (p5 ∨ p3)) ∨ p5) ∨ (p3 → (p2 → p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63010335770678122054811270422 : ((p4 ∧ (p2 → ((((p1 ∧ (((p3 ∨ p3) → True) → (p5 ∨ p3))) ∨ (((False ∧ False) ∨ True) ∧ p2)) ∧ p4) → ((p3 ∨ p1) ∧ p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111091902842803273787723292198 : ((((p4 ∨ (((((False ∨ p5) ∧ p4) ∨ p3) ∨ (p2 → p1)) ∨ p4)) ∨ ((((p2 ∧ False) ∧ p5) ∨ True) → (p3 → True))) ∧ p2) ∨ (False → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_618275501532157709819369068894 : ((((((False ∧ p1) ∧ (p1 ∧ p1)) ∨ (((False → ((p1 → p3) ∨ p5)) → ((p3 → ((p4 → p3) ∨ p3)) → (False ∧ False))) → p5)) ∨ p2) ∨ False) ∧ True) := by
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
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (False → ((p1 → p3) ∨ p5)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h5 : (p3 → ((p4 → p3) ∨ p3)) := by
    -- Implications on the right can always be decomposed.
    intro h6
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h6
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h7 := h4 h5
  -- We need to get the left conjuct of h7 based on <expert-advice>.
  let h8 := h7.left
  -- False on the left can always be used.
  apply False.elim h8
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37842801371633030789487854278 : ((((p4 ∨ (True → ((((True ∧ p4) ∨ ((p3 → (p2 ∨ p4)) ∧ (p5 → p1))) ∧ ((p2 → p3) → True)) → (p5 → p1)))) → False) ∧ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150148945574249651316871612963 : ((p1 → ((((((p1 → (p5 ∧ p3)) ∧ p5) ∧ True) → ((((p5 ∨ True) ∧ p4) ∨ p3) ∨ p3)) → p3) → False)) ∨ (False → (p4 ∧ (p3 ∨ p3)))) := by
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
theorem thm_5_vars_690779065528400790978483012195 : ((((((((p5 ∧ p1) → False) ∨ (p2 ∨ (p3 ∨ p2))) → ((p3 → p4) ∧ p2)) → p2) → (((p5 ∧ ((False ∨ p3) ∨ False)) → True) ∧ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_211643644832781575402169926001 : (((p2 → p4) → (p4 ∨ True)) ∧ ((p4 → (p3 ∧ (False → ((p1 ∧ p2) → p2)))) → ((False ∨ p4) → (p2 ∨ ((p2 ∨ (p4 ∧ False)) ∨ p4))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135567896820976692289575883658 : (((p3 → (p1 → (((p3 ∨ (False ∧ p3)) ∧ ((p4 → False) → p4)) ∨ (p3 → p5)))) ∧ (False ∨ ((p5 → False) ∨ p5))) ∨ ((p1 → True) ∧ True)) := by
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
theorem thm_5_vars_873364804925457125789661016185 : ((((p2 → (((p4 ∨ (p4 → p3)) ∨ False) → ((False → p5) → (p4 ∨ ((((True ∨ (p3 ∨ p4)) ∧ p3) → (False ∨ p2)) ∨ p1))))) → False) → p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p2 → (((p4 ∨ (p4 → p3)) ∨ False) → ((False → p5) → (p4 ∨ ((((True ∨ (p3 ∨ p4)) ∧ p3) → (False ∨ p2)) ∨ p1))))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h7
      case inr h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h9
        -- Conjunctions on the left can always be decomposed.
        let h10 := h9.left
        let h11 := h9.right
        -- Disjunctions on the left can always be decomposed.
        cases h10
        case inl h12 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h3
        case inr h13 =>
          -- Disjunctions on the left can always be decomposed.
          cases h13
          case inl h14 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h3
          case inr h15 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h3
    case inr h16 =>
      -- False on the left can always be used.
      apply False.elim h16
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h17 := h1 h2
  -- False on the left can always be used.
  apply False.elim h17
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_879843895323109771006316849772 : ((((p2 → (p4 ∧ ((p2 ∨ p1) ∧ (True ∧ (((p3 ∧ p3) ∨ (True ∨ ((((p3 ∨ p5) → p4) ∨ p3) → True))) → p5))))) ∧ (p4 ∧ p2)) → p5) ∧ True) := by
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
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h6 : p2 := by
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h7 := h2 h6
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- We need to get the right conjuct of h9 based on <expert-advice>.
  let h10 := h9.right
  -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
  have h11 : ((p3 ∧ p3) ∨ (True ∨ ((((p3 ∨ p5) → p4) ∨ p3) → True))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h10, we can now drive its conclusion.
  let h12 := h10 h11
  -- One of the premise coincides with the conclusion.
  exact h12
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_715924675801735091904085332396 : (((((p4 ∨ (p2 ∨ False)) ∨ True) ∧ (p2 → (((True → (False → p1)) → (p3 → (p5 ∨ False))) → (p5 → ((False ∨ p1) ∨ (p2 ∧ p1)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_693845983944374094252910712977 : ((((((p2 ∧ True) ∨ (((((True ∨ p1) ∨ True) ∧ p3) → False) ∧ p2)) → False) ∨ ((p4 ∨ False) ∨ ((p3 → p3) ∨ (False ∧ (p2 ∨ False))))) ∨ False) ∧ True) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_809171346531431888920950529292 : (((p5 → ((((((((((False ∨ p4) ∧ False) → True) → (p3 → p2)) ∨ p1) ∧ p3) ∨ ((p3 → (p1 ∧ p5)) ∨ p3)) → p4) → False) ∨ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_700627395614890732639045974621 : ((((p2 → (((p2 ∧ p4) ∨ p5) → ((p3 ∧ p1) ∧ (p3 ∧ p1)))) → (p3 → ((p4 → ((p1 ∨ p3) ∧ (p5 ∧ (False ∨ p4)))) ∨ p3))) ∨ p2) ∧ True) := by
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
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173181918408951909085524778115 : ((p4 ∨ ((p2 ∧ (True ∧ p4)) ∨ (True → (((p5 ∧ (p3 ∧ False)) ∧ p4) ∨ True)))) ∨ (((((p2 → p1) → p5) ∧ (p4 → p3)) → p5) → p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337342639407934770367498245594 : (p1 → (((((((p5 ∨ p4) ∨ p5) ∧ p3) ∧ (True ∨ ((False ∧ (p5 → ((p2 → p1) ∨ p2))) ∧ True))) ∧ p2) ∨ True) ∨ (p2 ∨ (p4 ∨ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299190150185912234813084882081 : (False ∨ (((p2 ∧ (p1 ∧ (True → (p3 → (p1 ∧ (((p5 ∧ p3) → ((False ∧ (True → True)) ∧ p4)) → (p2 → (p3 ∧ p5)))))))) → p5) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184173734995483712807862148846 : (((p1 → ((True → (p5 → p1)) → (p3 ∨ (True ∧ p5)))) ∨ True) ∨ ((p5 ∧ False) ∨ (p4 ∨ ((p2 ∧ (((False ∨ p2) → True) → p3)) ∨ True)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157585704068715540967789359958 : (((p3 ∧ (((((p4 ∧ False) → False) ∧ ((False ∨ False) ∨ p5)) → (p2 → p5)) ∨ p2)) → (p2 → False)) ∨ (((p3 ∧ False) → False) ∨ (p5 ∧ p2))) := by
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
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157157094200520117261116588211 : (((((True ∧ p4) → (((p5 ∨ False) → True) → (p2 → (p1 → (p4 ∨ (p2 ∨ p3)))))) ∨ p1) → p2) ∨ (False → (((p4 → False) ∨ True) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324120178503713021728194182641 : (p5 ∨ ((p4 ∧ (True → (p4 → (False ∨ (((p2 ∨ p1) ∧ True) ∨ p2))))) → (((p2 ∧ p5) → ((p5 → False) ∨ p1)) ∨ (p2 ∨ (True ∨ p4))))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160036292710463805225499775160 : ((((p1 ∨ p1) ∨ (True ∧ ((p5 → ((p2 ∨ p5) ∧ p2)) ∨ (((True ∨ p1) → True) ∧ True)))) → p4) → ((((p4 → p2) → False) ∨ p4) ∨ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p1 ∨ p1) ∨ (True ∧ ((p5 → ((p2 ∨ p5) ∧ p2)) ∨ (((True ∨ p1) → True) ∧ True)))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44015233226087224475510458532 : ((((((p1 ∧ (p2 → True)) → (p3 ∧ (p2 ∧ (False → p3)))) ∧ ((False ∨ (p4 ∧ p2)) → ((False ∧ p2) ∨ True))) → (p2 ∨ p1)) → p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115553421026028387276805194889 : (((((False ∨ True) ∨ (p2 ∨ p4)) ∧ p5) ∧ (p5 ∨ (((True → ((p3 → p2) ∨ False)) → (p5 → p5)) ∧ ((p5 ∨ p4) ∨ p4)))) ∨ (p1 → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178235394426909140074867901236 : (((p4 → (p1 ∨ ((p5 ∨ (p4 ∧ p4)) → (p2 → (p4 → True))))) → p1) ∨ ((p3 ∨ ((False → p5) → (False → ((p4 ∨ p4) → True)))) ∨ False)) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217905193776860609952942263573 : (((p3 → (p4 → p2)) → p1) → ((p2 ∧ (((((False → p4) ∧ (p2 ∨ False)) ∨ (((p1 → True) → False) ∨ (p3 ∧ False))) ∨ p2) → p3)) → p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h5 : ((((False → p4) ∧ (p2 ∨ False)) ∨ (((p1 → True) → False) ∨ (p3 ∧ False))) ∨ p2) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h6 := h4 h5
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112853914518253739795336206967 : (((((True ∧ p2) ∧ p1) ∨ ((p4 ∨ ((p5 ∨ (False ∧ (p1 ∧ p5))) ∨ ((p4 ∨ (p4 → (p1 ∨ p1))) ∨ p5))) ∨ p5)) → p1) ∨ (True ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_695256589276813121727719243337 : (((((((p3 → ((False ∧ (p3 → p5)) → (False → p3))) ∨ p3) → False) → False) → ((((p4 → (False ∨ (False ∧ p1))) → p5) → p2) ∨ True)) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_191240019809250271953246314211 : (((True ∧ False) ∧ (p2 ∨ ((p4 → (p2 ∧ p3)) → p2))) ∨ (False → (p4 ∨ ((((False ∨ (True ∧ (p5 → p5))) ∧ p3) ∨ p2) → (p3 ∧ False))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303853702025139154912514574489 : (p1 ∨ (((p2 ∨ (((p1 → (p3 → p1)) ∧ ((False ∧ ((((True → p5) → p4) ∧ (p4 → p2)) ∨ True)) → p5)) ∨ True)) → (False ∨ p2)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42027806003224546374985775452 : ((((p2 ∧ True) ∨ (((p5 ∧ ((p5 ∧ p3) → p5)) → (True ∧ (p4 ∨ p3))) ∧ ((((p4 ∧ (p4 ∨ p4)) ∧ p2) → False) ∧ False))) ∨ True) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167643474521428329768572827011 : (((((p5 ∨ False) ∧ ((p2 → p1) ∨ p3)) → (p4 → ((False ∨ p4) ∨ p1))) → (p3 ∧ False)) → (p2 ∧ ((p2 → p4) ∨ ((p1 ∧ p2) ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p5 ∨ False) ∧ ((p2 → p1) ∨ p3)) → (p4 → ((False ∨ p4) ∨ p1))) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h8 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h4
      case inr h9 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h4
    case inr h10 =>
      -- False on the left can always be used.
      apply False.elim h10
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h11 := h1 h2
  -- We need to get the right conjuct of h11 based on <expert-advice>.
  let h12 := h11.right
  -- False on the left can always be used.
  apply False.elim h12
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227237830928690882888147392210 : (((False → p3) → False) ∨ (((((p1 ∨ (((p5 → p3) ∨ ((False ∨ False) → False)) → True)) ∨ p3) → True) → ((True → p2) ∨ p2)) ∨ (False → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336140519815612027002162924483 : (p1 → (((p5 ∨ (p2 → (False ∨ ((((True ∨ p2) ∧ (True ∧ False)) ∧ ((p5 → True) ∧ p4)) ∧ (p2 ∨ (p4 → (p1 → False))))))) ∨ p1) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_684305943859028210414318831935 : ((((((False → (((p2 ∨ (p2 → p2)) → False) → (p1 ∧ p4))) ∧ p1) → (p2 ∨ (False ∧ p3))) ∨ (((False → p4) ∨ p4) ∨ (p3 → True))) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_710319795567408211684075736649 : (((((((False ∨ p4) ∧ False) ∧ False) → False) ∧ ((p3 ∨ (((((False ∧ True) ∨ p5) ∨ p3) → p2) ∧ p2)) ∨ ((p4 ∨ (False ∨ p4)) ∨ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174078793471064044152401221430 : (((((False ∨ ((((p1 ∧ p1) → p3) ∨ False) ∨ p5)) ∨ p1) → p3) ∧ (p5 ∨ p5)) → ((p3 → p1) ∨ ((False → (p3 ∨ (p1 → p5))) ∨ p5))) := by
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
theorem thm_5_vars_174749492051369185028662003616 : (((p4 ∨ (False ∧ p3)) → (p5 → ((((False ∨ p1) ∧ False) ∧ (p3 ∧ p1)) → True))) → ((True → (p4 ∧ p3)) ∨ (p4 ∨ (False → (p4 → True))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_786012551650480209180982438351 : (((p4 ∨ ((p5 → ((((p2 ∧ True) → (False ∨ ((p4 ∧ p4) → ((p2 ∧ p4) ∧ (True ∨ p1))))) → (p2 ∨ p1)) → p4)) ∨ (p3 → p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199566057052772839960263280454 : (((((p1 → (p3 ∧ p3)) → p5) ∨ p5) → p5) → ((p3 ∧ p4) → ((p1 → (True ∧ ((p3 → (p2 ∨ p4)) ∧ (False → p2)))) → (True ∧ p3)))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h4



