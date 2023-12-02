variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_348257103040607326793009290042 : (p3 → (True ∧ (((((p1 ∧ p1) ∧ (p4 → False)) → (p5 ∧ (p1 ∧ p2))) ∨ (p1 ∧ ((p5 ∧ (p4 ∧ p4)) ∨ p2))) ∨ (p5 → (False → p2))))) := by
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
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115571207589141743147990086362 : (((((p5 → p2) ∧ (True ∨ p1)) → p3) ∧ ((((p1 ∧ p3) ∨ p1) ∧ (((p5 ∨ (True → (True → False))) ∨ False) ∨ p1)) ∧ p2)) ∨ (True ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41097257001310661878622107282 : ((((((p4 ∧ (p4 ∧ (False → (p5 ∧ (p2 ∨ (False → (p3 → p2))))))) ∧ p4) → ((p5 → p5) → p5)) ∧ ((p4 → p4) → p5)) ∨ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147996226710638394367185038296 : (((((((p1 → p5) ∧ (((p1 → False) ∨ p4) → p4)) → (False ∨ True)) ∧ (True ∨ p4)) → p2) ∨ (p3 ∧ p4)) ∨ ((True → (False ∧ p1)) → p2)) := by
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
  -- We need to get the left conjuct of h3 based on <expert-advice>.
  let h4 := h3.left
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342847013759890372793570579198 : (p2 → (((False ∨ (p3 ∨ (False → p3))) ∧ p1) ∨ (p4 ∨ (p1 ∨ (((p2 ∨ (p3 → p5)) ∧ p5) ∨ (False → (True → (p1 ∧ (p2 ∨ p2))))))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_644033740172450697308770648551 : ((((True ∨ ((((((((False ∨ False) ∨ p3) → True) ∧ p3) ∧ p1) ∨ (p1 → False)) ∨ (p3 → p4)) ∨ (p4 ∨ ((p1 ∧ True) ∧ False)))) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42291082814216926449766408962 : (((p2 ∧ (((p3 → ((p5 ∨ p1) ∨ True)) → ((False → ((p3 ∨ (True ∨ p3)) ∨ False)) → (p4 ∧ (p4 → (p2 ∨ p1))))) ∧ p5)) ∨ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_264847321504861672619985665392 : (True ∧ ((p3 ∨ p1) ∨ (p1 ∨ (((((p1 → p5) ∧ ((p2 ∧ False) → ((False → True) → p2))) ∨ (p3 → False)) ∧ p4) → ((p2 → p1) ∨ p4))))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147439156784207085956677438730 : ((((p2 ∨ p5) ∧ ((True → ((p5 ∨ p3) ∨ p4)) → (False ∧ (((False → (p5 → p1)) ∧ p3) → p3)))) ∨ True) ∨ (p1 ∧ (p5 ∨ (p3 ∧ p5)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_250822358055160301911435274678 : ((p1 → p2) ∨ ((p1 ∨ ((((p4 ∨ p5) ∨ ((p4 → (p4 ∧ (p4 ∧ (p5 ∨ (p5 ∨ False))))) ∧ (p4 → p3))) ∨ True) → p1)) → (True → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h5 : (((p4 ∨ p5) ∨ ((p4 → (p4 ∧ (p4 ∧ (p5 ∨ (p5 ∨ False))))) ∧ (p4 → p3))) ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h6 := h4 h5
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_654235747276113606861787793837 : (((((((p5 ∨ (p4 ∨ p1)) → (p4 → ((False ∧ ((False ∧ p4) → True)) → ((p2 → (True ∧ p3)) ∨ p4)))) → p2) ∨ p4) ∨ (p4 → True)) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256408505870127007113437799233 : ((False ∨ p3) → ((((((p3 → True) ∧ False) ∨ (p5 ∨ (False → (((p4 ∨ False) ∨ (False → p3)) → p5)))) ∧ (p1 ∨ True)) → p4) → (p4 ∨ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h5 : ((((p3 → True) ∧ False) ∨ (p5 ∨ (False → (((p4 ∨ False) ∨ (False → p3)) → p5)))) ∧ (p1 ∨ True)) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- Implications on the right can always be decomposed.
      intro h7
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Disjunctions on the left can always be decomposed.
        cases h8
        case inl h9 =>
          -- False on the left can always be used.
          apply False.elim h6
        case inr h10 =>
          -- False on the left can always be used.
          apply False.elim h10
      case inr h11 =>
        -- False on the left can always be used.
        apply False.elim h6
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h12 := h2 h5
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51969524778990753654188807331 : ((((p3 ∧ (p1 ∨ p1)) ∨ (((True → True) ∨ ((p4 ∨ (False → p4)) → False)) ∧ False)) ∨ (((False → p5) → p2) → ((p4 ∨ True) ∨ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228232604765000081515129134176 : ((p5 ∧ (p5 ∨ True)) ∨ ((p2 ∧ p4) ∨ (((p4 ∧ ((p1 ∧ p3) ∨ ((p2 ∨ (p5 ∨ p3)) → p1))) ∨ (((True → p1) → p5) ∧ p5)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_32740728070372896221666579799 : ((p2 ∨ (p3 ∨ ((((p2 ∧ (p2 → (p5 → ((p5 ∧ p5) ∧ ((False ∧ p5) ∧ p2))))) → (p4 ∧ p5)) ∨ True) ∨ ((False ∧ False) ∨ True)))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_158931151352203915296247605516 : ((p2 ∨ (((((((False ∨ (p2 ∨ p5)) → ((p1 → True) → p5)) ∨ p5) ∧ p4) ∨ p5) ∧ p2) ∨ True)) ∨ ((p5 ∧ ((p4 ∨ p1) ∧ p1)) → False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_612609565610990352669343449188 : ((((((((p3 ∧ p4) → ((p5 ∧ ((((False ∧ p2) ∧ (p4 ∧ False)) ∨ p3) → p3)) → False)) ∧ p2) ∨ (p1 → True)) ∨ (p3 ∧ p4)) ∨ p1) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64781052154155743952443310357 : ((p2 ∨ (((p4 ∨ (p2 → (p3 ∧ ((False ∨ (((p1 → (p1 ∨ p3)) ∧ True) ∨ ((p4 → p3) ∨ p4))) ∧ (True ∧ p5))))) → p1) ∨ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_145065423847161962803419879715 : (((p5 ∧ ((p5 ∨ p3) ∧ (((p1 → False) → p3) ∧ (p3 ∨ p2)))) → ((True → (p1 ∨ False)) ∨ (p5 ∨ False))) ∧ ((True ∨ p5) → (p1 → p1))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h6
  case inr h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h5.left
    let h13 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h14 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h15 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h2
  -- Implications on the right can always be decomposed.
  intro h16
  -- Implications on the right can always be decomposed.
  intro h17
  -- Disjunctions on the left can always be decomposed.
  cases h16
  case inl h18 =>
    -- One of the premise coincides with the conclusion.
    exact h17
  case inr h19 =>
    -- One of the premise coincides with the conclusion.
    exact h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_692516181514738796199318511534 : (((((True → (p1 ∨ (p2 ∧ ((True ∨ p3) ∧ (p4 → p4))))) ∨ (False → True)) ∧ ((p4 → ((False ∨ False) ∨ False)) ∨ (p5 ∨ (False ∨ True)))) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_606490293876828399526352613882 : (((((((p4 ∨ (True ∧ (((False → True) ∧ (True → p5)) → ((p5 → p4) ∨ ((False → (p4 → p3)) ∧ True))))) ∧ p3) → p2) ∧ p4) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186616954150760689952704570069 : ((((True ∨ p5) ∧ ((False ∧ p2) → (p4 ∨ p1))) → (p5 ∧ False)) → (p3 ∧ (p3 ∧ (p2 ∨ ((((p1 ∧ (p2 ∧ p1)) → p3) ∨ p2) ∧ p2))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((True ∨ p5) ∧ ((False ∧ p2) → (p4 ∨ p1))) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- False on the left can always be used.
    apply False.elim h4
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h2
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- False on the left can always be used.
  apply False.elim h7
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h8 : ((True ∨ p5) ∧ ((False ∧ p2) → (p4 ∨ p1))) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
    -- Implications on the right can always be decomposed.
    intro h9
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- False on the left can always be used.
    apply False.elim h10
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h12 := h1 h8
  -- We need to get the right conjuct of h12 based on <expert-advice>.
  let h13 := h12.right
  -- False on the left can always be used.
  apply False.elim h13
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h14 : ((True ∨ p5) ∧ ((False ∧ p2) → (p4 ∨ p1))) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
    -- Implications on the right can always be decomposed.
    intro h15
    -- Conjunctions on the left can always be decomposed.
    let h16 := h15.left
    let h17 := h15.right
    -- False on the left can always be used.
    apply False.elim h16
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h18 := h1 h14
  -- We need to get the right conjuct of h18 based on <expert-advice>.
  let h19 := h18.right
  -- False on the left can always be used.
  apply False.elim h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47333914009249967265930279635 : ((((p3 ∧ False) ∧ (((p2 ∨ False) ∨ p2) ∧ (((p4 ∨ (False ∨ p4)) ∨ (p2 ∨ p1)) ∨ ((p3 → p1) ∨ (p5 ∧ p1))))) ∨ (False → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_443664445823767981874152769013 : ((((((False → True) ∨ (False ∧ p2)) ∧ (p3 ∨ (p4 ∨ (((p3 ∧ (p5 → p4)) ∧ (True ∨ p3)) → (p1 ∧ p4))))) ∨ ((p5 → p5) → True)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134621055951280409062111584433 : ((((((p2 ∧ False) ∨ (True → (((p3 ∧ (True ∨ p5)) ∨ p3) ∧ p2))) → (p3 → p2)) → (p3 ∨ (p4 ∨ p1))) → p4) ∨ (False → (p3 → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186073371853461292950086435616 : (((((((False ∨ (False ∨ False)) → p4) → p2) ∨ p5) → p4) ∨ p1) → ((p1 → p5) ∨ (False ∨ (((True ∨ (p5 ∨ True)) ∨ (p1 → False)) → True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64437686555736285632231945511 : ((p1 ∨ ((((True → ((p1 ∧ True) ∧ (p3 → p4))) ∧ ((False → ((True ∨ True) ∨ (True → p2))) ∧ (True ∨ p4))) → False) ∨ (p2 → True))) ∨ p5) := by
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
theorem thm_5_vars_185967448439474356900642698337 : (((p1 ∧ (p1 ∧ (p5 ∧ (((p4 ∨ p2) → p1) ∨ True)))) ∧ p5) → ((((p3 → p4) ∨ p5) ∨ (False ∧ (((p1 → p4) ∨ True) ∧ p1))) ∨ False)) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h8 := h7.left
  let h9 := h7.right
  -- Disjunctions on the left can always be decomposed.
  cases h9
  case inl h10 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h11 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341702443900429673936509498367 : (p2 → (((p5 ∧ (((((p2 ∧ (p5 → False)) ∧ p2) → False) ∧ (p5 → (p2 ∧ (p5 ∨ True)))) ∨ True)) ∨ (p1 ∧ (False ∨ p4))) ∨ (p2 ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165853556482618646686792861379 : (((True ∧ (p3 ∨ p2)) ∨ ((p5 ∨ (p3 → True)) ∧ (p5 ∧ (p1 → (p4 ∨ (True ∧ p2)))))) ∨ (True ∧ ((p1 ∨ p3) → ((p4 ∧ p4) → True)))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159034089218859991806528076206 : ((p4 ∨ (p2 ∨ (((((p2 ∧ p1) → ((p3 ∧ (p1 → False)) ∧ p4)) ∧ True) ∨ (p3 ∨ p1)) → p1))) ∨ ((p4 ∨ p5) → ((p4 ∨ p5) ∨ p1))) := by
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
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_21784519402657381688755335409 : (((False → (((p2 ∧ p4) ∧ (p5 → p2)) ∧ (p2 ∧ p3))) → ((p2 ∨ False) ∨ ((p5 → p2) → (((False ∧ p4) ∨ p5) → (p2 ∨ p1))))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- False on the left can always be used.
    apply False.elim h5
  case inr h7 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h8 : p5 := by
      -- One of the premise coincides with the conclusion.
      exact h7
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h9 := h2 h8
    -- One of the premise coincides with the conclusion.
    exact h9
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263083312482904348178495453492 : (True ∧ ((((p1 → p4) ∧ ((((p2 ∨ (((p3 → p3) → False) ∨ p2)) → p2) ∧ (p5 ∧ p3)) ∨ ((False → True) → p1))) ∨ False) ∨ (p1 → True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116377464090473865722176477056 : ((((False → True) → p5) → (((p4 → p1) ∧ ((False → ((False ∨ (p5 ∧ p2)) ∧ ((False ∧ (p4 → False)) → p1))) → p1)) ∨ True)) ∨ (p4 ∨ p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_659207113539826273377288899545 : ((((p4 → ((False ∨ (((((p5 → p1) → p5) → (p4 ∧ ((True → p2) ∧ ((False ∨ True) → p1)))) → p1) ∧ p2)) ∨ p3)) ∨ (False → False)) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_148380739917533039745506225524 : ((((p3 → (((p5 ∧ (p2 ∨ p4)) → p1) ∧ p2)) ∧ ((p5 → False) ∨ p5)) ∨ ((p4 → p1) → (True ∧ False))) ∨ (((False ∧ p2) → False) ∨ p3)) := by
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
theorem thm_5_vars_158238225441557856083405754221 : ((((p1 ∧ False) ∧ p4) ∨ (((((p4 ∨ True) ∧ p3) → True) ∨ (p2 ∨ (p1 → (p3 ∨ p2)))) → False)) ∨ (((False ∧ p3) → True) ∨ (p5 ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164854625833798648544356017456 : (((False ∨ (((True ∨ True) ∧ (p1 → ((p3 ∨ (p1 ∨ p5)) ∨ p1))) ∧ (p2 ∨ p2))) ∨ p3) ∨ ((p4 → (p1 → p4)) ∨ (p2 ∨ (p2 ∧ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_353201367334571702085496534548 : (p4 → (p4 ∧ ((p2 → p4) ∧ ((((p4 ∨ True) ∨ p4) ∨ (p4 ∨ (p2 ∧ (p5 → ((p4 → p3) ∨ ((p5 → p3) ∨ False)))))) → (False ∨ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
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
    case inr h8 =>
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
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_492866778936337166571466312616 : ((((False ∨ ((p1 ∧ p4) ∨ p5)) ∨ ((True ∧ ((p1 → (p5 ∨ ((p1 → p1) ∨ p4))) ∧ (p3 → p3))) → (p5 → ((p2 → p1) ∨ p5)))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_679865128465611050576032269669 : (((((p4 → (((p2 → p3) → ((False → (p3 ∨ (False → False))) → p5)) → ((False → p5) ∧ p2))) ∨ p5) → (((p2 ∧ p3) ∧ p1) ∨ True)) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_595397121431390381998539925322 : (((((p1 → (p3 ∨ (p5 ∧ ((p5 ∨ p1) → (True ∧ (False ∧ p5)))))) ∧ ((True → (((p2 → (p4 ∨ p1)) → p4) ∧ p3)) ∧ p5)) ∧ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_125070737736597727909899195699 : (((p5 ∧ (p4 → False)) ∧ (p1 → (((True ∧ ((p4 ∨ True) → (((p1 ∧ p4) ∨ False) → (False ∧ p2)))) → False) → (p1 ∨ p1)))) → (p4 → False)) := by
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
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h7 : p4 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h8 := h6 h7
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_597116166989489170348513048280 : (((((p5 ∨ ((p5 ∨ (p2 → p5)) → p4)) → (p5 → ((p1 ∨ True) ∧ (((p2 → True) → p1) ∨ (True ∧ (False → (p3 ∨ p3))))))) ∧ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60637826639993554498312082016 : ((True ∧ (((p3 ∧ ((True → (p1 ∧ p4)) ∧ ((p5 ∧ (((p2 ∨ (p1 ∨ p5)) ∨ p5) → p4)) ∨ True))) ∧ p5) ∨ (p5 → (p4 → False)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303176372773809767053525293891 : (False ∨ (p4 → (((((p2 → True) ∨ ((p3 ∧ False) ∧ (p3 ∧ (((p1 ∨ (p5 ∨ (p5 ∧ p1))) ∧ p2) ∨ p2)))) → p2) → p3) ∨ (p2 → True)))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41034471114674641351220015727 : ((((((p1 → ((p5 ∨ (p4 ∧ ((p1 ∨ (p1 ∨ p3)) ∨ p1))) ∨ True)) → p4) ∧ ((p3 → (p3 → True)) ∨ p1)) → (p3 → p4)) ∨ p3) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h6 : (p1 → ((p5 ∨ (p4 ∧ ((p1 ∨ (p1 ∨ p3)) ∨ p1))) ∨ True)) := by
      -- Implications on the right can always be decomposed.
      intro h7
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h8 := h3 h6
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h10 : (p1 → ((p5 ∨ (p4 ∧ ((p1 ∨ (p1 ∨ p3)) ∨ p1))) ∨ True)) := by
      -- Implications on the right can always be decomposed.
      intro h11
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h12 := h3 h10
    -- One of the premise coincides with the conclusion.
    exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_629797553202864356628880093476 : ((((((False ∨ ((p1 ∧ p4) ∨ (p5 → ((True → (p1 ∨ p5)) ∧ p1)))) ∨ (p3 → (p4 ∨ ((False ∧ (p2 → p4)) → p3)))) ∨ p5) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_653058755808563497185473541924 : ((((True → ((((True ∧ (p2 ∨ False)) ∨ False) ∨ ((p5 → p2) → p3)) ∧ (True → (p3 → (p1 ∨ (p4 ∨ (p2 ∨ p1))))))) ∧ (p3 → p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47037570162386465446437913880 : ((((((p2 ∨ (False ∨ (((False ∧ (False → p2)) ∧ (p2 ∧ p4)) ∧ (True ∧ True)))) ∨ p4) ∧ (p4 ∨ p2)) ∧ (p3 → True)) ∨ (p1 ∨ True)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246731443438171084453765828877 : ((p5 ∧ p4) ∨ (p5 → ((((p4 ∧ p5) ∧ p3) ∨ (p1 ∨ (((False ∧ (p1 → p2)) ∨ p1) → (p1 → ((p1 ∧ (True ∧ p1)) ∨ p2))))) ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- False on the left can always be used.
    apply False.elim h5
  case inr h7 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h7
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119250126582744223896870217761 : ((p2 → (p1 ∨ ((((True → ((p4 → True) ∨ (((True → p2) → ((True ∧ p2) ∧ (p5 → p5))) ∧ False))) → p5) ∨ p2) ∨ p5))) ∨ (p1 ∧ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_648158852305271466270444621463 : ((((((True → p3) → (p5 → ((p2 ∨ ((((p2 ∧ p1) ∧ True) ∨ p3) → ((p5 ∧ p2) ∧ p5))) ∨ (False ∨ p2)))) ∧ p2) ∧ (p3 → True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_642221533341696580853557620777 : ((((True ∧ (p1 ∨ (((p1 → ((p5 → p4) ∨ (p5 → (p3 ∧ ((p3 ∧ p3) → False))))) ∧ (True ∧ ((p4 → p2) → p2))) ∨ p2))) → p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_805286981865620371697858466111 : (((p3 → (p5 ∧ ((p5 ∨ ((((p1 ∧ p3) ∨ p5) → p2) → (p2 ∧ ((p3 ∧ (p5 ∨ (p3 ∨ p3))) → p1)))) ∧ ((p2 ∨ p4) → p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_792043101820474797689361135296 : (((True → ((((True ∧ (((p2 → p4) ∨ p2) ∨ (p2 ∧ (p2 ∧ (p1 → (p5 ∧ (p4 → p3))))))) → False) ∧ p4) ∧ (p3 ∨ (p2 ∧ p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161585460496856060818686388956 : ((True ∨ (((p2 ∨ p5) ∨ True) → ((p5 → p5) → ((p1 → (((p1 ∨ p1) → p4) ∨ p5)) ∨ p2)))) → (((p5 ∨ True) → p2) ∨ (False → p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_653659316606340460408642406827 : ((((((True → ((p3 ∨ p5) ∧ (True ∧ ((False → ((((p4 ∨ p4) ∧ p3) ∨ (p1 ∧ p4)) ∨ True)) ∧ p1)))) ∨ p4) ∧ False) ∨ (p5 → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_798941555330932764570235294711 : (((p1 → ((p2 ∧ True) ∨ ((((p1 → (p3 ∨ ((((p4 ∨ p5) ∧ (p3 → p4)) ∨ p4) ∧ p2))) ∨ p2) ∧ p5) ∨ (False ∨ (p2 ∨ p1))))) ∨ p2) ∧ True) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260968009971067481266279685971 : ((p4 → p1) → ((((((p2 → (p4 ∨ ((p2 ∧ p5) ∧ False))) → p4) ∧ True) ∨ p2) ∧ (p4 ∧ (p3 → True))) ∨ (p2 → (p2 ∨ (True ∧ p2))))) := by
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
theorem thm_5_vars_52886703980117145603071980310 : (((p2 ∨ ((p1 → ((p3 → ((True → p4) ∨ (p4 ∨ p4))) ∧ p5)) ∧ True)) → (((((True ∨ p4) ∨ (p2 ∧ False)) → True) ∧ p2) ∧ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138058442622965817212301437308 : ((True → (p3 ∧ (p4 ∨ (((((p4 ∨ p4) ∨ p3) ∧ True) ∨ ((((p5 ∨ (p4 ∧ p5)) ∨ p4) ∧ p2) ∧ True)) ∨ p5)))) ∨ ((p1 ∧ False) → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_195440177416264179824960926104 : ((((p1 → p4) ∧ p5) ∨ ((p5 → p2) → True)) ∧ (p5 → ((p3 ∨ (p1 ∨ True)) ∧ ((((p4 ∨ (p1 → (p3 ∧ p4))) → False) ∧ False) ∨ True)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_666419020660956355466045843009 : (((((((p4 ∧ (p4 ∨ (p5 ∨ ((p5 ∧ p1) ∨ ((False ∧ True) ∧ False))))) → p3) ∨ p5) → ((p5 ∧ p4) ∨ p2)) ∧ (True ∧ (True ∨ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149805912863458862344109370581 : ((False ∨ (p3 ∨ (((p5 ∨ p1) → (p3 → p2)) ∧ (((p1 ∧ p3) → (True ∨ ((p4 ∨ p4) → p1))) → p1)))) ∨ (p3 ∨ ((p2 → p4) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_27753749223336040464674890909 : (((p3 ∨ p4) → (((((p3 → False) → (p5 ∨ (((p3 → (True ∨ p2)) ∧ (p4 → p5)) ∨ p2))) ∨ ((True → p1) → p1)) ∨ False) ∨ p1)) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h4 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h5 := h3 h4
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h8 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h9 := h7 h8
    -- One of the premise coincides with the conclusion.
    exact h9
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_613060821137400055677227980870 : (((((((((p1 ∨ p4) → p5) ∧ True) ∨ (((p1 → False) ∧ True) → (True ∧ ((False ∨ p5) ∨ (p3 → p5))))) ∨ p5) → (p3 → False)) ∨ True) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_758523908180355530533211431323 : (((p2 ∧ ((p5 → ((p5 ∧ (p4 → ((((False → (p5 ∨ False)) → p3) ∨ p3) ∨ (p2 ∨ (p3 ∧ p1))))) ∧ ((False → p5) ∧ p1))) ∧ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42417511040617677068172919263 : (((p5 ∧ ((p2 ∨ ((p2 ∨ (False ∨ True)) ∨ ((p1 ∧ p5) ∨ (((p1 → (p3 → (p2 ∧ True))) → (p5 → False)) ∨ True)))) → p2)) ∨ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232998461190754500981847953942 : ((p3 ∧ (p5 → p3)) → ((((False ∧ False) ∧ (p5 → False)) ∧ (True ∧ (p3 ∧ p2))) ∨ (True ∨ (p4 → (((p4 ∧ p2) ∨ p4) ∨ (p3 → p4)))))) := by
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
theorem thm_5_vars_315126272922924511320703159617 : (p3 ∨ (((p4 ∧ p4) ∨ ((p5 → p3) ∨ False)) ∨ (((False ∨ (p2 ∨ (((p3 ∨ (p5 ∨ (False → p4))) ∧ p2) → False))) ∧ p4) ∨ (False ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356609514849388550098241043437 : (p5 → ((p4 → (((p3 → False) → (p4 → False)) ∨ p5)) ∧ ((p2 ∧ p3) ∨ ((p3 ∧ (p1 ∧ p2)) ∨ ((True → (p1 ∨ False)) ∨ (p2 ∨ p5)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60308123167863580279751040532 : (((p1 → p3) → ((p5 ∨ ((p2 ∨ (((p4 ∧ (p2 → p3)) → p3) → ((p3 ∨ p5) → p5))) → p1)) → ((p5 → (p1 ∧ p3)) ∨ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67374992383688164588803014646 : ((p1 → ((((p3 → True) → (p2 ∨ (p3 ∨ (p5 → (((p3 ∧ p1) ∧ False) ∨ (p3 ∨ (p3 ∨ p4))))))) ∧ (p5 → (p1 → False))) → p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133755667238494022049572375203 : (((((False ∧ (p5 ∨ False)) ∨ (False ∨ False)) ∧ ((((False → p2) ∧ p1) ∨ (((p5 ∧ False) ∧ p5) → p3)) ∨ True)) ∧ p1) ∨ (False → (True ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_262130954974817623782812050942 : (True ∧ (((p3 ∨ ((((p1 ∨ (((p1 → ((((p5 ∨ p3) → p2) ∨ p2) ∧ p4)) → (p2 → p1)) ∧ True)) → p3) ∨ p1) → p2)) ∧ p1) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_609449772094701480949466088293 : (((((True ∧ ((p1 ∧ False) ∨ (p4 → (p2 ∨ ((p2 ∧ (p3 ∧ (p3 → p2))) ∧ ((((p3 ∨ p1) ∨ p4) ∧ p5) → True)))))) ∨ p5) ∨ True) ∨ False) ∧ True) := by
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
theorem thm_5_vars_157676013573718002538046633918 : ((((p4 ∨ False) ∧ (p4 ∧ (((p1 ∨ ((p3 → True) ∨ p3)) ∧ p2) ∨ p5))) ∨ (True ∨ (p1 ∧ p2))) ∨ ((True ∧ p3) ∧ (p3 ∧ (False ∨ p1)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_612924127789549626696828315630 : (((((p5 ∨ (((((False → ((p1 ∨ ((True ∧ (True ∧ p2)) ∧ (p2 → p1))) ∨ p2)) → p4) → p2) ∨ False) ∨ False)) ∨ (True ∧ p3)) ∨ True) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_261652318443044845034630528987 : ((p5 → p5) → ((p1 ∨ p2) ∨ ((((True ∧ (((p5 → (p2 ∧ True)) ∨ p5) ∨ ((p3 ∧ p3) ∧ ((p5 ∨ p4) → False)))) ∨ p5) ∨ True) ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340169322806038425181666790562 : (p1 → (p4 → (((p4 → ((False → (p1 ∨ (p4 → p5))) → (p3 ∧ ((True ∨ True) → p3)))) → p4) → (((p3 → (p4 ∧ False)) ∧ True) ∨ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_670546169082243018253475199238 : (((((p4 ∧ False) ∨ ((((((p5 ∨ (p2 → p3)) → p5) → p5) ∧ (p1 ∧ True)) → (p2 → (False ∧ p1))) ∨ p1)) ∨ (p2 ∧ (p1 ∨ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_327463584800650095227616711183 : (True → (((((p3 ∨ False) → (p2 ∨ (p3 ∨ (p1 ∨ p1)))) ∨ p4) → ((((((True ∨ p4) → True) → True) ∨ p5) ∨ (p4 → p4)) ∧ False)) → False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (((p3 ∨ False) → (p2 ∨ (p3 ∨ (p1 ∨ p1)))) ∨ p4) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h4
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h6 =>
      -- False on the left can always be used.
      apply False.elim h6
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h7 := h2 h3
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_731944102007276821217940719838 : ((((p5 → (False → p1)) → ((((False → p4) ∨ (p2 ∨ (p2 ∧ (True ∨ p1)))) ∨ p3) → (False ∨ (True → (((p4 ∧ True) → p1) ∧ False))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147575481553380642963740487321 : (((((p2 ∧ p5) ∨ (True ∨ (p4 → (p5 ∨ ((p5 → False) ∧ ((p1 → p5) → (p4 ∨ False))))))) ∧ p1) → False) ∨ (((p4 ∧ p4) ∧ p1) → p1)) := by
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
theorem thm_5_vars_614959083367623919786388337440 : (((((((p3 → (((p2 → False) → p5) ∧ (p5 ∨ (p2 → p4)))) ∧ p1) ∨ (True ∧ (p3 ∧ p5))) → ((p3 ∨ p3) ∨ (True → p2))) ∨ True) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_164637542527666654662914322179 : (((p3 ∨ ((((p1 ∨ p3) ∨ p5) ∧ p5) ∧ (p2 → (((p5 ∧ True) ∨ p5) ∨ p1)))) ∧ p4) ∨ ((p1 → ((p4 → (p2 ∨ p1)) → p1)) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_689526658255070691486204486055 : (((((((p3 ∨ True) ∧ (p5 ∨ (p1 ∨ p5))) ∧ False) ∨ ((False → False) ∨ (False ∨ p4))) ∨ (((True ∨ True) ∨ ((True ∨ p1) ∧ p5)) ∧ p4)) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_917749798263699815174635181020 : (((((p5 ∧ (False ∧ ((p3 ∧ p1) ∨ True))) → (p1 ∨ ((p4 ∧ (p3 → p3)) ∨ p1))) → ((p1 ∧ (p4 ∨ (p2 ∨ (p4 ∨ True)))) ∧ p2)) → p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p5 ∧ (False ∧ ((p3 ∧ p1) ∨ True))) → (p1 ∨ ((p4 ∧ (p3 → p3)) ∨ p1))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- False on the left can always be used.
    apply False.elim h6
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h8 := h1 h2
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- One of the premise coincides with the conclusion.
  exact h9
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68228603696741340340097025598 : ((p3 → ((((((((p2 → p4) → (True ∨ False)) → (p5 → p4)) → p1) ∨ True) ∨ p1) → ((True ∧ (True → (p3 ∨ p2))) → p5)) → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218869393283974057674026083911 : ((p2 ∧ (p1 ∨ (p3 → p3))) → (((((p3 ∧ (((False → False) ∧ True) ∨ True)) ∧ ((p2 → False) ∨ False)) ∧ True) ∨ (False → p5)) ∨ (p5 → True))) := by
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
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60854993105670460727005084795 : ((True ∧ (p4 ∨ ((p3 → (((p1 → (p2 → (p1 ∨ ((p5 ∨ p4) ∧ (p1 ∧ False))))) ∧ (p1 → ((False ∨ False) ∧ p3))) ∨ p1)) ∧ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258050424346411683843537835486 : ((p4 ∨ p2) → ((((((((p2 → ((False ∨ (True → p3)) ∧ p2)) ∨ p4) → p2) ∨ (True → p3)) ∨ True) ∨ p4) ∨ p3) ∨ (p3 ∨ (p2 ∧ p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
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
theorem thm_5_vars_135328599078796003485839523988 : ((((((p5 → (p2 ∨ p3)) ∧ p2) ∨ p4) ∧ (p1 ∨ (((p1 ∨ p5) → (p2 → p4)) → True))) ∧ (p1 ∧ (p3 ∨ p4))) ∨ (p5 → (p1 ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_602619706327231531085303568636 : ((((False ∨ (((p4 ∨ (p4 ∨ (True ∧ ((p1 ∧ (p5 → p2)) ∧ (((p3 → p4) ∨ p4) ∨ (False → p1)))))) → p2) ∨ (True → False))) ∧ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_221351231352403518730629675291 : (((p5 ∨ True) ∨ p1) ∧ ((((p3 ∨ (True ∨ p1)) ∧ (p2 ∧ True)) ∨ (p3 ∧ (((p1 → p4) → ((False → p1) ∨ p3)) ∧ p3))) ∨ (p3 ∨ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_622509581396669838090019451392 : ((((p3 ∧ (p5 ∨ ((False ∨ ((p3 ∧ (False ∧ True)) ∨ p2)) ∨ (True → ((p4 ∨ (p1 ∨ (True ∧ (p2 ∧ (True ∧ True))))) ∨ p5))))) ∨ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51009321137318815369233837469 : (((True ∧ ((p2 ∧ (((p5 ∧ (p2 ∧ p2)) → p5) → (p5 → ((False ∧ p5) ∨ False)))) ∨ True)) ∧ (p4 ∨ ((p4 → (p2 → True)) ∨ p1))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319302332521325253287573452108 : (p4 ∨ (((False ∨ ((p4 ∧ ((p5 ∨ (p2 ∨ p2)) ∨ (p3 → (p5 → p1)))) ∨ p5)) → True) → (p1 → (p3 → (True ∧ ((p5 ∨ p1) ∨ True)))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178143686182451098974017914311 : (((((p4 ∨ p3) ∨ p5) ∧ ((p5 ∨ p2) ∨ (p3 ∨ (p2 ∧ p4)))) → p3) ∨ (((p4 ∨ p4) ∧ (p4 ∨ (True ∨ (p2 ∨ (False → p5))))) → p4)) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h5 =>
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- One of the premise coincides with the conclusion.
        exact h4
      case inr h8 =>
        -- Disjunctions on the left can always be decomposed.
        cases h8
        case inl h9 =>
          -- One of the premise coincides with the conclusion.
          exact h4
        case inr h10 =>
          -- One of the premise coincides with the conclusion.
          exact h4
  case inr h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h12 =>
      -- One of the premise coincides with the conclusion.
      exact h12
    case inr h13 =>
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h14 =>
        -- One of the premise coincides with the conclusion.
        exact h11
      case inr h15 =>
        -- Disjunctions on the left can always be decomposed.
        cases h15
        case inl h16 =>
          -- One of the premise coincides with the conclusion.
          exact h11
        case inr h17 =>
          -- One of the premise coincides with the conclusion.
          exact h11



