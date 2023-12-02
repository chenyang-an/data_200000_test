variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_77087335306608560310670794898 : (((((p4 → (p3 ∧ p4)) ∧ p4) ∨ ((((p3 ∨ ((p5 → ((False ∧ p4) ∨ ((p2 ∨ False) → p2))) ∨ p4)) → False) ∧ p1) → p4)) → False) → p4) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p4 → (p3 ∧ p4)) ∧ p4) ∨ ((((p3 ∨ ((p5 → ((False ∧ p4) ∨ ((p2 ∨ False) → p2))) ∨ p4)) → False) ∧ p1) → p4)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h6 : (p3 ∨ ((p5 → ((False ∧ p4) ∨ ((p2 ∨ False) → p2))) ∨ p4)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h7
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- One of the premise coincides with the conclusion.
        exact h9
      case inr h10 =>
        -- False on the left can always be used.
        apply False.elim h10
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h11 := h4 h6
    -- False on the left can always be used.
    apply False.elim h11
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h12 := h1 h2
  -- False on the left can always be used.
  apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198163740595462708246858870717 : (((p1 ∨ p2) → (False ∨ (p3 ∨ (p5 ∧ True)))) ∨ ((p4 → p5) → ((p3 ∧ (p2 ∧ ((False → p3) ∧ ((True → (p1 ∨ p2)) ∨ p2)))) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166655821799496630932195809894 : ((p1 → ((p4 → True) → (p5 ∧ ((True → (p2 ∧ (False ∨ ((True ∨ p1) → p5)))) ∨ p5)))) ∨ (((p5 ∨ p2) ∧ True) → (p5 ∨ (p2 ∨ p4)))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54537968770769990012301365603 : ((((p2 ∨ p1) → (True → (p4 ∨ (True ∧ p2)))) ∨ (p4 → ((p5 → ((p2 ∧ (p3 ∧ p5)) ∨ (p5 → p5))) ∧ (False → (p3 ∨ p3))))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156956683805626554730048396621 : (((((((p4 ∧ (p5 ∧ p5)) ∨ p5) ∧ ((p3 → True) ∨ False)) → p2) ∨ ((p5 → p3) ∨ p2)) ∨ True) ∨ ((p5 → (p4 → True)) → (p4 ∧ False))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46055638425438299004433443826 : (((((False ∧ ((((p1 ∧ (p2 ∨ True)) ∨ (p2 ∧ (False ∨ p3))) ∧ ((p3 → (p5 ∧ True)) ∨ False)) ∨ p2)) ∧ p3) ∨ True) ∧ (p4 → p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345471043833531208885830465886 : (p3 → ((((p1 ∧ (((p2 ∧ ((p4 → True) ∧ (((p4 → True) → True) → p4))) → p2) → p4)) ∨ (False → False)) ∨ ((p1 ∧ p1) ∧ p1)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340101237526881669314354028312 : (p1 → (p3 → ((p4 → (p5 ∨ ((((p4 ∧ (True ∨ (p4 ∧ (p2 ∨ ((False ∨ True) ∧ True))))) ∧ p4) ∧ (p3 → False)) ∧ p5))) ∨ (True ∨ False)))) := by
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
theorem thm_5_vars_185202682612485851193626576407 : ((True ∧ ((p5 ∨ (p1 ∨ False)) → ((p5 ∧ p2) ∨ (p3 ∨ True)))) ∨ (((p4 ∧ p3) ∨ p5) ∨ ((p4 ∨ (((p2 ∨ p1) ∨ p3) → p4)) ∨ p2))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- False on the left can always be used.
      apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_686298342656487604334022548103 : (((((p2 ∨ (p5 → (((p4 ∨ p1) ∧ p4) → p4))) → (((p2 → p5) → (p2 ∨ p3)) ∧ False)) → (((p4 ∨ (p5 → p5)) ∨ p3) → p5)) ∨ p1) ∧ True) := by
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
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h5 : (p2 ∨ (p5 → (((p4 ∨ p1) ∧ p4) → p4))) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h6
        -- Implications on the right can always be decomposed.
        intro h7
        -- Conjunctions on the left can always be decomposed.
        let h8 := h7.left
        let h9 := h7.right
        -- Disjunctions on the left can always be decomposed.
        cases h8
        case inl h10 =>
          -- One of the premise coincides with the conclusion.
          exact h9
        case inr h11 =>
          -- One of the premise coincides with the conclusion.
          exact h9
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h12 := h1 h5
      -- We need to get the right conjuct of h12 based on <expert-advice>.
      let h13 := h12.right
      -- False on the left can always be used.
      apply False.elim h13
    case inr h14 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h15 : (p2 ∨ (p5 → (((p4 ∨ p1) ∧ p4) → p4))) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h16
        -- Implications on the right can always be decomposed.
        intro h17
        -- Conjunctions on the left can always be decomposed.
        let h18 := h17.left
        let h19 := h17.right
        -- Disjunctions on the left can always be decomposed.
        cases h18
        case inl h20 =>
          -- One of the premise coincides with the conclusion.
          exact h19
        case inr h21 =>
          -- One of the premise coincides with the conclusion.
          exact h19
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h22 := h1 h15
      -- We need to get the right conjuct of h22 based on <expert-advice>.
      let h23 := h22.right
      -- False on the left can always be used.
      apply False.elim h23
  case inr h24 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h25 : (p2 ∨ (p5 → (((p4 ∨ p1) ∧ p4) → p4))) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h26
      -- Implications on the right can always be decomposed.
      intro h27
      -- Conjunctions on the left can always be decomposed.
      let h28 := h27.left
      let h29 := h27.right
      -- Disjunctions on the left can always be decomposed.
      cases h28
      case inl h30 =>
        -- One of the premise coincides with the conclusion.
        exact h29
      case inr h31 =>
        -- One of the premise coincides with the conclusion.
        exact h29
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h32 := h1 h25
    -- We need to get the right conjuct of h32 based on <expert-advice>.
    let h33 := h32.right
    -- False on the left can always be used.
    apply False.elim h33
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137266419522417096435346397827 : ((p1 ∧ (p5 ∧ (((p3 → p3) → (p2 ∨ p1)) → (p2 → ((((False ∧ (False ∧ (p3 ∨ p4))) ∨ True) ∨ False) → False))))) ∨ ((p2 ∧ True) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_683678703910088587040759360305 : ((((((p3 → p3) → (((((p3 ∨ p2) → p1) → (True ∧ p1)) ∧ (p5 → p5)) ∨ False)) ∧ True) ∨ (False → ((p4 ∧ (p3 ∧ p2)) ∧ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136989533143733380291824689739 : (((p5 ∧ p1) → ((p3 ∨ (((True ∨ p4) → (True ∨ (p5 ∧ ((False ∨ True) → p5)))) ∧ (p5 ∧ True))) → (p4 → False))) ∨ ((True → p2) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42909041110098007347673963312 : (((p3 → (p1 ∧ (((False ∧ (True ∧ p4)) → p3) → ((False ∨ ((p5 ∨ (p5 → p4)) ∨ (p2 ∧ p3))) → ((p3 → p5) → False))))) ∨ True) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59955168896681471113050606459 : (((True ∨ p3) → ((True ∧ False) ∨ ((False → (p2 ∨ (p4 ∧ (p2 ∨ ((p4 ∧ p3) ∧ (((True → (p5 → p2)) ∧ p4) ∨ p1)))))) → p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_937012074486060777748744277042 : (((((False ∨ ((True ∨ p2) ∨ p1)) → False) ∧ ((False → (False ∧ (p1 ∧ (((p2 ∧ p2) → (False ∨ (True → p2))) ∨ p1)))) ∧ (True ∨ p3))) → p4) ∧ True) := by
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
  cases h5
  case inl h6 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h7 : (False ∨ ((True ∨ p2) ∨ p1)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h8 := h2 h7
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h10 : (False ∨ ((True ∨ p2) ∨ p1)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h11 := h2 h10
    -- False on the left can always be used.
    apply False.elim h11
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215908615392380734155910345901 : ((p3 ∨ ((p1 → False) → p1)) ∨ (((p1 ∨ True) ∧ p1) ∨ (((p4 ∨ ((((((p3 ∨ p2) → p4) → p3) ∨ p1) ∨ p5) ∨ p3)) ∨ p4) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61390130883642674893021676378 : ((p1 ∧ ((((p2 → ((True ∧ p4) ∨ (p5 ∨ False))) → p5) ∨ (True ∧ (((p4 → (p5 ∨ p3)) → p3) → (p3 ∨ (False → p3))))) ∨ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118126213795218445919243639887 : ((False ∨ (((p1 → p5) ∧ (((p3 → (p1 → (True ∨ True))) → (True ∧ ((p5 → (p1 ∧ True)) → True))) → False)) ∨ (False → p5))) ∨ (True → p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245013004408151619446589375456 : ((p1 ∧ p4) ∨ ((p2 → p3) ∨ (p2 → (((((((p1 ∨ p4) → (False ∧ True)) ∧ p2) → ((True ∨ p2) ∧ p1)) ∧ (False ∧ False)) ∧ p2) ∨ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_125540390537362733050407662687 : (((True → p5) ∧ ((p2 ∧ ((p1 → ((False ∨ (p4 ∧ (p1 ∧ p1))) ∧ (p1 ∧ p2))) ∧ (((p2 → True) → False) ∨ p2))) → p4)) → (p4 → p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h5 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h5
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118813834043588199595425682007 : ((True → ((((p2 ∧ p3) ∧ (p2 ∨ p3)) ∨ (p3 ∧ (((p3 → p3) → False) → (p2 ∧ ((True ∧ p1) ∨ (False → p4)))))) ∨ p4)) ∨ (p4 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68400432959266304835011754433 : ((p3 → (((False → p3) ∧ p4) → (((((True ∨ p4) ∧ (p3 → ((False ∨ p3) → (False ∧ p4)))) → ((p1 ∧ p3) ∨ p5)) ∨ p2) ∨ p4))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47392308909420637307223954491 : ((((p3 → p2) → ((((False ∧ p2) ∨ ((False ∨ True) ∧ (((False ∧ True) ∨ p2) ∧ p2))) → (p1 ∧ p4)) ∧ (p1 ∨ p4))) ∨ (p4 ∧ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159085893307614827699450294346 : ((True → (((p3 ∧ (((False ∨ p5) → (p3 ∧ False)) → p1)) ∨ ((False ∧ (p2 ∨ p5)) → p1)) → p2)) ∨ ((p1 ∧ p3) ∨ (p4 ∨ (False ∨ True)))) := by
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
theorem thm_5_vars_622480128083093214474057047922 : ((((p3 ∧ (p4 ∧ ((p5 → (True ∨ ((p5 ∧ False) → (True → False)))) → ((p2 → p4) ∨ (((p5 ∧ (p4 ∧ p1)) → p3) ∧ p4))))) ∨ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_596189308127700520741048839396 : ((((((False ∨ ((p3 ∨ (True ∨ p1)) ∧ p2)) → False) ∧ ((p2 ∨ ((p2 ∧ p2) → (p4 ∧ p3))) ∨ ((p1 ∨ False) ∨ (False ∨ False)))) ∧ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_603410100090803782220086983550 : ((((p3 ∨ ((p2 → (((p4 ∧ p2) ∧ (False ∧ (((p2 ∨ p4) → False) ∨ p1))) ∨ ((p4 ∨ (True ∧ (p3 → True))) ∨ p2))) ∨ p1)) ∧ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66372153493084230919867482340 : ((p5 ∨ (p2 ∨ (((((((p5 ∧ (False ∨ p4)) ∧ p5) ∧ p1) ∧ p3) ∨ (p5 ∧ p5)) ∧ True) ∨ (((p3 → (True ∨ p3)) ∧ True) ∨ False)))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347838731344321091314004569834 : (p3 → (((p4 ∧ p2) → False) → (p4 → ((((False → p5) → (p2 ∧ ((True ∧ (p1 ∨ (p2 ∧ p4))) ∧ p4))) ∨ (p2 ∧ p1)) ∨ (True → p3))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_398083428151760840593589742509 : ((((p4 ∨ ((p1 ∧ (p5 ∨ ((p2 → p2) ∧ (p4 → p2)))) → ((p2 ∨ (p2 ∧ (((False → True) ∨ (p4 → p2)) → p5))) → p5))) ∨ True) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40022100573456397899890181857 : (((((((p1 ∨ ((p3 ∧ ((True ∧ p4) ∧ ((True ∨ False) ∧ ((p1 ∧ p4) ∧ p2)))) ∧ (p1 ∨ p1))) ∨ p4) ∧ p3) ∧ p5) ∧ p4) ∨ True) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_21094320549843179998819242363 : ((((False → p3) ∧ (((p2 ∨ ((p4 ∧ False) ∨ p5)) ∨ p5) ∧ p4)) → (((((p2 → p4) ∧ (True ∧ p4)) → (False → True)) → p5) ∨ p4)) ∧ True) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Conjunctions on the left can always be decomposed.
        let h10 := h9.left
        let h11 := h9.right
        -- False on the left can always be used.
        apply False.elim h11
      case inr h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h5
  case inr h13 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116622691671948120504466937348 : (((False → p4) ∧ ((p2 → ((((p3 → ((p2 → False) ∨ (((p4 ∨ False) ∨ p5) ∨ True))) ∧ True) → p5) ∨ True)) ∨ (p1 ∨ p5))) ∨ (p1 ∨ p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62072084858491389933907458187 : ((p2 ∧ (False ∧ (False ∧ (((((False → p2) ∧ p1) ∨ (p3 ∨ p2)) ∧ (True ∨ (False ∨ (False → ((p1 ∧ (p5 ∨ p1)) ∨ True))))) ∧ p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51497070536572525190654020518 : (((((p5 → p4) ∧ p4) ∧ ((((False ∧ True) → p2) ∨ (p3 ∨ p1)) ∨ (False ∧ (p4 ∨ p2)))) → (((p1 ∨ p2) ∨ p3) ∨ (p1 → p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_779998056839896491373176957088 : (((p2 ∨ (((p1 ∨ (((p1 ∨ (((p1 ∧ (p5 ∧ False)) ∧ (p4 ∨ (False ∧ True))) ∧ (p5 ∨ p1))) ∧ p2) ∨ p1)) ∨ p4) ∨ (p1 ∨ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_737885014388360086298028860819 : ((((True ∧ p2) ∨ ((p4 → ((p3 ∨ (((p1 ∧ p4) → ((p2 ∧ False) → p5)) ∨ True)) → (p2 → (p4 ∧ True)))) → (False ∨ (p3 → False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40035328919153316658676546871 : (((((((p2 ∨ (p3 ∨ True)) ∨ (p5 ∧ False)) ∧ ((p5 ∨ p2) ∧ ((p4 ∧ p1) ∨ (p1 → ((p1 → p2) → False))))) ∧ p4) ∧ False) ∨ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172332618559085542353292670698 : ((((False ∧ (p3 ∧ True)) ∨ (p1 ∧ p1)) ∧ (((False ∨ p4) ∨ (False → False)) ∧ p3)) ∨ ((p3 → (p4 ∨ (False ∧ (True → p3)))) → (True ∧ True))) := by
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
theorem thm_5_vars_148723042419348755029842053286 : (((False ∨ ((False ∨ ((p5 ∨ False) ∧ p4)) → p1)) → (((p1 → ((p5 ∨ False) ∧ (False → True))) ∧ False) ∨ True)) ∨ (p5 ∧ (p1 ∧ (False ∧ p3)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- False on the left can always be used.
    apply False.elim h2
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135082499216952948651188245424 : (((((p5 ∧ (((p4 ∨ True) ∨ p3) → (False ∨ (True ∨ (False ∨ False))))) → p4) → ((p3 ∧ p4) ∨ p4)) ∨ (p2 ∨ True)) ∨ (p3 ∧ (p5 ∨ p5))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228576585240611353539664371002 : ((p1 ∨ (p3 ∨ False)) ∨ (p3 ∨ (p4 → (((False ∨ (False ∨ p5)) ∨ ((False → (p1 ∨ False)) → p4)) ∨ (((True ∨ False) ∨ (p3 ∨ True)) ∧ p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54486467746007253662707949530 : ((((((p4 ∧ p3) → p4) ∨ p4) → (False ∧ p5)) ∨ (p4 ∨ (p2 → (p5 → (True ∧ ((p5 ∨ (((False ∧ p5) ∧ p4) ∧ True)) ∨ p3)))))) ∨ p1) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_78673592628040453372640635010 : (((((((p2 ∧ p4) → False) ∨ False) ∨ (p2 ∨ (((False ∨ (p3 ∨ p3)) → p2) ∧ p1))) ∧ (True → ((p1 ∧ False) ∧ False))) ∧ (p3 → p2)) → False) := by
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
    cases h6
    case inl h7 =>
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h8 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h9 := h5 h8
      -- We need to get the right conjuct of h9 based on <expert-advice>.
      let h10 := h9.right
      -- False on the left can always be used.
      apply False.elim h10
    case inr h11 =>
      -- False on the left can always be used.
      apply False.elim h11
  case inr h12 =>
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h13 =>
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h14 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h15 := h5 h14
      -- We need to get the right conjuct of h15 based on <expert-advice>.
      let h16 := h15.right
      -- False on the left can always be used.
      apply False.elim h16
    case inr h17 =>
      -- Conjunctions on the left can always be decomposed.
      let h18 := h17.left
      let h19 := h17.right
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h20 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h21 := h5 h20
      -- We need to get the right conjuct of h21 based on <expert-advice>.
      let h22 := h21.right
      -- False on the left can always be used.
      apply False.elim h22



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_639729873177387284916704584378 : (((((p1 → (p5 → p5)) ∧ (((((p4 ∧ p1) → p5) ∧ (((p4 ∨ False) ∧ p2) ∧ (False ∧ p2))) ∧ True) → (p5 ∨ (False ∧ False)))) → p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328279034027719640202157745960 : (True → (((((p3 → p5) → ((False → (((p2 → ((False → p1) ∨ p2)) ∨ True) ∨ p3)) ∨ p1)) → p5) → p4) ∨ ((False ∧ p3) ∨ (p4 → True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150744596044634018916713644966 : (((((((((p3 ∧ False) → p4) ∧ p5) → p2) → (p1 ∧ p3)) ∨ ((p5 ∨ (True ∧ p4)) ∨ p2)) ∨ True) ∨ p3) → (False ∨ ((False → p2) → True))) := by
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
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h5
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
            -- Implications on the right can always be decomposed.
            intro h9
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h10 =>
            -- Conjunctions on the left can always be decomposed.
            let h11 := h10.left
            let h12 := h10.right
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h13
            -- True on the right can always be proven directly.
            apply True.intro
        case inr h14 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h15
          -- True on the right can always be proven directly.
          apply True.intro
    case inr h16 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h17
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h18 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h19
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65926390401048094280079905041 : ((p4 ∨ (p5 ∧ (p2 ∧ (p4 → (((p1 ∧ p3) ∧ (p5 ∨ p5)) → (p4 → ((False → (False ∧ False)) ∧ (p5 → ((p2 ∨ p4) ∧ p2))))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_710786794778732917574894870347 : (((((False → (p3 → False)) → (p5 → True)) ∧ ((((p2 → p3) → (((False → False) ∧ p2) ∨ (p1 → (p5 ∨ False)))) → p3) → (False ∨ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336379794452606353413929275703 : (p1 → ((False ∧ (((p2 ∧ ((p4 ∨ p5) → p2)) ∧ (False ∨ ((((False → ((p4 → p4) ∨ p2)) ∧ p5) → p2) → False))) ∧ (p1 ∨ False))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_647034536993804325787150380266 : ((((p3 → ((((((p3 ∧ ((p2 ∧ ((p3 ∨ p4) ∧ True)) → False)) ∨ p1) ∧ (p3 ∨ False)) → (p5 ∧ True)) ∨ p3) ∨ (p4 ∧ p5))) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_624210438229140779630706959412 : ((((p3 ∨ ((p4 ∧ (((p5 → p5) ∨ (p5 ∨ ((False ∧ (True ∨ p4)) ∧ (p2 ∧ (False ∨ (False ∧ (p3 ∨ p1))))))) → p4)) ∧ p1)) ∨ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192092386261081780433347644021 : ((p4 → (((p1 ∧ p1) → (True ∧ (p1 ∨ p1))) → False)) ∨ (False → (p1 ∨ (p1 ∨ ((p1 → True) ∨ (p1 → (p1 ∧ (p4 → (p4 ∧ p2))))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110801060119140723720414063004 : (((((((True ∧ ((p2 ∨ ((p1 ∨ p3) ∧ ((p4 ∨ True) → False))) ∧ False)) → p3) ∧ True) ∧ (p2 ∨ (False ∨ p2))) ∨ p4) ∧ p3) ∨ (True ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225751768405452547530052366120 : (((p4 → p4) ∧ p5) ∨ (((((False → (p5 ∧ p4)) → (p2 ∨ (p4 ∨ (True → (p3 → False))))) ∨ (False ∨ p1)) ∨ p2) ∨ ((True ∧ p2) → p2))) := by
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
theorem thm_5_vars_234462749259955215312301326232 : ((p2 → (False ∨ True)) → (((((p5 ∨ p1) → p2) ∧ ((((True → p3) ∨ p3) ∧ (True → (p5 ∧ (p5 ∨ p2)))) ∨ False)) ∧ p4) → (p2 ∧ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h10 =>
      -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
      have h11 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h9, we can now drive its conclusion.
      let h12 := h9 h11
      -- We need to get the left conjuct of h12 based on <expert-advice>.
      let h13 := h12.left
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h14 : (p5 ∨ p1) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h13
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h15 := h5 h14
      -- One of the premise coincides with the conclusion.
      exact h15
    case inr h16 =>
      -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
      have h17 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h9, we can now drive its conclusion.
      let h18 := h9 h17
      -- We need to get the left conjuct of h18 based on <expert-advice>.
      let h19 := h18.left
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h20 : (p5 ∨ p1) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h19
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h21 := h5 h20
      -- One of the premise coincides with the conclusion.
      exact h21
  case inr h22 =>
    -- False on the left can always be used.
    apply False.elim h22
  -- Conjunctions on the left can always be decomposed.
  let h23 := h2.left
  let h24 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h25 := h23.left
  let h26 := h23.right
  -- Disjunctions on the left can always be decomposed.
  cases h26
  case inl h27 =>
    -- Conjunctions on the left can always be decomposed.
    let h28 := h27.left
    let h29 := h27.right
    -- Disjunctions on the left can always be decomposed.
    cases h28
    case inl h30 =>
      -- We want to use the implication h29 based on <expert-advice>. So we show its premise.
      have h31 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h29, we can now drive its conclusion.
      let h32 := h29 h31
      -- We need to get the left conjuct of h32 based on <expert-advice>.
      let h33 := h32.left
      -- One of the premise coincides with the conclusion.
      exact h33
    case inr h34 =>
      -- We want to use the implication h29 based on <expert-advice>. So we show its premise.
      have h35 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h29, we can now drive its conclusion.
      let h36 := h29 h35
      -- We need to get the left conjuct of h36 based on <expert-advice>.
      let h37 := h36.left
      -- One of the premise coincides with the conclusion.
      exact h37
  case inr h38 =>
    -- False on the left can always be used.
    apply False.elim h38



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44305479517443248493222904028 : ((((((((p2 ∨ ((p1 ∧ ((p2 → p3) → p1)) ∨ False)) ∧ p4) ∧ p4) → p3) ∧ p5) ∨ (((p3 ∨ p4) → (False → False)) ∨ False)) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_596741539013744815387211993492 : (((((p5 ∧ (((True → p5) → p5) → p1)) ∧ ((p3 ∨ (p1 ∨ (((False ∨ p4) ∨ ((p2 → p5) → (p5 ∧ True))) ∧ True))) ∧ p2)) ∧ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136546505765033831340615358522 : ((((p4 ∨ p4) ∧ p3) ∨ (((p1 ∨ ((((p4 ∨ True) ∨ p2) ∨ (p2 → p5)) ∧ p1)) ∧ p5) → (p4 ∨ (p1 ∨ p1)))) ∨ (p3 → (p4 ∨ p2))) := by
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
  cases h2
  case inl h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Disjunctions on the left can always be decomposed.
        cases h9
        case inl h10 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h10
        case inr h11 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h7
      case inr h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h7
    case inr h13 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49836358982961589736798615193 : (((p5 → ((((False ∧ p5) ∨ (p2 ∨ False)) ∨ ((p3 ∧ ((p1 ∧ ((p1 ∨ p5) ∨ p5)) → False)) → p1)) ∨ True)) → (p2 ∨ (p2 ∧ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314009331332821870947110543340 : (p3 ∨ ((p2 ∧ ((p5 ∨ False) ∧ (p1 ∨ ((((p2 ∧ ((p4 → p5) → p5)) ∨ ((p3 → p4) ∧ False)) ∨ (p5 ∨ True)) ∧ p2)))) ∨ (p5 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47114937291219735190535131726 : ((((((p5 ∧ (p3 → (False → (True → p2)))) → p5) ∧ (p5 ∧ ((p5 ∨ (False ∨ p2)) ∧ p3))) ∨ ((p5 → p3) ∨ True)) ∨ (p5 ∨ True)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_636360592723795831702887541234 : ((((((((True ∧ p3) → (False ∧ p5)) → p1) ∧ (True ∧ ((p4 → (p3 ∧ p5)) ∨ p1))) → ((p3 → (p2 ∨ p1)) ∨ (p4 ∨ True))) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300099337023853444679942897377 : (False ∨ ((((False ∨ True) → (((p1 ∧ (p1 → (True → p2))) → p2) → (p2 → (p3 ∧ p2)))) ∨ ((p5 → p1) ∨ (True ∨ True))) ∨ (True ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_163526303805720679265448625299 : ((((p2 ∧ p5) ∨ p5) → (((((True ∧ p3) ∨ (False → True)) → p1) ∧ (p4 ∨ p2)) ∨ True)) ∧ ((True ∨ (p3 → (p1 → (p3 → p2)))) ∨ p1)) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_221321380706697709185163479022 : (((p4 ∨ p1) ∨ True) ∧ ((True ∧ (((((p1 → p2) → (p2 ∧ p2)) → (((p3 ∨ (p4 ∨ p3)) ∨ p1) → p1)) ∨ (False ∧ False)) ∨ True)) ∨ False)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
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
theorem thm_5_vars_117159376516966279416192735933 : ((True ∧ ((((p2 ∨ (p5 → (False ∨ (p3 ∧ (p4 ∧ False))))) ∧ (False ∧ p3)) ∨ (p4 → (p5 ∨ (p1 ∨ (False → False))))) ∨ p2)) ∨ (p1 → False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_110822359810936315111298528926 : (((((p1 ∧ p2) ∧ ((p1 → ((p5 ∨ (False ∨ (p3 ∧ True))) ∨ False)) → ((p2 ∨ ((p2 ∧ p1) → False)) ∧ True))) ∨ p4) ∧ p4) ∨ (p1 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260011991408399103570381196267 : ((p2 → True) → ((False ∧ True) ∨ ((True ∨ p3) → (p5 ∨ ((False ∨ (p1 ∨ ((p5 ∧ (p5 → (True → (p5 ∧ (p2 ∨ False))))) → False))) ∨ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184157536445607919514524317958 : (((p3 ∨ (((False ∧ p1) ∧ p4) ∧ ((p3 → True) → p1))) ∨ p4) ∨ (((True ∧ (p2 ∧ (p3 → p3))) → (p3 ∧ (True → p1))) → (True ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_732836619182418649537400692721 : ((((p2 ∧ False) ∧ ((((False ∨ p3) → (p3 ∧ p4)) → (p3 ∨ (p3 ∨ (((False ∧ (p2 ∧ (True → (p1 → p5)))) → p5) → False)))) ∨ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_616252936112388376467016022350 : (((((((p3 → ((p1 ∨ p5) ∧ (p2 ∧ (p5 → p1)))) ∧ p5) ∨ False) ∨ ((p3 ∧ ((False ∧ (False ∧ (p3 ∧ p4))) ∧ p5)) → False)) ∨ p4) ∨ p5) ∧ True) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- False on the left can always be used.
  apply False.elim h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116240190678494255380449936431 : ((((False ∨ p5) → p1) ∨ (((p1 → False) → (((p2 ∨ p2) → False) → p3)) ∨ (p1 ∨ ((False ∨ ((p3 → p1) → p2)) ∨ p5)))) ∨ (True ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55401496368460908660898920786 : ((((((p5 ∧ p5) → p4) ∧ p3) ∨ p4) → (False ∧ (((True ∨ ((True → (((p3 ∧ (p2 → p4)) ∨ True) → True)) ∧ True)) → False) ∨ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_720702569779278255359945787207 : ((((((True → p3) → p5) → p1) → (p1 → (((True → True) ∧ ((((True ∨ p2) → p1) ∨ p1) ∧ True)) ∧ ((p2 → (True → True)) → p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_654284000423134740577099710564 : ((((((((((((p5 → (p3 → p4)) ∧ (p1 ∧ p3)) ∨ True) → (p1 → p5)) ∨ p3) → p2) ∧ True) → (p4 ∨ p3)) ∨ p5) ∨ (p5 ∨ True)) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_149711684435365531431447789627 : ((p5 ∧ (p2 ∨ ((((True ∧ (True ∧ False)) ∨ p1) → (((p3 ∧ p4) ∧ (p1 → p4)) → p5)) ∧ (True ∧ True)))) ∨ (p1 → ((p2 ∨ True) ∨ p3))) := by
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
theorem thm_5_vars_64125321950277308243798034942 : ((False ∨ (((p4 ∨ p2) → (p1 ∨ p1)) ∧ (p5 → ((((p1 ∨ p1) → (((p3 → (p3 → p3)) ∨ p2) ∨ p2)) ∧ (False → p1)) → p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_451711319914082829640369016232 : (((((((p5 ∧ p4) → ((False ∧ p5) ∧ p5)) → (True ∨ p5)) → (((p2 → (p2 ∨ p1)) ∧ p2) ∨ p2)) ∨ (p5 → (True ∨ (False ∨ p5)))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246516027019633168777085327633 : ((p5 ∧ p1) ∨ ((((p4 → p2) ∨ (p5 ∨ (p2 → (((p3 ∨ (p3 → p5)) ∨ False) ∧ True)))) → False) ∨ (True ∨ (p4 ∨ (p1 ∨ (p1 → p5)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119331341599440428315252080369 : ((p3 → (((((p3 ∧ p3) → p3) ∨ (p1 ∧ p4)) ∨ p2) → (((p1 → p5) ∨ (((p1 → p4) ∨ (p4 ∧ True)) ∨ p5)) ∧ True))) ∨ (True ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53274667005565488794185115260 : (((p1 ∧ (True → ((((p1 → p4) ∨ p5) ∧ p2) ∨ (p1 ∧ p2)))) ∨ (((True → (p3 ∨ p2)) ∨ (p5 ∨ (True ∨ (p5 ∧ p5)))) ∨ p3)) ∨ p4) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177283666725332214538121211251 : ((p1 ∨ ((((p5 ∨ True) ∨ ((p4 ∨ p4) ∧ p3)) ∨ p4) ∨ (True ∨ p1))) ∧ (((p1 → (True → ((p2 ∨ p4) ∨ (p5 ∨ p1)))) ∨ False) ∨ p5)) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_741417871771235419648423651521 : ((((p5 ∨ p1) ∨ (((p2 → p4) ∨ (p1 ∨ ((((p3 ∨ (p1 ∨ ((p5 ∧ True) ∨ p5))) ∨ (p3 ∨ (p3 ∧ True))) ∨ True) ∨ p5))) ∨ p3)) ∨ p2) ∧ True) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_673857808148747390858623412318 : (((((False ∧ p1) → (((True ∨ (p5 ∧ (((True ∧ False) ∧ True) ∧ False))) ∧ p4) ∨ (p5 → ((False → p1) ∧ p5)))) → ((p2 ∧ False) ∨ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111922831277901452603974035365 : ((((((p3 ∨ p4) ∧ (p2 → p2)) → (((p2 → p1) → p1) → p4)) → ((p1 ∨ p1) ∨ (p1 ∨ ((True → p1) ∧ p1)))) ∨ True) ∨ (False ∨ p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_12407915191891430164401463547 : (((((False → p2) ∨ (p1 → p1)) → (((((p1 ∧ (p1 ∧ True)) ∧ (p2 ∨ p1)) ∧ (False ∧ False)) ∧ p5) ∧ ((p4 → True) → p3))) → p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((False → p2) ∨ (p1 → p1)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- We need to get the left conjuct of h7 based on <expert-advice>.
  let h8 := h7.left
  -- False on the left can always be used.
  apply False.elim h8
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111630141140586489708139119624 : ((((((p1 → ((p5 ∨ ((False ∨ (p2 → (True → (p2 ∨ p3)))) → p2)) → p3)) ∧ True) → ((p3 → p5) → p4)) ∨ p3) ∨ p2) ∨ (p5 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115243684742984351050050672404 : (((((True ∨ False) ∧ (p1 ∧ (p1 ∨ p4))) ∧ (p5 ∧ p2)) ∨ (p3 → ((p2 → ((False → True) ∧ p3)) ∨ ((False ∧ False) ∨ p1)))) ∨ (p5 ∨ p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336373512858473793362739798789 : (p1 → ((True ∧ ((p5 ∨ (True ∧ (((p4 ∧ p5) ∨ p3) ∧ (p4 → ((p2 → (False ∨ ((p1 ∧ p5) → p4))) → (p1 → p4)))))) ∨ p4)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59007391095281900885593172536 : (((p3 ∧ p3) ∨ (((True ∧ ((p5 → p1) ∨ (False → ((p4 ∨ (True → p3)) ∨ (p5 → (((p2 → False) ∨ p5) → p5)))))) → False) ∨ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245112420829800120698114302606 : ((p2 ∧ True) ∨ ((p4 → (p2 → (((p3 ∧ (((p1 ∨ (p5 ∨ ((p4 ∨ False) ∧ p4))) ∧ p5) ∧ False)) ∧ (p1 → p2)) ∨ p2))) ∨ (p5 ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_732620008997922750871428909087 : ((((p1 ∧ p1) ∧ ((p2 ∧ False) ∧ ((((p4 ∨ ((p4 ∧ p3) → (p2 → (p3 ∨ ((p2 ∨ p2) ∧ p2))))) ∧ p5) → p4) ∧ (True ∨ p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_104582667920976564414586701854 : ((((p5 → ((p3 ∨ ((((p4 ∧ False) ∧ False) ∨ (True → True)) ∧ p3)) ∨ p3)) → (p3 ∧ (False ∧ (p5 → p2)))) ∨ (False → p2)) ∧ (True ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165148320663071367465297799537 : ((((p3 → ((((p2 ∨ False) ∨ (True ∧ False)) → p5) ∨ p1)) → (False ∨ False)) ∧ (True ∧ p5)) ∨ (p3 → ((p3 ∧ False) → ((p2 → p3) → p2)))) := by
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
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67537487000835857955746396593 : ((p1 → (((p2 ∨ False) ∧ p1) ∧ (((True ∨ ((False → ((p5 ∧ p4) ∧ (p3 → (((p4 → p1) ∧ p3) → False)))) ∨ p3)) → False) ∧ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57105596097726319555916804169 : ((((False ∨ p2) ∧ p2) ∨ ((((((p2 ∨ (p4 ∧ True)) → False) → p1) ∨ True) ∨ (p1 ∨ ((True ∧ (False → True)) ∨ (False ∧ p4)))) ∧ True)) ∨ p1) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111861967245353657313138830188 : ((((((True → p3) ∨ p5) ∨ ((p4 ∨ p4) ∨ (((True ∧ p5) → (p2 → p2)) ∨ p1))) ∧ (((p1 ∨ p5) → True) → False)) ∨ p1) ∨ (True ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200763767736405597502364002114 : ((p4 ∧ ((p2 ∧ ((p5 → p4) → p2)) ∨ p1)) → (((True → p5) → ((p2 ∨ (p4 ∧ p3)) → ((p2 ∧ (p2 ∧ p5)) ∨ (False → p3)))) ∨ p4)) := by
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
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2



