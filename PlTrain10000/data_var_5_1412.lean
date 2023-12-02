variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206037141936621494703452698863 : ((p2 ∧ (False ∧ (True ∧ (p5 ∧ p2)))) ∨ (True ∧ ((p3 ∨ ((False ∧ p1) → True)) → ((((p2 ∧ p1) ∨ (p4 → p5)) ∧ (p3 ∧ p3)) ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_623010569867976627192763451845 : ((((p5 ∧ ((p5 → True) → (((p5 → p4) ∧ ((False → p4) → p5)) ∧ ((p4 ∨ p1) ∧ (((p3 → p3) ∨ (p3 ∧ p5)) → p2))))) ∨ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207229441155400405470794727297 : (((((False ∨ True) ∨ False) ∨ p3) ∨ True) → (((True → (False ∨ p2)) → False) ∨ ((False ∨ (p5 ∧ (p1 → ((p2 ∨ p4) ∨ (p3 ∧ False))))) → p5))) := by
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
        -- Disjunctions on the left can always be decomposed.
        cases h4
        case inl h5 =>
          -- False on the left can always be used.
          apply False.elim h5
        case inr h6 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h7
          -- Disjunctions on the left can always be decomposed.
          cases h7
          case inl h8 =>
            -- False on the left can always be used.
            apply False.elim h8
          case inr h9 =>
            -- Conjunctions on the left can always be decomposed.
            let h10 := h9.left
            let h11 := h9.right
            -- One of the premise coincides with the conclusion.
            exact h10
      case inr h12 =>
        -- False on the left can always be used.
        apply False.elim h12
    case inr h13 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h14
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h15 =>
        -- False on the left can always be used.
        apply False.elim h15
      case inr h16 =>
        -- Conjunctions on the left can always be decomposed.
        let h17 := h16.left
        let h18 := h16.right
        -- One of the premise coincides with the conclusion.
        exact h17
  case inr h19 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h20
    -- Disjunctions on the left can always be decomposed.
    cases h20
    case inl h21 =>
      -- False on the left can always be used.
      apply False.elim h21
    case inr h22 =>
      -- Conjunctions on the left can always be decomposed.
      let h23 := h22.left
      let h24 := h22.right
      -- One of the premise coincides with the conclusion.
      exact h23



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62077208686841779650986550798 : ((p2 ∧ (p1 ∧ ((p2 ∧ p2) ∧ ((((((((p3 ∨ p4) ∨ p5) ∨ p1) → (p2 ∧ p3)) ∧ ((p5 ∨ p3) → p5)) ∧ p4) ∧ p4) ∨ p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135580225578389690196095040511 : ((((((p3 ∨ (p3 → (p4 ∨ ((p4 ∧ True) ∨ (p4 ∨ False))))) → p4) ∧ p2) → p3) ∨ (p5 ∨ (False → (p2 ∧ p1)))) ∨ (p1 → (True ∧ p5))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_54008856690159308598635431426 : (((((p3 ∧ (p3 ∧ p2)) ∧ ((p2 → False) → p1)) → False) → ((p4 ∨ ((True ∨ p1) → ((p1 ∨ (p5 ∨ p4)) ∧ (False ∧ p4)))) → p4)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h5 : (True ∨ p1) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h6 := h4 h5
    -- We need to get the right conjuct of h6 based on <expert-advice>.
    let h7 := h6.right
    -- We need to get the left conjuct of h7 based on <expert-advice>.
    let h8 := h7.left
    -- False on the left can always be used.
    apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53157426266963914313203372356 : (((((p2 ∧ p4) ∧ ((((p1 ∧ p5) → p3) ∨ p4) ∨ p4)) ∨ False) ∨ ((p4 ∧ p5) → ((((False → p2) ∧ p2) ∧ p5) → (p4 ∧ p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116202198388584042699728061184 : ((((True → p1) ∧ False) ∨ ((((((True ∧ False) → True) → (p5 ∨ p3)) ∨ p5) ∧ (p1 ∧ p5)) → (p2 ∨ (p2 ∨ (False → p5))))) ∨ (p5 ∨ p4)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h3.left
    let h6 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h3.left
    let h10 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h11
    -- False on the left can always be used.
    apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_708878335862621651529659175942 : (((((False → (False → (False ∧ True))) ∧ (p4 ∨ p2)) → ((p5 ∧ True) ∨ (p1 ∨ (p3 ∧ ((p1 ∧ p3) → ((p5 → (False → True)) ∧ p4)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186428225654810531286699386192 : (((False → ((p2 ∨ (p2 ∧ False)) ∨ ((p5 ∨ p2) ∧ p2))) → False) → (p3 ∨ (((p4 ∨ p1) → p3) → ((p4 ∧ p5) ∧ ((p3 ∨ True) ∨ p1))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (False → ((p2 ∨ (p2 ∧ False)) ∨ ((p5 ∨ p2) ∧ p2))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230462134757040005720682442168 : (((p5 ∨ p2) ∧ p3) → ((((p4 ∧ (False ∨ p3)) → ((p3 → (p2 → (True ∨ (((p2 ∨ p5) → p3) → p3)))) ∨ p3)) → (p4 ∧ p2)) ∨ p3)) := by
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
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_676304798988557857192083155440 : (((((False ∧ False) ∧ (p3 ∧ (p3 ∧ (True → ((p5 → (p2 ∧ False)) ∨ ((p2 ∧ p1) → (p4 → p5))))))) ∧ ((True ∧ (False → p4)) ∨ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208836369859690685493916859520 : ((p3 ∧ (True ∨ ((p4 → p5) → False))) → (((((((p5 ∧ p3) ∨ p1) ∧ p4) → ((p5 ∨ (False ∧ True)) → False)) ∨ p1) ∨ p5) ∨ (p3 ∨ True))) := by
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
theorem thm_5_vars_320068451940908545555744018402 : (p4 ∨ ((p1 → (p2 ∨ p2)) ∨ ((p3 → p2) ∨ (p5 → ((p2 ∨ ((p1 ∧ (p1 ∨ p3)) ∧ p3)) ∨ (True ∨ ((p5 ∧ p4) ∨ (p5 ∧ p5)))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_611861596904024375123819937984 : (((((p4 → ((p4 ∧ (p1 → (((((p2 → p2) ∨ p2) → False) ∨ p3) → p4))) ∧ (p3 ∧ (((False ∨ p3) ∧ True) → False)))) → p1) ∨ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_311777328664630181626286169360 : (p2 ∨ (False ∨ ((p4 ∨ p4) ∨ (((False ∨ ((False ∧ True) ∨ p2)) → ((((p5 ∨ p2) → (p5 ∧ False)) ∨ (False → p4)) ∧ (p4 → True))) ∨ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- False on the left can always be used.
    apply False.elim h2
  case inr h3 =>
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
      -- False on the left can always be used.
      apply False.elim h8
  -- Implications on the right can always be decomposed.
  intro h9
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_617916132846029102367050510826 : (((((p2 ∧ (((False ∧ p1) ∨ True) → p3)) → (((p3 ∨ p2) → True) ∧ (True → ((((p1 ∧ False) ∧ False) ∨ p3) ∧ (True ∨ True))))) ∨ p4) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h6 : ((False ∧ p1) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h7 := h5 h6
  -- One of the premise coincides with the conclusion.
  exact h7
  -- Conjunctions on the left can always be decomposed.
  let h8 := h1.left
  let h9 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198897691580666126198605259887 : ((p3 → ((((p3 → True) ∧ p4) → p3) → p1)) ∨ (((True → ((p5 → p1) ∨ p1)) ∧ (p5 ∨ p4)) → ((((p3 ∧ p2) → True) → p5) ∨ p4))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233188135474208316101838734575 : ((p5 ∧ (p4 ∨ p1)) → (((False → True) → p4) ∨ (((((True → p3) ∧ p2) ∨ ((False ∧ p2) ∨ (True ∧ (p3 ∧ p4)))) ∨ False) ∨ (p1 ∨ True)))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205262443278064135618797780906 : ((((p4 ∧ True) → p5) ∨ (p3 ∧ False)) ∨ ((((p3 ∨ p2) ∨ (((p4 → (True ∧ p3)) ∧ p5) ∨ True)) ∧ (True → ((p4 ∧ p1) ∨ p1))) → p1)) := by
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
    cases h4
    case inl h5 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h6 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h7 := h3 h6
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Conjunctions on the left can always be decomposed.
        let h9 := h8.left
        let h10 := h8.right
        -- One of the premise coincides with the conclusion.
        exact h10
      case inr h11 =>
        -- One of the premise coincides with the conclusion.
        exact h11
    case inr h12 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h13 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h14 := h3 h13
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h15 =>
        -- Conjunctions on the left can always be decomposed.
        let h16 := h15.left
        let h17 := h15.right
        -- One of the premise coincides with the conclusion.
        exact h17
      case inr h18 =>
        -- One of the premise coincides with the conclusion.
        exact h18
  case inr h19 =>
    -- Disjunctions on the left can always be decomposed.
    cases h19
    case inl h20 =>
      -- Conjunctions on the left can always be decomposed.
      let h21 := h20.left
      let h22 := h20.right
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h23 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h24 := h3 h23
      -- Disjunctions on the left can always be decomposed.
      cases h24
      case inl h25 =>
        -- Conjunctions on the left can always be decomposed.
        let h26 := h25.left
        let h27 := h25.right
        -- One of the premise coincides with the conclusion.
        exact h27
      case inr h28 =>
        -- One of the premise coincides with the conclusion.
        exact h28
    case inr h29 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h30 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h31 := h3 h30
      -- Disjunctions on the left can always be decomposed.
      cases h31
      case inl h32 =>
        -- Conjunctions on the left can always be decomposed.
        let h33 := h32.left
        let h34 := h32.right
        -- One of the premise coincides with the conclusion.
        exact h34
      case inr h35 =>
        -- One of the premise coincides with the conclusion.
        exact h35



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150565492529691898673883926136 : (((((p4 ∨ True) → False) ∧ (p4 ∨ (((p5 ∨ (((True ∧ p1) ∨ (p2 → p2)) ∧ True)) → p5) → p4))) ∧ p4) → (p1 ∧ (True ∨ (False → p1)))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h7 : (p4 ∨ True) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h3
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h8 := h4 h7
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h10 : (p4 ∨ True) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h3
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h11 := h4 h10
    -- False on the left can always be used.
    apply False.elim h11
  -- Conjunctions on the left can always be decomposed.
  let h12 := h1.left
  let h13 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h14 := h12.left
  let h15 := h12.right
  -- Disjunctions on the left can always be decomposed.
  cases h15
  case inl h16 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h17 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_704609427306371271644985104513 : (((((True ∨ p3) → ((p2 ∧ (p3 ∨ False)) ∨ (False ∧ p5))) → ((p1 → False) ∧ ((p5 ∨ (p4 → (p4 → p2))) ∧ ((p3 ∨ False) ∧ False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157847159210688302878925539148 : (((((p2 ∧ p3) ∧ ((p4 ∨ p5) ∧ p4)) ∧ (False → p2)) ∧ ((((True ∨ True) → False) ∧ False) → p2)) ∨ ((p5 ∧ (p4 ∧ p3)) → (False → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149259892514081618930095229680 : (((p4 ∨ p2) ∨ ((((p1 → p4) ∨ p4) ∨ ((p1 ∧ (((p2 → False) ∧ p3) ∧ p4)) ∨ (False ∨ False))) ∧ p1)) ∨ (p4 → ((True → True) ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164559902906918889725180711213 : (((((p5 ∧ (True ∨ p3)) → p4) ∧ (((False → p2) → (True → False)) ∧ (p5 ∨ p1))) ∧ p4) ∨ ((((p2 → p5) → p1) → p1) ∨ (True ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_212487938289230288896468053773 : ((p4 ∨ ((False ∨ p2) ∨ True)) ∧ (((p4 ∨ p4) ∨ p5) ∨ (p5 → ((p2 ∨ p5) → ((((True ∨ p1) → ((False ∨ p4) ∧ p1)) ∨ p5) ∨ p3))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59951605322582462176554825322 : (((True ∨ p3) → (((False → (p5 → ((True → ((True ∧ True) → (p4 ∧ p3))) ∨ ((p4 ∨ p5) ∧ (True ∧ p2))))) → (p3 ∧ p1)) ∧ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_36883050534460663222956300881 : ((p5 → (((True → p5) ∧ p1) ∨ (((p4 → (p1 ∨ p1)) ∧ (True → p4)) → (True ∧ (((p1 → (False ∧ True)) → p2) ∨ (p2 ∨ True)))))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_98266733602284773516157023834 : ((p4 ∨ (p2 ∧ ((((True → ((p1 → ((((False → p5) ∨ p4) → p5) → p1)) ∧ False)) → p3) → (False ∧ (True → (True ∨ False)))) ∧ p5))) → p4) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h8 : ((True → ((p1 → ((((False → p5) ∨ p4) → p5) → p1)) ∧ False)) → p3) := by
      -- Implications on the right can always be decomposed.
      intro h9
      -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
      have h10 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h9, we can now drive its conclusion.
      let h11 := h9 h10
      -- We need to get the right conjuct of h11 based on <expert-advice>.
      let h12 := h11.right
      -- False on the left can always be used.
      apply False.elim h12
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h13 := h6 h8
    -- We need to get the left conjuct of h13 based on <expert-advice>.
    let h14 := h13.left
    -- False on the left can always be used.
    apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165593310971332673062437424089 : ((((p2 → ((False ∨ (True → p1)) → p4)) ∧ p3) → ((p2 → ((p5 ∧ p4) ∧ p3)) ∨ p1)) ∨ (((p4 ∨ (True ∨ (False ∧ False))) → p5) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114810939898440747119829194428 : ((((p2 ∧ p3) ∧ ((((p4 ∨ (p1 → p4)) ∧ p4) ∧ p4) → (p5 ∧ p2))) ∧ ((False ∨ p2) ∧ (((True ∧ p2) ∧ p2) ∨ False))) ∨ (True ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217814362716287245384667274527 : (((p2 ∨ (True → p1)) → p4) → (p2 ∨ ((((((p4 ∧ p5) ∨ p2) ∧ p2) ∧ (p3 ∧ False)) ∧ p5) ∨ ((p2 ∨ p2) → (p3 → (p4 → p2)))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h5 =>
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217781462772625965478020404173 : (((True ∨ (True → p4)) → True) → ((p5 ∧ (((((p2 → (True ∨ (p3 ∨ True))) ∨ p1) ∧ p4) → (p3 ∨ (p5 ∧ p2))) ∨ (False ∧ p1))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244311443050354133159123592454 : ((False ∧ False) ∨ ((((p1 ∧ (p1 → (True ∧ (True ∧ p1)))) ∧ p3) ∧ ((False ∨ p5) ∧ ((p3 ∨ ((True → p1) ∨ (False ∨ p1))) ∨ p4))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_247613360413017313901894525811 : ((False ∨ p5) ∨ (((p5 → (p5 ∨ p3)) ∧ ((False ∨ p5) ∧ (False ∨ False))) ∨ ((p4 → (True ∧ (True ∨ p4))) → ((p5 → True) ∧ (False ∨ True))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_302060986517427363517820647687 : (False ∨ (True ∧ (p1 → ((p5 ∧ p4) ∨ (((p3 ∨ p5) ∧ p4) ∨ (p4 ∨ (p2 ∨ (((True ∨ ((True → (p4 → p1)) → p5)) ∨ p3) → p1)))))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h5 =>
      -- One of the premise coincides with the conclusion.
      exact h1
  case inr h6 =>
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_717664084383179992242969812811 : ((((p5 → (p4 → (False → p1))) ∧ ((p4 ∨ (p1 ∨ ((p2 ∨ p1) ∨ p1))) ∧ (p3 ∨ (p5 ∨ (p2 ∨ (p3 → ((p5 → p2) → p5))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249958222546250475099780048000 : ((True → p2) ∨ ((((((p2 → p2) ∨ p1) ∨ (p5 → True)) ∧ ((((p5 ∧ (True ∨ p2)) → (False ∧ p3)) ∨ p4) ∧ p5)) ∨ (p2 ∨ True)) ∨ False)) := by
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
theorem thm_5_vars_809309747895958779347218366046 : (((p5 → (((p5 ∨ p1) → ((((p1 → (((p1 ∨ p5) ∧ (True ∨ (p1 → (p4 ∨ True)))) → (p3 ∧ p1))) ∨ True) → False) ∨ p5)) ∨ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62394875188792715254266495572 : ((p3 ∧ (((p5 ∨ p1) ∨ (p1 → (p4 ∨ (p1 ∨ (False → p3))))) ∧ (p4 ∨ (False ∧ (p3 → ((p3 ∨ ((False ∧ p5) ∧ p2)) ∧ p5)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258763348959278242961820021806 : ((True → False) → (((((True → ((p4 → p1) ∧ (((p4 ∨ p1) ∧ p4) ∨ p3))) ∧ ((False ∧ (p5 → (False ∧ p4))) ∨ p2)) ∨ p5) → p4) ∨ p1)) := by
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
theorem thm_5_vars_667162158203376935653934126614 : ((((((p2 → p1) ∨ p5) → (p3 ∨ (((p2 → (True ∧ p4)) → (p4 → p2)) ∨ ((p3 ∧ False) → (p5 ∧ p4))))) ∧ (False → (True ∧ False))) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- False on the left can always be used.
    apply False.elim h5
    -- Conjunctions on the left can always be decomposed.
    let h6 := h3.left
    let h7 := h3.right
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- False on the left can always be used.
    apply False.elim h11
    -- Conjunctions on the left can always be decomposed.
    let h12 := h9.left
    let h13 := h9.right
    -- False on the left can always be used.
    apply False.elim h13
  -- Implications on the right can always be decomposed.
  intro h14
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- False on the left can always be used.
  apply False.elim h14
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136129198812125467546346958712 : (((((((False ∧ p4) → p2) ∧ p5) → p2) ∧ p2) → (((True → ((p2 ∧ (p2 ∧ (p3 ∧ p3))) ∧ p2)) ∨ p5) → p5)) ∨ (True ∨ (p3 → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157283192448240114777939528785 : ((((p5 ∨ p3) ∧ (((p4 → p3) → (True ∨ p2)) → (((p3 ∨ True) → False) → (True ∧ p5)))) → p2) ∨ ((False → p4) ∧ ((True ∧ False) → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232372211236973808021200624269 : (((p5 → True) → False) → (p5 ∨ (True → ((((True → p5) → (p1 → True)) → p5) → (((((False ∧ p4) → p4) ∨ False) → p1) ∨ (p3 → p5)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p5 → True) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116516837916567923994084337461 : (((p5 ∧ False) ∧ (((((p3 → p1) → ((p2 ∨ p3) ∨ (p3 ∨ ((p5 ∧ (p2 ∧ p3)) ∧ (p1 ∨ p1))))) ∧ False) ∨ p3) ∨ True)) ∨ (p5 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64332423941782992887471989542 : ((p1 ∨ (((p3 ∧ True) ∨ ((((p1 ∧ ((p2 → p1) ∨ p2)) ∨ p3) → (True ∨ p4)) ∧ (((p2 ∨ p1) ∨ (p5 ∨ p3)) ∧ p4))) ∧ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_242815844785950226620421812019 : ((p3 → p3) ∧ ((p1 ∨ ((p5 → p1) ∧ (p3 ∧ (p3 ∨ (p2 ∧ p2))))) ∨ (p3 → (False → (((p2 ∨ False) ∨ ((p4 → p2) ∧ p2)) → p1))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- False on the left can always be used.
      apply False.elim h3
    case inr h7 =>
      -- False on the left can always be used.
      apply False.elim h7
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- False on the left can always be used.
    apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49874938180499750211178496190 : (((((True ∧ ((p4 ∧ (((p1 ∧ ((False → (p4 → p4)) ∧ p4)) → p3) ∧ p1)) ∧ p4)) ∧ p1) ∨ False) ∧ (p5 ∧ (False ∧ (p5 → p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244143255901485553150460992852 : ((True ∧ p4) ∨ ((((p2 ∨ ((((True ∧ p5) → p3) → (p5 ∨ True)) ∧ (p4 ∨ ((p3 ∧ p4) ∨ p4)))) → p2) ∧ p3) ∨ (p4 → (p4 ∨ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149503797199445156050062279832 : ((p1 ∧ ((((p2 ∨ (p3 ∨ (p3 → p2))) ∨ (p2 ∧ (True ∨ (p5 ∨ p2)))) → p4) → (True → (True ∧ p2)))) ∨ (((False ∨ False) ∧ p4) → p3)) := by
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
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112080723957462077165493101733 : ((((p5 ∧ p2) ∨ ((((False ∧ ((False ∨ (p4 ∨ ((p1 → True) ∨ p1))) ∨ p3)) → p4) ∧ p4) → ((p3 ∨ p5) → p1))) ∨ p2) ∨ (p2 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56028869386134023425363358670 : ((((p4 ∧ (p2 → False)) ∨ p3) ∨ ((True ∧ (False ∧ False)) ∨ (((False → p2) → (p3 → (p4 ∨ (False ∨ (p2 ∨ False))))) ∨ (False ∨ True)))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_115399023220558871134720129807 : (((p4 ∧ ((True → p1) → (p1 ∨ (False ∨ p4)))) ∧ (((p3 → ((p5 → p2) ∨ ((p4 → False) → (p3 ∧ p2)))) ∨ p2) → p5)) ∨ (p4 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55435633027395569273182808398 : ((((((p5 ∨ p3) ∧ p3) ∨ p5) → p5) → (((False → ((True → (False ∨ p5)) ∨ True)) ∧ (False ∧ ((p2 → p5) ∧ False))) ∨ (p2 → False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_632187735376172545015361939233 : ((((((p4 → p1) → ((True → p3) → ((((True ∧ ((p2 → p4) ∧ False)) ∨ ((p5 ∧ False) ∨ True)) ∧ p3) ∧ (p3 → p2)))) → p1) → p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_139936486386927597589645699989 : ((((p3 → (True ∨ p1)) ∧ ((p4 ∨ (True → ((True ∧ ((True ∧ p5) ∨ (p5 ∧ True))) ∨ p4))) → False)) ∧ (True → p5)) → ((p2 ∧ p4) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h6 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h7 := h3 h6
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46194438804541141997262209347 : ((((p3 ∨ ((True → (((((((False ∧ True) ∨ (p3 ∧ True)) ∧ p1) ∧ (p4 → False)) ∧ p2) → p1) ∧ p4)) ∨ p5)) → p5) ∧ (False ∧ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149307179715502143161093136285 : (((p1 ∧ True) → (((p4 → p5) → (p4 ∨ ((p4 → True) → (p3 ∧ p3)))) ∨ (p5 ∨ ((p1 ∨ False) → p2)))) ∨ ((True ∨ (p1 ∧ True)) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_126048630718271467481070978646 : (((p4 → True) → (((p4 ∧ p5) ∧ ((p3 ∨ (((((True → p5) → (False ∧ (p1 ∨ p5))) → p3) ∨ p4) ∨ p3)) → p1)) ∧ p1)) → (p4 → p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : (p4 → True) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h3
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55220523824033327285156864639 : ((((p3 ∧ (True ∨ p3)) ∨ (p3 → p4)) ∨ ((((p5 ∨ p2) ∨ (True ∨ False)) → (p2 → ((p5 ∧ ((p5 → p3) → p4)) ∧ p2))) ∧ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_638827074794022949266487128241 : ((((((p3 → (p5 ∨ p1)) ∧ p2) ∧ (True → ((((p2 ∨ p5) ∧ ((p3 → p3) → p3)) → p1) ∧ (((p5 → p2) → p2) ∧ False)))) → p1) ∨ p3) ∧ True) := by
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
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h6 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h7 := h3 h6
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- False on the left can always be used.
  apply False.elim h9
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_84149693227595570625386459971 : (((p5 ∧ ((((p4 ∨ ((p5 → (p3 ∧ p4)) → False)) ∨ p3) → True) → (p3 ∧ False))) ∧ ((False → ((p5 → p2) ∧ (p2 ∨ False))) ∧ p2)) → False) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h3.left
  let h7 := h3.right
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h8 : (((p4 ∨ ((p5 → (p3 ∧ p4)) → False)) ∨ p3) → True) := by
    -- Implications on the right can always be decomposed.
    intro h9
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h10 := h5 h8
  -- We need to get the right conjuct of h10 based on <expert-advice>.
  let h11 := h10.right
  -- False on the left can always be used.
  apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168817700686402212619373990777 : ((p2 ∨ (p2 ∧ (p5 → (p2 ∨ (p1 ∨ ((p4 ∧ ((p2 ∨ (p4 ∨ p4)) ∨ p4)) ∧ False)))))) → (((p1 ∨ (p2 ∨ p2)) ∧ p1) ∨ (p5 ∨ True))) := by
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
theorem thm_5_vars_313074292691127394337308886757 : (p3 ∨ (((((False ∧ (p2 ∨ p4)) ∧ (False ∨ p5)) ∨ ((((((False ∨ p5) → p4) ∧ (True ∨ p5)) → True) ∨ False) ∨ p4)) ∧ (False → p4)) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_201110625313619176385596534077 : ((True → ((p1 ∧ (True ∧ p1)) → (p3 ∧ p1))) → (((((p1 → False) ∨ True) ∧ (p4 ∧ True)) ∨ (p1 ∨ (((False ∧ False) ∧ p1) ∧ p3))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_18797313402778775960772606230 : ((((p1 → ((p4 → p4) ∨ (((p1 ∧ False) ∧ (p5 ∧ ((p4 ∨ p4) ∧ p1))) → False))) → p1) ∨ (((p4 ∧ p1) ∨ (True ∨ p5)) ∧ True)) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351793436045068390752383367863 : (p4 → ((((False ∨ p5) ∨ p1) ∨ (((p3 ∨ p5) ∧ p4) ∨ (True ∨ p2))) ∧ (p2 ∨ ((p4 ∨ (p2 ∧ (p1 ∧ (p4 → (p3 ∨ p1))))) ∨ p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168228902824616873282894277092 : ((((p2 ∧ p2) ∧ True) → ((p4 ∨ (False ∧ ((False → True) ∨ p1))) ∨ (False → (True ∧ p5)))) → (((False → p3) → p1) → (p5 → (p1 ∨ False)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (False → p3) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- False on the left can always be used.
    apply False.elim h5
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h4
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50974481135762075345866217127 : (((((p4 → False) ∨ True) ∧ (((p5 → p2) ∧ (p2 ∧ p4)) ∧ (p2 ∧ ((p4 ∨ True) ∧ p4)))) ∧ (((p2 ∧ (p3 ∨ p2)) ∨ False) ∧ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_80765895356669071545515461603 : (((p1 → (((p4 ∨ p3) ∧ p2) ∨ ((((p4 → ((True ∧ (p3 ∨ True)) ∨ (p1 ∨ p1))) → p5) → p5) ∨ (False ∨ p2)))) → (p2 ∧ p5)) → p2) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p1 → (((p4 ∨ p3) ∧ p2) ∨ ((((p4 → ((True ∧ (p3 ∨ True)) ∨ (p1 ∨ p1))) → p5) → p5) ∨ (False ∨ p2)))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h4
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h5 : (p4 → ((True ∧ (p3 ∨ True)) ∨ (p1 ∨ p1))) := by
      -- Implications on the right can always be decomposed.
      intro h6
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h3
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h7 := h4 h5
    -- One of the premise coincides with the conclusion.
    exact h7
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h8 := h1 h2
  -- We need to get the left conjuct of h8 based on <expert-advice>.
  let h9 := h8.left
  -- One of the premise coincides with the conclusion.
  exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341761585925119835714053255651 : (p2 → ((p4 ∨ ((((False ∧ p1) ∨ (p1 ∨ p5)) ∧ p3) ∧ (((False ∨ p1) ∧ ((False → (True → (False ∨ p3))) ∧ p1)) → False))) ∨ (p3 → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184852090144967277268798055222 : ((((False ∧ p5) ∧ p2) ∧ ((((True ∨ True) → False) ∧ p5) ∨ p2)) ∨ (True ∨ ((p5 ∨ (p1 ∧ True)) ∧ (((p5 → p2) ∧ (p4 ∨ p2)) → False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207503622270430496337941061425 : (((((p1 ∧ False) ∧ p5) ∧ p4) → False) → (((p1 ∨ p4) → (p2 ∨ (((True ∧ True) → p1) ∨ (p3 ∨ (p3 ∨ (p4 ∨ (p5 ∧ p1))))))) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232051429663168323386376035304 : (((p3 ∨ p5) → False) → ((((p3 ∨ p2) ∨ p1) → p3) ∨ ((p2 ∧ (p4 ∨ p3)) → ((p2 ∨ p1) ∧ (((p2 → p4) ∧ False) ∨ (p4 ∨ p4)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h6 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
  -- Conjunctions on the left can always be decomposed.
  let h7 := h2.left
  let h8 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h9
  case inr h10 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h11 : (p3 ∨ p5) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h10
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h12 := h1 h11
    -- False on the left can always be used.
    apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158697968131973648017224243539 : ((p2 ∧ (p2 ∨ (p2 ∧ (((((p5 → p5) ∨ p3) ∧ p5) ∧ ((True → (p1 → p2)) → True)) ∨ p3)))) ∨ ((((False → p1) ∧ p5) ∧ p1) → p5)) := by
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
theorem thm_5_vars_171569057873630823042462539566 : (((((False ∧ p1) ∧ (p3 ∨ (p3 → (p3 ∧ (False → False))))) ∧ (p5 ∨ p3)) ∨ True) ∨ (p3 → ((((True ∧ p5) ∨ p1) ∧ (True → p3)) ∧ p5))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59346933218038091222989412658 : (((p5 ∨ False) ∨ (((p3 ∧ (p3 → True)) → ((p3 ∧ (p4 ∧ p2)) ∨ False)) ∨ (False ∨ (p3 ∨ ((p1 ∧ p5) → ((False ∨ p2) → p1)))))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h1.left
    let h6 := h1.right
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57302662478131274260570828020 : ((((p5 → True) → p5) ∨ (((True ∧ ((p3 → p2) → p3)) ∨ (p5 ∨ (p2 → p4))) ∧ (p1 ∨ (True → (((True → p4) → p1) ∧ p4))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_594479843834210591804853816398 : (((((((p5 ∧ ((p4 → p5) ∧ ((True ∧ p1) → False))) ∨ (p3 → (p1 ∨ p1))) → p4) ∨ (((p3 ∧ p3) → (p4 ∨ p3)) → False)) ∧ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66786609002089671822811362361 : ((True → (False ∨ ((False ∨ (((p2 → False) ∨ p3) ∨ p2)) ∨ ((((True → p4) ∧ p4) → p4) ∨ ((p1 → (p4 ∧ p5)) → (p2 ∨ p3)))))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_650424644746055121521540589859 : (((((((((p3 ∨ ((p1 → False) ∧ False)) ∨ p3) ∧ True) → p5) ∧ (p2 → True)) → ((p5 → p2) ∨ (p4 ∨ (False → p5)))) ∧ (p5 → p5)) ∨ p3) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- False on the left can always be used.
  apply False.elim h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- One of the premise coincides with the conclusion.
  exact h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_139804073066352275939424692392 : (((p4 ∨ (((p2 ∧ True) → (p2 ∨ ((True ∨ ((((p3 ∨ False) → p2) ∧ p1) ∨ True)) → False))) ∧ (p3 → True))) → False) → (p2 ∧ (False ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p4 ∨ (((p2 ∧ True) → (p2 ∨ ((True ∨ ((((p3 ∨ False) → p2) ∧ p1) ∨ True)) → False))) ∧ (p3 → True))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4
    -- Implications on the right can always be decomposed.
    intro h6
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h7 := h1 h2
  -- False on the left can always be used.
  apply False.elim h7
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h8 : (p4 ∨ (((p2 ∧ True) → (p2 ∨ ((True ∨ ((((p3 ∨ False) → p2) ∧ p1) ∨ True)) → False))) ∧ (p3 → True))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h9
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h10
    -- Implications on the right can always be decomposed.
    intro h12
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h13 := h1 h8
  -- False on the left can always be used.
  apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168782516111549479419827988644 : ((p1 ∨ ((False ∧ True) → (((p1 ∨ ((p4 ∨ True) ∨ (p5 → (p5 ∧ p4)))) ∧ p4) ∨ p3))) → ((((True → (True ∧ False)) ∧ p2) ∨ True) ∨ True)) := by
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
theorem thm_5_vars_207317120340628595329585875427 : ((((p2 ∨ True) ∧ (p3 → p3)) ∨ p5) → (p2 ∨ (((((p5 ∧ (p3 ∨ (p3 ∨ p1))) ∨ (p3 ∧ p4)) ∧ p1) ∧ (p4 ∨ p3)) ∨ (p3 → True)))) := by
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h7
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118746707967908936810538818753 : ((p5 ∨ (((False ∧ True) ∧ (p3 → True)) ∨ ((p3 ∨ ((p5 ∧ p2) ∨ (p5 → ((p5 ∧ p2) → False)))) ∨ (False → (p3 ∧ True))))) ∨ (p2 → p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137270909329794815093444606720 : ((p1 ∧ (p3 ∨ (((p3 → p2) → p4) → ((p5 ∧ p2) → (p3 → ((p2 ∨ (p3 ∧ True)) → ((p1 ∨ False) ∧ False))))))) ∨ (p3 → (p1 ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50345918273003379848454590909 : (((((p4 ∧ p5) ∨ (p3 ∧ (p1 → p2))) → (((((p4 ∨ (True → False)) ∧ p5) ∨ True) ∨ False) ∧ p4)) ∨ ((p2 → p5) → (p3 → p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_344712715009297525297944969967 : (p2 → (p3 → (((((p5 ∨ True) → ((p4 → p1) ∨ (False → p1))) → p5) ∨ (((p3 ∨ (p3 ∨ p1)) ∧ (p2 ∧ p3)) ∨ (p2 ∨ p4))) ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219583486554574327926803368261 : ((True → (False ∧ (p1 ∨ True))) → (((p5 → (False ∨ (True ∧ (False ∧ (((p5 ∧ (p1 → False)) ∧ p5) → p1))))) ∨ (True ∨ False)) ∨ (p3 ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157908828464594064163811897371 : ((((((p3 ∨ p1) ∧ p1) ∨ False) → ((p3 ∧ p4) → p2)) → (((p1 ∨ p2) ∨ (p3 ∨ p1)) → p1)) ∨ ((p5 ∧ (p2 → (False ∧ p4))) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208713792625440435614557479693 : ((p1 ∧ ((p1 → (p2 ∨ p3)) ∧ p4)) → ((p5 ∧ p2) ∨ (((((p4 ∨ (p5 ∧ (True ∧ True))) ∨ p2) ∨ p2) ∧ (p1 → False)) ∨ (p5 → True)))) := by
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
  -- Implications on the right can always be decomposed.
  intro h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_264004375691841445480779923454 : (True ∧ ((((p4 ∨ (p2 → (False ∧ (True ∧ (p5 ∨ p4))))) ∨ True) → p2) → ((((p4 ∨ p4) ∧ p1) ∧ (False ∧ (p2 ∨ p4))) ∨ (p2 ∨ False)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p4 ∨ (p2 → (False ∧ (True ∧ (p5 ∨ p4))))) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55044496111438714917278399836 : (((p5 ∧ (p2 → ((p2 ∧ p5) → p1))) ∧ ((((p2 ∧ (False → (False → (p5 → p4)))) ∨ (p2 ∨ (p5 ∨ (p5 ∨ p1)))) ∧ p2) ∨ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_738146937967544119062147528744 : ((((False ∧ p2) ∨ ((((p4 ∧ p4) ∨ p2) → ((p3 ∧ ((p1 ∧ p5) ∨ p1)) ∨ (((p4 ∨ (p2 → p5)) ∨ True) ∧ (p2 ∨ False)))) ∧ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112161274351477061400803154776 : (((p2 ∧ (p3 → (((p2 ∧ p3) → ((((((True ∨ p4) ∨ p1) ∧ p5) ∨ (p5 ∨ p2)) ∨ (p2 ∨ p2)) ∧ p2)) → p2))) ∨ True) ∨ (p5 ∨ True)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173122576756372332513364282383 : ((p2 ∨ ((False ∨ (p5 ∨ p3)) → ((p5 ∨ (p4 → ((p2 ∧ p5) ∨ p3))) → p4))) ∨ (((False ∧ False) → (p4 → (p5 → p5))) ∨ (True → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351568443265422492498408790937 : (p4 → (((((True ∨ (p2 ∧ (p4 ∧ p1))) → (True → p1)) → True) ∧ ((p5 → p4) → (p5 ∧ False))) → ((p3 ∧ p1) ∨ ((False ∧ False) ∧ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h5 : (p5 → p4) := by
    -- Implications on the right can always be decomposed.
    intro h6
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h7 := h4 h5
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134090185854275690485547712078 : (((((p1 ∧ p5) → ((p4 ∧ p2) ∧ (p5 ∨ (p5 ∨ ((p2 ∨ (((p1 → True) ∨ p3) ∨ False)) ∧ p5))))) → p5) ∨ p4) ∨ (p2 → (p5 → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_223784738208540071330515647555 : ((p2 ∨ (p5 → True)) ∧ ((p2 ∧ True) → ((False ∨ (p2 ∧ ((p4 → False) ∨ p4))) → (((p4 ∨ p2) → False) → (p5 ∨ ((p5 → p3) → p4)))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h2.left
      let h11 := h2.right
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h12 : (p4 ∨ p2) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h10
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h13 := h4 h12
      -- False on the left can always be used.
      apply False.elim h13
    case inr h14 =>
      -- Conjunctions on the left can always be decomposed.
      let h15 := h2.left
      let h16 := h2.right
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h17 : (p4 ∨ p2) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h14
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h18 := h4 h17
      -- False on the left can always be used.
      apply False.elim h18



