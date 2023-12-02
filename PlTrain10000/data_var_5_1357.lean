variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49602079632030758240842542816 : ((((((True ∨ ((False ∨ True) ∧ (p3 ∨ p4))) ∨ p2) ∧ True) ∨ ((p4 → (p4 → ((p5 ∧ False) ∨ p5))) → p2)) → (p1 ∨ (p5 ∨ True))) ∨ False) := by
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
    cases h3
    case inl h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h7 =>
        -- Conjunctions on the left can always be decomposed.
        let h8 := h7.left
        let h9 := h7.right
        -- Disjunctions on the left can always be decomposed.
        cases h8
        case inl h10 =>
          -- False on the left can always be used.
          apply False.elim h10
        case inr h11 =>
          -- Disjunctions on the left can always be decomposed.
          cases h9
          case inl h12 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h13 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
    case inr h14 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h15 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341048877183412929536735366934 : (p2 → ((p1 ∨ ((((p4 → (False ∧ p3)) ∧ (((p3 ∨ False) ∧ True) ∨ p4)) ∨ p4) → (((p2 ∨ p1) → p1) → ((p2 → p3) ∧ p1)))) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185098576652863800800252875899 : (((True → p3) ∨ (False ∧ (p3 ∨ (((p2 ∧ p2) → p1) → False)))) ∨ ((False → ((((p5 → p1) → (p3 → False)) ∨ (p2 → p1)) → True)) ∨ p3)) := by
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
theorem thm_5_vars_184600409493675358463189183610 : (((((p4 ∨ (p3 → p5)) → False) ∧ False) ∧ ((False → p2) ∨ p5)) ∨ ((p3 ∨ ((((p4 ∨ p4) ∧ True) → (True → (True → p2))) ∨ True)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59790105723583614382765718370 : (((p2 ∧ p2) → ((((False → p1) ∨ ((((p4 → ((p3 ∧ p1) ∧ True)) ∧ (p2 → True)) → p3) → (p4 → True))) → p4) ∨ (p1 → p2))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51747421081033498047528648998 : ((((True → (p4 ∨ p3)) → (((p5 ∧ ((p4 ∧ p4) → (p2 ∧ p3))) → p3) ∧ p2)) ∧ ((((p3 → (False ∧ p3)) ∨ p2) → p1) ∧ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68675565806942482437495337094 : ((p4 → ((((p1 ∨ (((p2 ∨ p2) → (False → (p3 → (p2 → False)))) → p2)) ∧ (True → ((True → p2) ∨ True))) ∧ p5) ∧ (p3 ∨ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52436835951600455558831740658 : (((True ∧ (((p1 ∧ (p4 → p3)) ∨ (((p2 ∨ p2) ∨ p2) ∧ False)) ∨ p4)) ∧ (p3 → ((((p2 → False) ∧ (p5 ∧ p2)) ∨ p1) → p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_389835429486323879049860119755 : (((((p4 ∨ (((p5 ∨ (p5 ∧ False)) ∧ (p2 → p2)) ∨ (False ∨ True))) ∨ (p1 ∧ (p5 ∧ ((((True ∨ p5) ∧ False) → p1) ∨ p2)))) ∨ p3) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_216926398924387675193044793429 : (((True → (p1 ∧ p2)) ∧ p1) → ((((p1 ∧ p4) → True) → ((p2 → p2) ∧ p5)) ∨ (True ∧ ((False → (((p4 ∧ p2) ∧ False) → False)) ∨ p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181098680154605172935623339207 : (((p3 → p3) → ((False ∧ ((p4 → p2) ∧ p5)) ∧ ((False ∧ True) ∨ p3))) → (p4 ∧ (True → (p1 ∨ (False ∨ (((True ∧ p2) → p3) → p4)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p3 → p3) := by
    -- Implications on the right can always be decomposed.
    intro h3
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
  -- Implications on the right can always be decomposed.
  intro h7
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h8 : (p3 → p3) := by
    -- Implications on the right can always be decomposed.
    intro h9
    -- One of the premise coincides with the conclusion.
    exact h9
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h10 := h1 h8
  -- We need to get the left conjuct of h10 based on <expert-advice>.
  let h11 := h10.left
  -- We need to get the left conjuct of h11 based on <expert-advice>.
  let h12 := h11.left
  -- False on the left can always be used.
  apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300143080155994741864781621971 : (False ∨ ((p4 ∧ ((p1 ∨ (((((True ∧ p4) ∨ p3) ∧ p3) → p1) ∨ p3)) ∨ ((p5 → (((p3 → p4) ∧ p3) → p2)) ∨ p2))) ∨ (True ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_621208613511806906498817667294 : ((((True ∧ ((True → (p1 ∨ (p3 ∨ ((p2 ∧ p1) ∨ (((p3 ∨ (p4 ∨ p1)) → ((False → True) ∧ p3)) ∧ (p2 ∨ p3)))))) ∨ p4)) ∨ True) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_716432247845370586952703543703 : (((((p4 → p1) ∧ (p4 ∧ p2)) ∧ (p2 → ((True → ((False ∧ False) ∧ (((p1 ∧ p2) ∨ (p5 ∧ True)) ∧ False))) ∧ (p2 ∨ (p5 ∧ p2))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65914813087194166945390350747 : ((p4 ∨ (p3 ∧ ((p1 → p1) → ((p5 ∨ p2) ∨ ((False ∧ (p5 ∨ True)) ∨ (p3 → (p3 → ((((p2 → p2) ∨ p2) → False) ∨ p4)))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_742371369740695128623700202468 : ((((p1 → p4) ∨ ((((p4 → p1) ∨ ((False ∨ False) ∧ (p3 ∨ False))) ∧ ((p5 ∧ p2) ∨ ((p3 ∨ False) → True))) ∨ (p4 ∨ (True ∧ True)))) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_747340117725625327634006862180 : ((((p5 ∨ p4) → (((p5 ∧ True) ∨ p1) ∨ (((False → (p5 ∧ p2)) → (False ∧ ((p2 ∧ ((p5 ∧ (p3 ∨ p2)) ∨ p4)) → False))) ∨ p4))) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h2
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173570148640979127184973500754 : ((((p3 ∧ p5) ∨ (((False ∨ (p4 ∧ (p4 ∧ p4))) ∨ (p5 → p3)) ∧ p3)) ∧ p2) → (p2 → (((p1 ∨ (p4 ∨ p2)) ∨ (p5 ∨ False)) ∨ p1))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- False on the left can always be used.
        apply False.elim h12
      case inr h13 =>
        -- Conjunctions on the left can always be decomposed.
        let h14 := h13.left
        let h15 := h13.right
        -- Conjunctions on the left can always be decomposed.
        let h16 := h15.left
        let h17 := h15.right
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h17
    case inr h18 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_777078953374106813661687303729 : (((p1 ∨ ((True → (((((((p1 → p4) → p3) ∧ p1) ∨ (p3 → p3)) ∨ ((p1 ∨ p1) ∨ p5)) ∧ (p3 → False)) ∨ p2)) ∨ (p5 ∨ True))) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_116698747909216960696273431983 : (((False ∧ p3) ∨ ((p2 ∧ False) ∧ (p1 ∨ ((p2 ∧ ((p4 ∨ (((((p4 ∧ False) ∨ p5) → True) → p5) ∧ p1)) ∧ p1)) ∨ p1)))) ∨ (p2 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_139475344599048063272530644489 : ((((False ∨ (p1 ∨ (((p4 ∨ p1) ∧ ((p4 ∧ (p4 ∨ p1)) ∧ p2)) → ((True ∨ p2) ∨ (p3 ∧ p2))))) ∨ p4) → False) → (p2 ∨ (p5 ∧ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((False ∨ (p1 ∨ (((p4 ∨ p1) ∧ ((p4 ∧ (p4 ∨ p1)) ∧ p2)) → ((True ∨ p2) ∨ (p3 ∧ p2))))) ∨ p4) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h5.left
      let h8 := h5.right
      -- Conjunctions on the left can always be decomposed.
      let h9 := h7.left
      let h10 := h7.right
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h12 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h13 =>
      -- Conjunctions on the left can always be decomposed.
      let h14 := h5.left
      let h15 := h5.right
      -- Conjunctions on the left can always be decomposed.
      let h16 := h14.left
      let h17 := h14.right
      -- Disjunctions on the left can always be decomposed.
      cases h17
      case inl h18 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h19 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h20 := h1 h2
  -- False on the left can always be used.
  apply False.elim h20



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_96629974117902143623327215343 : ((False ∨ (True → ((((((((p5 → False) → (p1 → p3)) ∧ (p5 ∧ True)) ∨ p3) ∧ True) ∧ p5) ∨ (p3 ∧ p2)) ∧ ((p1 ∧ True) ∧ p4)))) → p1) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- False on the left can always be used.
    apply False.elim h2
  case inr h3 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h4 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h5 := h3 h4
    -- We need to get the right conjuct of h5 based on <expert-advice>.
    let h6 := h5.right
    -- We need to get the left conjuct of h6 based on <expert-advice>.
    let h7 := h6.left
    -- We need to get the left conjuct of h7 based on <expert-advice>.
    let h8 := h7.left
    -- One of the premise coincides with the conclusion.
    exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_194607714470864577433523659414 : ((((p2 ∨ ((p2 ∧ p1) ∨ True)) ∨ p1) ∨ p3) ∧ ((p3 ∧ ((((False ∧ p5) → ((False ∨ p3) → False)) ∧ p5) ∨ ((False → p5) → True))) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_325978597050878246132954926819 : (p5 ∨ (True → (((p4 ∧ p3) ∨ (((True ∧ ((p4 ∨ p5) ∨ ((((False ∧ (p2 ∨ True)) ∧ p5) → p2) ∨ p2))) ∧ p3) ∨ (False ∨ False))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135816014916631848135890696115 : (((((((p1 ∨ p3) → (p1 ∨ p5)) ∧ (p5 ∧ p4)) ∨ False) ∨ p2) ∧ (p1 → (False ∧ (p3 ∧ (p3 ∨ (p2 ∧ p2)))))) ∨ ((True ∨ False) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_612050268189285328712971323760 : ((((((False → (((p1 ∧ p1) → (p4 → p5)) → ((True → p2) ∧ (((p5 ∧ True) ∨ (p5 → p2)) → p3)))) → False) ∧ (p4 → False)) ∨ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317067625107849542295262293137 : (p3 ∨ (p4 → ((p1 ∧ p1) ∨ ((False ∧ (p1 ∨ (p1 → p4))) ∨ (p2 → (((p1 ∨ (p5 → (p4 ∧ p3))) → p5) → (p4 → (p1 → p2)))))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_610870159058157442404884764694 : ((((((((True → (p5 → p2)) → (False → (True → (p4 ∨ True)))) ∨ p2) ∧ (((p5 ∧ (p3 ∨ (True → p5))) → p3) → p4)) → p3) ∨ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112739382869978183376484847371 : (((((((p1 ∧ (p3 ∨ (p2 ∨ p1))) ∧ (p2 → p3)) ∨ p2) ∧ True) ∨ (((False → True) → (True ∧ p3)) ∨ (p1 ∨ p2))) → p1) ∨ (False → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_522013665083911904005674519563 : ((((p3 → False) → ((p2 ∨ ((True ∧ (((p1 ∧ p4) → ((p5 ∧ (False ∧ p3)) ∧ True)) ∧ ((p5 ∧ p3) ∧ (p3 ∨ False)))) ∨ True)) ∨ p3)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_708075241881921933863153832067 : ((((p4 ∨ ((p5 ∨ (p3 ∨ p3)) ∨ (False ∧ p2))) ∨ ((((p5 → p3) → p5) → p2) → ((((p2 ∨ True) ∧ True) ∨ p1) ∨ (p1 ∨ p4)))) ∨ p3) ∧ True) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_198376946764412934734059434691 : ((p3 ∧ ((p5 ∨ ((True ∧ True) → True)) → True)) ∨ (p4 ∨ ((True ∧ (p4 ∨ p4)) → ((((p1 ∧ ((p3 ∨ p2) ∨ p1)) ∧ False) ∨ p4) ∨ p1)))) := by
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
  cases h3
  case inl h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_316998116910585641584574817297 : (p3 ∨ (p3 → ((((p4 ∨ (p2 ∨ (False ∨ p1))) ∧ p4) ∧ p2) ∨ ((p5 ∨ (p3 ∧ True)) ∨ (p3 ∧ ((True ∨ p3) ∨ (p5 → (False ∧ False)))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160328130471383449120646784201 : ((((p2 → p2) → (p4 ∨ (p4 ∨ ((False ∨ ((p4 ∨ True) ∨ False)) ∨ (p5 ∨ p1))))) → (p4 ∨ p2)) → (p2 ∨ ((p3 → p4) ∧ (p2 → True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p2 → p2) → (p4 ∨ (p4 ∨ ((False ∨ ((p4 ∨ True) ∨ False)) ∨ (p5 ∨ p1))))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
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
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h6
    -- One of the premise coincides with the conclusion.
    exact h5
    -- Implications on the right can always be decomposed.
    intro h7
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h8 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_121754311531038003694873248737 : (((((p1 ∧ False) ∧ (p4 → p1)) ∨ ((True → (p2 ∨ ((((p3 ∧ p4) → p5) ∨ p2) ∧ p4))) → (p1 → (False → p4)))) → False) → (p5 → p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : (((p1 ∧ False) ∧ (p4 → p1)) ∨ ((True → (p2 ∨ ((((p3 ∧ p4) → p5) ∨ p2) ∧ p4))) → (p1 → (False → p4)))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- Implications on the right can always be decomposed.
    intro h6
    -- False on the left can always be used.
    apply False.elim h6
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h7 := h1 h3
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228944996323122540364450107541 : ((p4 ∨ (p5 ∨ p4)) ∨ ((((p4 ∨ p5) ∧ p5) ∨ (((p3 ∧ False) ∧ True) ∨ p2)) ∨ (((((True ∨ (p5 ∨ p3)) ∧ True) → p2) ∨ True) ∨ False))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_188647137259658825115205561664 : ((((p2 → ((p2 → p3) ∧ p5)) → False) ∨ (False → p4)) ∧ (False → ((p3 ∨ ((p3 → (p2 ∨ (p2 ∨ False))) ∧ (p4 → p4))) ∧ (False ∧ p2)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_335703916415172889551391083298 : (p1 → (((((p5 ∧ p4) ∨ p2) ∨ ((p3 ∨ (((False → p2) → p1) → (((p2 ∨ False) → (True ∧ p5)) ∨ False))) ∨ (True → p1))) ∨ True) ∧ p1)) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148926910142630112995102512982 : ((((False → p2) ∧ (p2 ∨ p1)) → (p1 → ((p3 ∨ ((p3 → p1) ∧ p2)) ∧ (((p3 ∧ p1) → p2) → True)))) ∨ ((p4 ∧ (p3 ∧ True)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48821466793706356015212239055 : (((p4 ∧ (p1 ∨ ((True ∧ (p4 → p5)) ∧ (((p5 ∨ ((p3 ∧ p3) ∨ (p3 → (False → p3)))) ∧ True) ∧ p1)))) ∧ ((p1 → True) → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304679061347402780610363658246 : (p1 ∨ ((((p1 ∧ (False → p5)) ∧ (False ∧ (p1 ∧ (((((p2 ∧ (p5 ∧ p2)) ∧ p4) ∧ p5) ∨ (p4 ∧ True)) ∧ p2)))) ∧ True) ∨ (p1 → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308715338278446782858151999729 : (p2 ∨ ((True → ((p4 ∧ (p1 → (p2 ∧ ((p4 ∧ (False ∨ True)) ∧ (p3 ∨ (p4 ∨ (True ∨ True))))))) ∨ (p1 → ((True ∨ True) → p3)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52602728143384130330248433390 : (((((True ∨ p2) ∧ ((p1 → p3) → p5)) → (p2 ∨ ((p4 ∨ p3) ∨ p3))) ∨ ((((False → False) ∨ (p5 → p1)) → p4) → (True ∨ p2))) ∨ p5) := by
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
theorem thm_5_vars_698965898412891314753841702073 : ((((p5 ∧ (True ∧ (p4 → (((False ∧ False) ∧ True) ∧ (p2 ∧ True))))) ∨ (False ∨ (((p2 ∧ p1) ∨ (p3 → p2)) ∧ ((p4 ∧ False) → p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_439842144118282543255697346393 : ((((((p3 ∨ (p4 ∨ ((((False → p5) → p2) → (p2 → p4)) ∧ (p4 ∧ p1)))) ∨ p1) ∨ (False → (p2 ∧ p3))) ∧ (True ∧ (p2 → True))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_886699139548007215754280846260 : ((((((((p2 → (p4 ∧ p3)) ∧ p2) → (p4 ∧ p5)) → ((p5 ∨ ((p5 → p2) → p2)) ∨ (p2 ∧ (p1 ∧ False)))) ∨ True) → (False ∧ p1)) → False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((((p2 → (p4 ∧ p3)) ∧ p2) → (p4 ∧ p5)) → ((p5 ∨ ((p5 → p2) → p2)) ∨ (p2 ∧ (p1 ∧ False)))) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the left conjuct of h3 based on <expert-advice>.
  let h4 := h3.left
  -- False on the left can always be used.
  apply False.elim h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198291296855368625456286743434 : ((p1 ∧ (((False ∧ p3) ∧ (p2 ∧ p1)) ∧ p2)) ∨ ((p4 ∨ (False → True)) ∧ ((False ∧ ((True → ((p2 ∨ p5) ∧ p1)) ∧ (p4 → p4))) → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114534413865487027622126799475 : (((True → ((True ∨ ((p4 → (False → p5)) → p2)) → (False ∨ ((p2 ∨ False) ∧ (False → p3))))) → (True → ((p3 ∨ True) ∨ p4))) ∨ (p2 ∨ p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150041016176245536386098974327 : ((p5 ∨ (p5 ∨ (p5 ∨ (p1 ∨ (p4 ∨ ((True ∨ ((((p2 → (p1 → p1)) ∧ p1) ∧ p3) ∧ p1)) ∨ p3)))))) ∨ (((p2 ∧ p5) ∨ True) ∧ p1)) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328541155874719540028922263463 : (True → ((((p3 → (p4 ∨ (False → p2))) ∨ ((True → p3) → ((p2 → p5) ∨ p1))) ∧ True) → ((p3 → p4) ∨ (False → (p5 ∨ (p4 ∧ p5)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- False on the left can always be used.
    apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_803385843074522404453038647778 : (((p3 → ((p5 ∧ (p4 ∧ (((p3 → ((p4 ∧ False) ∧ p2)) ∧ ((p2 ∨ (((p5 → False) → p3) ∧ False)) ∨ p3)) ∧ (p3 ∧ p4)))) ∨ p3)) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68793446338696438942025129873 : ((p4 → ((((p1 ∨ False) → p1) → (p2 ∨ p3)) ∨ ((p1 → (p2 ∧ (p3 ∨ p2))) → (((p4 ∨ p2) ∨ p1) ∨ ((p2 → p3) ∧ p2))))) ∨ p3) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60317879263064839945227516083 : (((p1 → p5) → ((False ∨ ((p5 ∧ (p4 ∧ (((False → p2) ∧ ((p2 → p1) ∧ p1)) ∧ True))) ∨ (p3 ∧ (p4 → (p3 → p2))))) ∨ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119124799321708742033488161558 : ((p1 → (p3 ∧ ((p1 ∧ (((p5 ∧ p3) ∧ (True → p5)) ∧ p1)) ∧ ((True → (p5 → (p2 ∨ (p4 ∨ False)))) ∧ (p2 ∧ False))))) ∨ (True → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_320451192813586855148941793847 : (p4 ∨ ((p5 ∨ True) → ((((p1 ∧ False) ∨ (p1 ∧ True)) → (p5 ∨ ((p4 ∧ (((p3 ∨ p5) ∨ (False ∧ p1)) ∨ p2)) ∨ False))) ∨ (p5 → p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64693926826561505736886089677 : ((p1 ∨ (True → (((p4 ∨ ((p4 → p5) ∨ ((False → p4) ∨ (p1 ∨ (p1 ∨ p1))))) ∧ ((False → False) ∨ p4)) → ((p2 ∨ p5) ∧ p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_730726884939228582439907234012 : ((((p3 ∧ (p5 → True)) → ((((((False ∨ (True → ((p3 ∧ p2) ∧ p4))) ∧ ((True ∧ True) → p1)) ∧ (p1 ∨ True)) → p4) → False) → p1)) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h5 : ((((False ∨ (True → ((p3 ∧ p2) ∧ p4))) ∧ ((True ∧ True) → p1)) ∧ (p1 ∨ True)) → p4) := by
    -- Implications on the right can always be decomposed.
    intro h6
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
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
      cases h8
      case inl h13 =>
        -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
        have h14 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h12, we can now drive its conclusion.
        let h15 := h12 h14
        -- We need to get the right conjuct of h15 based on <expert-advice>.
        let h16 := h15.right
        -- One of the premise coincides with the conclusion.
        exact h16
      case inr h17 =>
        -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
        have h18 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h12, we can now drive its conclusion.
        let h19 := h12 h18
        -- We need to get the right conjuct of h19 based on <expert-advice>.
        let h20 := h19.right
        -- One of the premise coincides with the conclusion.
        exact h20
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h21 := h2 h5
  -- False on the left can always be used.
  apply False.elim h21
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_778657400219316000961772815775 : (((p1 ∨ (p2 ∨ (((p5 → (p3 ∨ (p5 ∨ False))) ∧ (((p4 ∧ ((p4 ∧ p4) → (p2 ∧ p1))) ∨ (True ∧ (False ∧ p5))) → False)) → p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214797203674291157098847030748 : (((p1 ∨ p5) ∨ (p2 ∨ p3)) ∨ (((p5 → ((p2 → (True → p1)) ∧ p2)) → (p1 ∧ (((True → p5) ∧ ((p5 ∧ p1) ∧ p1)) → p3))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62355122881218658770334080984 : ((p3 ∧ (((p3 → (True ∧ (p4 ∧ (((False ∨ p2) ∨ (False → p5)) ∨ ((p4 ∨ p5) → False))))) ∧ True) ∨ (True ∧ ((p1 ∨ False) ∨ p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50710870479370639742940779190 : ((((p4 → p5) ∧ ((True ∨ (p3 ∨ (p5 ∨ p4))) ∧ (p2 ∧ (((True → (True ∨ True)) ∨ p2) ∧ p5)))) → (p4 ∨ ((p2 → p3) → p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_666184814482909605195721451840 : ((((((False ∨ ((True ∧ p2) → False)) ∧ (((((False → p1) → (p5 ∧ p3)) ∧ p5) → p3) → True)) ∨ (p3 ∧ p2)) ∧ ((p4 ∧ p2) ∨ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56138768134158408924832580213 : ((((p5 ∧ p3) → (True → p4)) ∨ ((((True → p1) → p4) ∨ (p1 ∧ (p4 → (((p4 → p5) ∨ (True → p5)) ∧ p2)))) ∨ (True ∨ False))) ∨ p1) := by
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
theorem thm_5_vars_167873139555378407370513823383 : ((((True → ((False ∧ p1) → p2)) ∧ (p4 ∨ (True ∧ True))) → (((p2 → p2) ∧ True) → p1)) → ((False ∧ p2) ∨ (((p4 → p2) → False) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165608444769089693587958150346 : ((((True → p4) → (True ∨ ((False ∧ True) ∨ False))) → ((False ∧ (False ∨ (p3 ∧ p2))) ∨ p5)) ∨ (((True ∧ p2) ∨ p2) → (p1 ∨ (p2 → True)))) := by
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
theorem thm_5_vars_114492303567327777930949850182 : (((((p2 ∧ p3) ∨ (((p3 → p1) → (p4 ∧ p3)) ∧ p5)) → (p3 → (False ∧ (p5 ∧ p3)))) → (((p1 ∧ False) ∨ False) ∨ True)) ∨ (True ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_262259115531723284498868582346 : (True ∧ (((p5 ∧ (((True ∨ False) → ((p3 ∨ (p3 → p1)) ∧ p4)) → (p5 ∧ ((p2 ∨ False) ∧ (p2 ∧ p4))))) ∨ ((False ∧ p5) → p1)) ∨ p2)) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152341082854009609130670046755 : (((((p1 ∧ p2) ∧ p2) ∧ p2) ∨ (((((True ∨ (p2 → (p3 ∧ p1))) → (p5 → p3)) ∨ True) → p2) ∨ p2)) → (((False ∧ True) ∧ False) ∨ p2)) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
      have h11 : (((True ∨ (p2 → (p3 ∧ p1))) → (p5 → p3)) ∨ True) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h10, we can now drive its conclusion.
      let h12 := h10 h11
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h12
    case inr h13 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_684388986408746904386458521213 : ((((((True ∧ ((p1 ∧ p5) ∨ ((p3 ∨ p3) → p1))) → p1) → (((False ∧ p1) ∨ p5) → False)) ∨ ((p4 ∧ p4) → ((p2 ∨ True) ∨ p5))) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_216734863533044122931497398912 : ((((p3 ∨ False) → p2) ∧ p3) → (p5 ∨ ((p2 → (True ∧ (p2 → ((p4 ∨ p5) → (True ∧ ((p2 ∧ p3) → (p2 ∧ False))))))) ∨ (p3 ∨ p2)))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_254588655828068936603126370305 : ((p3 ∧ p1) → ((True → ((p1 → ((p1 → ((((False → p2) ∧ p5) ∨ p2) → p5)) ∧ ((p2 ∨ p2) → p5))) ∨ True)) ∧ ((p3 ∧ p2) → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184691107514265941776700128440 : ((((p2 ∧ (p3 → (p1 → True))) ∧ True) → ((p4 ∨ False) ∧ False)) ∨ (p2 ∨ ((False ∧ False) → ((p1 → ((p2 ∨ p1) → False)) ∧ (False ∨ p5))))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h1.left
    let h6 := h1.right
    -- False on the left can always be used.
    apply False.elim h5
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h1.left
    let h9 := h1.right
    -- False on the left can always be used.
    apply False.elim h8
  -- Conjunctions on the left can always be decomposed.
  let h10 := h1.left
  let h11 := h1.right
  -- False on the left can always be used.
  apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55884799526564255639317406231 : (((p1 ∨ ((False ∧ False) → p1)) ∧ (p3 ∨ (True ∧ (((p5 ∧ ((p4 ∧ (p5 → p5)) → ((p5 ∨ True) → (p4 ∧ False)))) ∨ True) ∨ p4)))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  apply False.elim h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61616794749767926919282767994 : ((p1 ∧ ((p2 ∧ True) ∨ (((((p5 → (True → (p1 ∧ False))) ∨ p2) → p4) ∨ False) ∨ (p5 ∨ ((p1 ∧ p1) ∨ (p3 → (True ∧ False))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_719149783117723903059975661157 : ((((p1 ∧ (False ∧ (True → p5))) ∨ ((False ∨ ((p4 ∧ ((p5 ∧ p4) ∧ (True ∧ False))) ∧ ((True → p2) → True))) ∧ ((p5 ∧ False) → p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185395378241605765069952074687 : ((p5 ∧ (p5 → ((False → p1) ∧ (p3 ∨ (False ∨ (p4 → p3)))))) ∨ ((((False → (((p4 ∨ (p3 → True)) → p2) → True)) ∨ p4) → False) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111232359125341328880752588050 : ((((p5 ∧ p2) ∧ ((p4 ∨ p5) ∧ (p3 → (False ∨ (False → ((p3 ∨ p1) ∨ (p2 → (((p1 ∨ p4) → True) ∧ p2)))))))) ∧ p3) ∨ (False → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_517015153836280368070936865787 : ((((True ∧ True) → ((p4 → ((p4 → (((p3 → (p2 ∧ p5)) → p1) → ((((p3 → True) ∨ (p3 ∨ p4)) → p1) → False))) ∧ p3)) ∨ True)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179039193211476226468481529867 : (((True → p4) → ((p3 ∧ (((False ∧ p1) → p5) ∧ (p5 ∨ p1))) ∧ p5)) ∨ (True ∧ (p1 → ((p3 → ((p1 → (False ∨ p3)) → p1)) ∨ True)))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314745621635170471484274059261 : (p3 ∨ (((p1 ∨ ((p1 ∧ (p1 → p3)) ∨ (p2 ∨ p4))) ∨ ((p5 ∧ p2) → p2)) ∨ ((((p1 → False) ∨ (True ∧ p3)) ∧ (p1 → p2)) → p2))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191502750589744637863378161812 : ((False ∧ (((p1 → (True ∧ (p1 ∧ p1))) ∧ p4) ∨ p1)) ∨ (((((p1 → False) ∨ (p4 ∧ p2)) ∧ (p2 ∧ p5)) → ((True → p1) ∨ p5)) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h3.left
    let h11 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_761808484371275997308184644490 : (((p3 ∧ (((((p4 ∨ ((p2 ∧ (((p4 → p4) ∧ p4) ∨ p1)) ∨ (p2 → (((p2 ∨ p5) ∨ p1) ∨ p5)))) ∨ p2) → p5) ∨ True) → p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198199085730858170629867270048 : (((p2 → p2) → ((p3 ∨ (p4 → True)) → False)) ∨ (False ∨ ((((True ∧ ((False → (True ∨ False)) → p3)) ∧ p3) → ((False ∨ p1) ∨ True)) ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_24957391202774564917868678613 : (((False ∧ (p2 ∧ p2)) ∨ ((False ∨ p1) ∨ ((p2 ∨ p1) → (p1 → (((p4 ∨ ((p2 ∧ p1) → (True ∨ p2))) ∨ (p2 ∧ p5)) ∨ p4))))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h7 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115232656497184076260766332361 : ((((((p1 ∧ p4) ∨ True) → ((p3 ∧ True) ∨ p3)) ∨ p5) ∨ (p5 → (((p4 ∨ p4) ∧ (p2 ∧ p2)) ∧ (p5 ∧ (p4 ∨ p3))))) ∨ (p5 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_216767417982029562771611747647 : ((((p5 → True) → p2) ∧ p5) → (((p3 → p4) → ((p4 → (((p2 → True) ∨ p5) → ((False → (p2 ∨ False)) → p3))) ∨ p4)) ∨ (p5 ∧ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h3
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (p5 → True) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h4
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138247116996934159439264106795 : ((p2 → ((p4 → (p3 → p3)) → ((((p5 ∨ False) ∧ ((p3 ∨ ((True ∧ p2) ∧ p1)) ∧ False)) ∧ True) ∧ (p5 ∧ p1)))) ∨ (p3 ∨ (p2 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256711490908350668734550954405 : ((p1 ∨ p1) → ((p4 ∧ (p5 ∧ ((p1 ∧ (False ∨ p3)) ∨ ((p1 ∧ p1) → ((p1 → (False ∨ (p4 → p3))) → (True → p5)))))) ∨ (True ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233285386021288215828033685247 : ((True ∨ (False ∨ p3)) → ((p2 ∨ p5) ∨ ((p5 ∨ ((p5 ∨ (p3 ∨ (p1 → True))) ∨ (p5 ∨ ((p5 → p3) ∧ (p1 → p5))))) ∨ (p4 ∧ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- False on the left can always be used.
      apply False.elim h5
    case inr h6 =>
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65120498674745061740939159378 : ((p2 ∨ (True → ((p3 ∨ p3) ∧ ((p4 ∨ (False → True)) ∧ ((((True → True) ∧ (True → p2)) ∨ ((p1 → (p3 ∧ True)) ∨ p2)) ∨ p5))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_714406642489504700055889272655 : ((((((p5 ∧ p1) → p4) → (p2 ∨ False)) → (False ∨ ((p4 ∨ (((False ∨ p4) ∧ p3) ∧ p3)) → ((((False → True) ∨ p2) ∨ p1) ∧ p2)))) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h4
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h6.left
    let h9 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h10 =>
      -- False on the left can always be used.
      apply False.elim h10
    case inr h11 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h12
      -- True on the right can always be proven directly.
      apply True.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h13 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h14 : ((p5 ∧ p1) → p4) := by
      -- Implications on the right can always be decomposed.
      intro h15
      -- Conjunctions on the left can always be decomposed.
      let h16 := h15.left
      let h17 := h15.right
      -- One of the premise coincides with the conclusion.
      exact h13
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h18 := h1 h14
    -- Disjunctions on the left can always be decomposed.
    cases h18
    case inl h19 =>
      -- One of the premise coincides with the conclusion.
      exact h19
    case inr h20 =>
      -- False on the left can always be used.
      apply False.elim h20
  case inr h21 =>
    -- Conjunctions on the left can always be decomposed.
    let h22 := h21.left
    let h23 := h21.right
    -- Conjunctions on the left can always be decomposed.
    let h24 := h22.left
    let h25 := h22.right
    -- Disjunctions on the left can always be decomposed.
    cases h24
    case inl h26 =>
      -- False on the left can always be used.
      apply False.elim h26
    case inr h27 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h28 : ((p5 ∧ p1) → p4) := by
        -- Implications on the right can always be decomposed.
        intro h29
        -- Conjunctions on the left can always be decomposed.
        let h30 := h29.left
        let h31 := h29.right
        -- One of the premise coincides with the conclusion.
        exact h27
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h32 := h1 h28
      -- Disjunctions on the left can always be decomposed.
      cases h32
      case inl h33 =>
        -- One of the premise coincides with the conclusion.
        exact h33
      case inr h34 =>
        -- False on the left can always be used.
        apply False.elim h34
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54112878290872252618093885859 : (((p3 ∧ (p5 → ((((p1 → p3) ∧ p5) → p4) → p2))) → ((((p5 ∧ p3) ∨ p5) ∧ p4) ∨ ((((True ∨ p4) → p2) ∨ False) → p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_621512963638954966381249506437 : ((((False ∧ ((((p2 ∧ ((False ∧ p3) ∨ ((False ∧ (True → (p5 ∨ True))) ∧ p2))) ∨ ((p5 → False) → False)) ∨ p1) ∧ (p4 ∧ p1))) ∨ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164518178335138189161890249799 : (((((p5 ∨ True) ∧ ((True ∧ (True ∨ (p1 ∧ (False → False)))) → p2)) ∨ (p5 ∨ p5)) ∧ p4) ∨ ((p5 ∧ (p1 ∧ (p5 → (p5 ∨ False)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66788311310570148525304512225 : ((True → (False ∨ (p2 ∨ ((((((((p2 → (True ∧ False)) ∧ (p4 ∨ (p3 ∨ (False ∨ p3)))) ∧ p2) ∨ p1) ∧ True) ∨ True) ∨ p4) ∨ p5)))) ∨ False) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181431159032652226151564067974 : ((p3 ∨ (((p3 ∨ (p5 ∧ ((p3 → True) → (False → p3)))) ∨ p1) ∨ True)) → ((((p4 ∧ p4) ∨ (p5 ∨ False)) → (True → False)) → (p5 → p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h4 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h5 : ((p4 ∧ p4) ∨ (p5 ∨ False)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h3
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h6 := h2 h5
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h7 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h8 := h6 h7
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- Disjunctions on the left can always be decomposed.
        cases h11
        case inl h12 =>
          -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
          have h13 : ((p4 ∧ p4) ∨ (p5 ∨ False)) := by
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h3
          -- We have shown the premise of h2, we can now drive its conclusion.
          let h14 := h2 h13
          -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
          have h15 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h14, we can now drive its conclusion.
          let h16 := h14 h15
          -- False on the left can always be used.
          apply False.elim h16
        case inr h17 =>
          -- Conjunctions on the left can always be decomposed.
          let h18 := h17.left
          let h19 := h17.right
          -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
          have h20 : ((p4 ∧ p4) ∨ (p5 ∨ False)) := by
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h18
          -- We have shown the premise of h2, we can now drive its conclusion.
          let h21 := h2 h20
          -- We want to use the implication h21 based on <expert-advice>. So we show its premise.
          have h22 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h21, we can now drive its conclusion.
          let h23 := h21 h22
          -- False on the left can always be used.
          apply False.elim h23
      case inr h24 =>
        -- One of the premise coincides with the conclusion.
        exact h24
    case inr h25 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h26 : ((p4 ∧ p4) ∨ (p5 ∨ False)) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h3
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h27 := h2 h26
      -- We want to use the implication h27 based on <expert-advice>. So we show its premise.
      have h28 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h27, we can now drive its conclusion.
      let h29 := h27 h28
      -- False on the left can always be used.
      apply False.elim h29



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_803006395080268140329515508806 : (((p3 → ((((p1 ∨ p5) ∨ (p5 ∨ (True ∨ ((p4 ∨ True) → ((True → p4) ∨ (p1 ∧ False)))))) → ((p3 ∨ (False → p3)) → p1)) ∧ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191362709303657320464543959031 : (((p5 ∨ False) ∨ (p3 → (((p4 ∨ p2) ∧ p5) ∨ p4))) ∨ (((p2 ∧ ((p2 → p3) → False)) ∧ (((p5 → (p1 ∧ p2)) ∧ p3) ∨ p4)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_768143925347727418271580216649 : (((p5 ∧ ((p5 ∧ ((p2 ∨ p3) ∧ ((p5 → ((True → ((True → p1) → (False ∨ p5))) → (False ∨ p1))) ∧ (p3 ∧ p4)))) ∨ (False → p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_591957421104343069320905447731 : ((((((p2 ∧ p2) ∧ ((p5 → (False → True)) → ((p5 ∨ (p4 ∨ True)) ∧ ((False → (False ∧ (p1 → p2))) → p1)))) ∨ (p3 ∧ p4)) ∧ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



