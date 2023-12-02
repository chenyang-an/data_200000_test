variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41700659420759975439242718321 : ((((((p1 → p5) → True) ∨ (True ∧ False)) → ((True ∧ ((p1 ∨ p1) → p5)) ∨ ((True → (p1 ∧ p4)) ∨ ((True ∨ False) ∧ p4)))) ∨ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_69147395379490490881139157284 : ((p5 → (((p3 ∧ ((((p4 ∨ (p4 ∨ ((p4 ∨ (True ∨ p5)) → p2))) ∨ (p2 ∧ p1)) ∧ p5) → p1)) → True) → (True → (p2 ∨ True)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117319469120867034585855303154 : ((False ∧ (((p3 ∨ (p1 ∧ (p4 ∧ True))) ∧ ((p3 ∧ p3) → True)) ∧ ((False ∨ p2) ∨ ((((p3 → False) ∨ p1) ∨ p1) ∨ p3)))) ∨ (True ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150800352886241285495308695207 : ((((True ∨ (((True ∧ ((False ∨ p3) → True)) ∧ ((p2 → p4) ∧ p3)) ∨ (p4 → p2))) ∧ (p2 ∨ True)) ∨ p1) → (((p3 ∨ False) ∨ p4) ∨ True)) := by
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
    case inr h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Conjunctions on the left can always be decomposed.
        let h10 := h9.left
        let h11 := h9.right
        -- Conjunctions on the left can always be decomposed.
        let h12 := h10.left
        let h13 := h10.right
        -- Conjunctions on the left can always be decomposed.
        let h14 := h11.left
        let h15 := h11.right
        -- Disjunctions on the left can always be decomposed.
        cases h4
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
        -- Disjunctions on the left can always be decomposed.
        cases h4
        case inl h19 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
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
theorem thm_5_vars_299317960161829717127483171186 : (False ∨ ((((p4 → p5) ∨ ((False → p3) ∧ p2)) ∨ (((True ∨ (p5 ∨ True)) ∧ ((True ∧ p4) ∧ (p1 ∨ p2))) ∨ ((True ∨ p2) ∨ p2))) ∨ p2)) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159056171614771451218800921018 : ((p5 ∨ ((((p3 → (p2 ∧ p2)) → ((p1 ∧ p5) → p3)) → p1) ∨ ((p1 ∧ p4) ∨ (False → p5)))) ∨ ((True ∨ (False ∨ p3)) ∨ (p2 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336241454385336290496096629037 : (p1 → (((((((True ∨ ((p2 ∨ (True ∨ False)) ∧ p5)) ∧ p1) ∧ p5) ∨ False) ∧ ((p4 → False) ∧ p3)) ∨ (((True → p3) ∧ p2) ∧ p5)) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_726324380349718622279794535493 : (((((p3 ∨ p3) ∨ p3) ∨ ((p4 ∨ p5) ∨ ((p2 ∨ ((True → p3) → (((p3 ∧ False) ∧ p1) ∨ ((p2 → p1) ∨ p3)))) → (p5 → p5)))) ∨ p2) ∧ True) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h4 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200487766048017669753001246378 : (((p1 ∧ p3) → ((True ∧ False) ∨ (False ∨ False))) → ((True → (True ∧ (p4 ∧ False))) → (((False ∨ p4) ∧ (p4 ∧ p3)) ∧ (True ∧ (p1 ∨ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- False on the left can always be used.
  apply False.elim h6
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h7 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h8 := h2 h7
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- We need to get the left conjuct of h9 based on <expert-advice>.
  let h10 := h9.left
  -- One of the premise coincides with the conclusion.
  exact h10
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h11 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h12 := h2 h11
  -- We need to get the right conjuct of h12 based on <expert-advice>.
  let h13 := h12.right
  -- We need to get the right conjuct of h13 based on <expert-advice>.
  let h14 := h13.right
  -- False on the left can always be used.
  apply False.elim h14
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_151460649872445397857020328982 : (((((((True ∨ (p5 → p5)) → p4) → p4) ∨ ((False → (True → False)) ∨ (p5 → p4))) ∨ True) ∨ (p1 → p5)) → (((p2 ∨ True) → p1) ∨ True)) := by
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
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62034506716600825487940865866 : ((p2 ∧ ((p1 ∨ p5) ∧ (p1 ∨ (((p5 → False) → (((p1 ∧ False) ∨ (p4 ∧ p5)) → ((p4 ∨ (p3 ∧ (True → False))) ∧ p1))) ∧ p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_14457069297141056571841732961 : (((((((p3 ∨ (p2 → p3)) ∨ p3) ∨ ((p4 ∧ (p4 ∧ (True ∨ p1))) → (p2 → (p1 ∨ (p3 ∨ False))))) → p5) ∧ p2) ∨ (False → p3)) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193820239621125886072376687572 : ((p5 ∧ (((True ∧ p5) ∨ p3) → ((p5 ∨ p1) ∧ p3))) → ((p1 → ((p1 ∨ (p3 ∨ p4)) ∨ p4)) ∧ (p1 ∨ (p3 ∧ ((False ∨ p3) → p5))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Conjunctions on the left can always be decomposed.
  let h5 := h1.left
  let h6 := h1.right
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h7 : ((True ∧ p5) ∨ p3) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h8 := h6 h7
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h9
  -- Implications on the right can always be decomposed.
  intro h10
  -- Disjunctions on the left can always be decomposed.
  cases h10
  case inl h11 =>
    -- False on the left can always be used.
    apply False.elim h11
  case inr h12 =>
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111757173159789332340989906411 : (((((((p4 → p2) ∨ p5) ∧ ((((p4 ∨ (p2 ∨ p3)) → (p4 ∨ p4)) → p1) ∧ (p2 ∨ p4))) ∨ p1) ∧ (True ∧ p5)) ∨ p2) ∨ (p4 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_690435527177587619077333855871 : ((((((((p4 → ((p1 ∨ p5) ∨ (p2 ∧ p3))) ∨ True) → (False → False)) → False) ∧ True) → (p1 ∨ (p4 ∧ ((True → p3) → (p3 ∧ False))))) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (((p4 → ((p1 ∨ p5) ∨ (p2 ∧ p3))) ∨ True) → (False → False)) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- Implications on the right can always be decomposed.
    intro h6
    -- False on the left can always be used.
    apply False.elim h6
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h7 := h2 h4
  -- False on the left can always be used.
  apply False.elim h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118429856680116053929129554021 : ((p2 ∨ (p5 ∨ (((((True ∧ p3) ∨ p2) ∧ (p5 ∧ (((p5 ∨ True) ∧ (p4 ∧ (True → True))) → p3))) ∨ (p4 ∨ p5)) ∨ True))) ∨ (p4 ∧ p5)) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_728220325845862592540168379337 : ((((True → (p1 ∨ p4)) ∨ (((False ∧ ((p2 → False) ∨ (p4 ∨ (p5 → (p2 ∨ (p3 ∨ (False ∧ (p2 → (True ∧ p2))))))))) → p2) → p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136859845630130093526976217262 : (((p5 ∧ p2) ∨ ((p1 ∧ p4) ∧ ((False → (((False → p5) ∧ p2) ∨ (p3 → p5))) ∧ (p5 ∨ ((p5 → p4) ∧ False))))) ∨ ((p1 ∧ p5) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299382915383918348965526326051 : (False ∨ (((p3 ∨ True) → ((p1 ∨ (((True ∧ True) ∨ ((p4 → False) → ((p2 ∨ p5) → p4))) ∧ ((True ∨ p4) → p1))) → (p4 → p1))) ∨ p2)) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h5 =>
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h6 =>
      -- One of the premise coincides with the conclusion.
      exact h4
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h13 =>
        -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
        have h14 : (True ∨ p4) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h9, we can now drive its conclusion.
        let h15 := h9 h14
        -- One of the premise coincides with the conclusion.
        exact h15
      case inr h16 =>
        -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
        have h17 : (True ∨ p4) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h9, we can now drive its conclusion.
        let h18 := h9 h17
        -- One of the premise coincides with the conclusion.
        exact h18
    case inr h19 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h20 =>
        -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
        have h21 : (True ∨ p4) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h9, we can now drive its conclusion.
        let h22 := h9 h21
        -- One of the premise coincides with the conclusion.
        exact h22
      case inr h23 =>
        -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
        have h24 : (True ∨ p4) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h9, we can now drive its conclusion.
        let h25 := h9 h24
        -- One of the premise coincides with the conclusion.
        exact h25



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305218905962645731480580125325 : (p1 ∨ ((((True → p1) ∧ (p1 → ((((p1 ∨ p5) ∧ (p1 → p4)) ∧ p5) ∧ p2))) ∨ (False ∧ (p1 → p2))) → ((p4 → p2) ∧ (p5 ∨ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h6 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h7 := h4 h6
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h8 : p1 := by
      -- One of the premise coincides with the conclusion.
      exact h7
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h9 := h5 h8
    -- We need to get the right conjuct of h9 based on <expert-advice>.
    let h10 := h9.right
    -- One of the premise coincides with the conclusion.
    exact h10
  case inr h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- False on the left can always be used.
    apply False.elim h12
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h14 =>
    -- Conjunctions on the left can always be decomposed.
    let h15 := h14.left
    let h16 := h14.right
    -- We want to use the implication h15 based on <expert-advice>. So we show its premise.
    have h17 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h15, we can now drive its conclusion.
    let h18 := h15 h17
    -- We want to use the implication h16 based on <expert-advice>. So we show its premise.
    have h19 : p1 := by
      -- One of the premise coincides with the conclusion.
      exact h18
    -- We have shown the premise of h16, we can now drive its conclusion.
    let h20 := h16 h19
    -- We need to get the left conjuct of h20 based on <expert-advice>.
    let h21 := h20.left
    -- We need to get the right conjuct of h21 based on <expert-advice>.
    let h22 := h21.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h22
  case inr h23 =>
    -- Conjunctions on the left can always be decomposed.
    let h24 := h23.left
    let h25 := h23.right
    -- False on the left can always be used.
    apply False.elim h24



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_318869113051513956601933493322 : (p4 ∨ (((((p3 → ((p2 ∨ p5) ∨ (p1 → p3))) → (p4 ∧ (p3 ∨ (p5 ∨ p4)))) ∨ True) ∨ (p2 ∨ (p1 ∧ p1))) ∨ ((p5 ∨ p5) → False))) := by
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
theorem thm_5_vars_775607315501927357592678076626 : (((False ∨ (False ∨ (((p1 ∨ p3) → (((p1 → (((False ∧ (False ∧ True)) ∨ (p4 ∨ p2)) → True)) ∨ (True ∨ p4)) ∧ p1)) → (p3 → p1)))) ∨ p2) ∧ True) := by
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
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : (p1 ∨ p3) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- One of the premise coincides with the conclusion.
  exact h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65004076764893874416987166750 : ((p2 ∨ ((True → (p4 ∨ p4)) → (((p2 ∧ (False ∨ (p2 ∨ p5))) ∨ ((p2 → p4) ∨ (True ∧ ((p2 ∨ (p3 ∨ p2)) ∨ p5)))) ∨ p2))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246342807166218541116676196761 : ((p4 ∧ p5) ∨ ((p2 → ((p1 → True) → p3)) ∨ ((p3 ∧ False) ∨ ((p3 ∧ (((p5 → p2) ∧ (p2 ∨ p1)) → p4)) → (p3 ∧ (False → True)))))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149032001932373937290486099436 : (((False ∧ (p4 ∨ False)) ∨ ((((((p1 → p5) ∧ (p1 ∨ p5)) ∨ True) ∨ False) → (p4 → p2)) ∨ (p3 ∧ True))) ∨ (((p1 ∧ True) → True) ∧ True)) := by
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
theorem thm_5_vars_181205697174865264030619436573 : ((p2 ∧ ((((p4 → p5) ∧ p5) → (p5 ∨ p3)) ∧ ((p1 → p2) → False))) → (p1 ∨ (p5 → (p3 ∧ ((((False → p1) ∧ p4) → p5) → p3))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h6 : (p1 → p2) := by
    -- Implications on the right can always be decomposed.
    intro h7
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h8 := h5 h6
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134360103146111728282382936389 : (((False ∨ (p2 ∨ (((((p1 ∧ p1) ∨ ((False ∨ p1) ∧ (True ∧ p2))) ∨ p5) → False) ∨ (p2 ∨ (p3 ∧ p2))))) ∨ p3) ∨ (True → (True ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_807220130782353670517880160430 : (((p4 → ((p4 → ((((True ∧ p2) → p2) ∧ (((p3 ∨ (True ∨ p3)) ∧ False) → p3)) ∨ p2)) → (p5 ∧ (p3 → ((p5 ∨ True) ∧ p5))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_683077828474065554751304456471 : ((((p1 ∧ (((p4 ∨ ((True ∧ (True ∨ ((p3 → (p3 ∨ True)) ∧ True))) ∨ p3)) ∨ False) ∨ p5)) ∧ ((p5 ∧ False) ∨ ((p4 ∧ p4) ∨ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_805605713686637980765931557282 : (((p3 → (True → ((p3 ∧ ((True → (p1 ∧ ((p4 ∨ p3) ∧ p5))) → (False ∨ p1))) ∧ (((True ∨ p3) ∧ p1) → (p5 ∧ (p5 ∨ p1)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_640889852717441917356388905983 : (((((p5 → False) ∧ ((p3 ∨ p1) ∧ (p4 ∨ (((((p1 ∨ True) → p4) ∧ p3) ∨ p5) ∨ ((p3 → (p1 ∨ (True ∧ p4))) → p2))))) → p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_266032728908394799997523873988 : (True ∧ (p1 → ((p5 ∨ False) ∨ ((p3 ∧ (((p4 ∧ True) ∨ ((True → (True ∨ (False → False))) ∧ p4)) ∨ True)) ∨ ((p4 ∧ p1) → (p1 ∨ p5)))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200457035601387850437463628372 : (((p1 → p4) ∨ ((p2 → (False → True)) ∧ False)) → (((p1 → (p1 ∧ p5)) → (p3 ∧ p2)) ∨ ((p2 ∨ True) ∨ ((p2 ∨ (True → p4)) → p5)))) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322347854091614801184566940640 : (p5 ∨ ((((((p4 → False) ∨ p3) ∨ (((p3 → p4) → (False ∧ (True → (p1 ∧ (p1 ∨ False))))) → p1)) ∧ p4) ∧ ((p1 ∧ False) ∨ p2)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_429548642810692913280965592029 : (((((p5 ∧ (((((True → ((True ∧ p5) ∧ p1)) ∧ p1) ∨ p5) → p2) ∧ (p4 → p5))) → ((True → (False → False)) → p1)) ∨ (True ∨ p5)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_56235873386216264566516183689 : (((p5 ∨ ((p3 ∧ False) ∨ p2)) ∨ (((p1 ∨ (p2 ∨ (True → p3))) ∨ (((True ∧ p4) → True) → (p3 ∧ p3))) → ((p4 → p1) → p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54272249109889543755266891640 : ((((p3 ∨ (p1 → p4)) ∧ ((True ∨ True) → p5)) ∧ (p1 ∨ (((p3 → (p2 ∨ p1)) ∧ (p1 → (False ∨ p4))) ∧ ((p3 → p1) ∨ p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_229161054757483054435194672768 : ((True → (p2 ∨ False)) ∨ ((p4 ∨ (((p1 ∧ ((((p4 ∧ p2) → p1) → p5) ∧ p4)) ∨ p4) ∨ p5)) → (((p3 → p1) ∨ True) ∧ (False → p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
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
        -- Conjunctions on the left can always be decomposed.
        let h6 := h5.left
        let h7 := h5.right
        -- Conjunctions on the left can always be decomposed.
        let h8 := h7.left
        let h9 := h7.right
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
  -- Implications on the right can always be decomposed.
  intro h12
  -- False on the left can always be used.
  apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41809425336412862545497795631 : (((((p1 ∧ p2) ∧ p1) ∧ (((False → p5) ∨ False) ∧ (((p4 ∨ True) ∨ (((p3 → ((p5 ∧ p2) ∨ p2)) ∨ p3) → False)) ∧ p5))) ∨ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_629253674649739686385085954175 : (((((((((False → (((p3 ∧ p5) → p5) ∨ p2)) ∨ ((False ∧ (p3 → p3)) → ((p1 → p2) ∧ p5))) ∨ p5) ∨ p4) → p4) ∨ p4) → p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206478548515383693817901011645 : ((p5 ∨ ((p2 ∧ (False ∧ p4)) ∧ p5)) ∨ (((p4 ∨ (p1 ∨ ((False → (True → p3)) ∧ ((False ∧ True) ∨ (False ∨ (p2 → p1)))))) ∧ p4) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147263902274570900667607972709 : ((((((p3 ∨ (False ∨ True)) → (((p3 ∧ ((p2 → False) → True)) ∨ (p5 → False)) → False)) ∨ p2) ∨ p1) ∨ p3) ∨ (p4 ∨ (False → (p3 ∧ p5)))) := by
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
theorem thm_5_vars_112524995066410904813931940173 : (((((p4 → ((((p4 ∨ p2) ∧ p4) → ((p4 ∧ True) ∧ p3)) ∨ (p1 ∧ (((p3 ∧ p2) ∨ True) ∨ p1)))) → p3) → False) → p4) ∨ (p5 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204870105966087978778694294122 : ((((p4 ∧ (p4 ∧ True)) → False) → p1) ∨ (False ∨ (p1 → ((p5 ∧ ((p2 → (True ∨ True)) ∧ p5)) ∨ (p5 → (((True → True) ∨ False) → p5)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115331467376801726827724119115 : (((p2 ∧ (((p5 → (False ∨ p5)) ∧ (p4 ∨ p5)) ∨ p4)) → ((((((p1 ∧ (True ∧ p3)) ∨ True) ∧ p3) ∧ p1) → True) ∧ p1)) ∨ (True ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308484690469843020291537685672 : (p2 ∨ (((((p5 ∧ ((p4 → (((((p2 → p1) ∨ False) ∨ p3) → (p1 → False)) → p4)) → p3)) ∨ True) ∧ True) ∨ ((p1 ∨ p3) ∨ True)) ∨ p1)) := by
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
theorem thm_5_vars_391618180559391780486408667758 : (((((p3 ∨ ((True ∨ p3) → p2)) ∧ ((p2 ∧ (((p3 ∧ p4) ∧ p1) → True)) → (((p1 ∧ (True ∨ True)) → (True → p5)) ∨ p5))) ∨ True) ∧ True) ∧ True) := by
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
theorem thm_5_vars_157140150326546195708940842102 : (((((((p3 → p1) ∨ ((p1 ∧ (((p4 → p2) ∨ p1) ∧ p4)) ∨ True)) ∧ p4) ∧ p4) ∨ p3) → p5) ∨ (((p4 ∨ True) → p1) → (True ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135687667375260439545574036527 : ((((((((False → p5) → p1) → (p5 → p2)) → (True → p5)) → p3) → False) ∧ ((p4 → (False ∨ (p3 ∨ p5))) → True)) ∨ (p1 → (False ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133808974812617598378014128432 : ((((True ∨ False) ∧ (p1 ∨ (p5 → ((((((p4 ∧ False) ∨ p4) ∨ p2) ∨ ((p1 ∧ p2) ∨ p4)) ∨ p2) → p2)))) ∧ p5) ∨ ((p5 ∨ p1) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_639710048719138559255154998762 : (((((True → (p4 ∧ p3)) ∧ ((((False ∧ p3) ∨ ((p2 → (p5 ∧ p2)) → p4)) ∨ (p1 ∨ p1)) ∧ (p5 ∨ ((p1 → p2) ∨ p2)))) → p3) ∨ p1) ∧ True) := by
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
  let h4 := h3.left
  let h5 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- False on the left can always be used.
      apply False.elim h8
    case inr h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h11 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h12 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h13 := h2 h12
        -- We need to get the right conjuct of h13 based on <expert-advice>.
        let h14 := h13.right
        -- One of the premise coincides with the conclusion.
        exact h14
      case inr h15 =>
        -- Disjunctions on the left can always be decomposed.
        cases h15
        case inl h16 =>
          -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
          have h17 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h2, we can now drive its conclusion.
          let h18 := h2 h17
          -- We need to get the right conjuct of h18 based on <expert-advice>.
          let h19 := h18.right
          -- One of the premise coincides with the conclusion.
          exact h19
        case inr h20 =>
          -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
          have h21 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h2, we can now drive its conclusion.
          let h22 := h2 h21
          -- We need to get the right conjuct of h22 based on <expert-advice>.
          let h23 := h22.right
          -- One of the premise coincides with the conclusion.
          exact h23
  case inr h24 =>
    -- Disjunctions on the left can always be decomposed.
    cases h24
    case inl h25 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h26 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h27 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h28 := h2 h27
        -- We need to get the right conjuct of h28 based on <expert-advice>.
        let h29 := h28.right
        -- One of the premise coincides with the conclusion.
        exact h29
      case inr h30 =>
        -- Disjunctions on the left can always be decomposed.
        cases h30
        case inl h31 =>
          -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
          have h32 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h2, we can now drive its conclusion.
          let h33 := h2 h32
          -- We need to get the right conjuct of h33 based on <expert-advice>.
          let h34 := h33.right
          -- One of the premise coincides with the conclusion.
          exact h34
        case inr h35 =>
          -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
          have h36 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h2, we can now drive its conclusion.
          let h37 := h2 h36
          -- We need to get the right conjuct of h37 based on <expert-advice>.
          let h38 := h37.right
          -- One of the premise coincides with the conclusion.
          exact h38
    case inr h39 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h40 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h41 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h42 := h2 h41
        -- We need to get the right conjuct of h42 based on <expert-advice>.
        let h43 := h42.right
        -- One of the premise coincides with the conclusion.
        exact h43
      case inr h44 =>
        -- Disjunctions on the left can always be decomposed.
        cases h44
        case inl h45 =>
          -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
          have h46 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h2, we can now drive its conclusion.
          let h47 := h2 h46
          -- We need to get the right conjuct of h47 based on <expert-advice>.
          let h48 := h47.right
          -- One of the premise coincides with the conclusion.
          exact h48
        case inr h49 =>
          -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
          have h50 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h2, we can now drive its conclusion.
          let h51 := h2 h50
          -- We need to get the right conjuct of h51 based on <expert-advice>.
          let h52 := h51.right
          -- One of the premise coincides with the conclusion.
          exact h52
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_804790477062464558904929720939 : (((p3 → ((True ∨ (p5 ∧ p1)) → (p2 → (p1 → ((((p4 → True) → (p5 → p5)) ∨ p2) → ((p3 → p4) ∨ (p1 ∧ (p3 ∧ True)))))))) ∨ p2) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h5
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h4
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h1
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h10
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h1
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h4
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h1
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h13 =>
      -- Conjunctions on the left can always be decomposed.
      let h14 := h13.left
      let h15 := h13.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h15
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h1
      -- True on the right can always be proven directly.
      apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198379737352473018770509939361 : ((p3 ∧ (((p3 ∧ p2) ∨ p5) ∨ (p2 ∧ True))) ∨ (((p2 ∨ (p1 → p3)) ∨ (p4 ∧ (p1 ∨ (False ∧ (p4 ∧ (p3 ∧ (True → p1))))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65743836053478168745200650088 : ((p4 ∨ ((False ∨ ((p5 ∧ (p5 ∧ (p3 ∧ p1))) ∨ ((False ∨ ((((True → True) ∧ True) ∧ p3) ∧ p3)) → p2))) ∨ (True ∨ (False ∧ True)))) ∨ p3) := by
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
theorem thm_5_vars_323799666679330368457533213152 : (p5 ∨ ((((False → False) ∨ p2) → (p2 → (p5 ∨ (True ∧ (p5 → (p4 ∨ (p3 ∧ (p2 ∧ True)))))))) ∨ (True ∨ (((p2 ∧ True) ∨ p3) ∧ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64128210685756069242509743937 : ((False ∨ (((p5 ∧ (p5 → p5)) ∨ False) ∨ ((p5 ∨ (p4 → ((p5 ∨ p5) ∨ False))) ∨ (p5 ∨ ((((p4 → p3) ∧ p4) ∧ p1) → p4))))) ∨ p4) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263490627879909990159171618725 : (True ∧ ((p2 ∨ (False → ((p5 ∧ (False ∧ True)) → ((((p2 ∧ (p2 ∨ p3)) → p5) → (p2 ∧ p4)) ∨ (p2 → p4))))) → ((p5 → p1) ∨ True))) := by
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
theorem thm_5_vars_314231957262783678346707375130 : (p3 ∨ (((p3 ∧ (p4 → (((p5 → p5) ∨ p3) → (p3 ∧ ((p2 ∨ False) ∨ ((True ∨ (p3 ∧ p4)) ∨ p3)))))) ∨ p5) ∨ (p2 → (p4 ∨ p2)))) := by
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
theorem thm_5_vars_50760931363464256742002627405 : (((True ∨ ((p4 → (p2 → ((((p1 ∧ p2) → (p4 → (p2 ∨ p2))) ∨ (p3 ∧ p3)) ∧ p5))) ∧ p5)) → ((p3 ∨ (p1 ∨ p4)) ∨ True)) ∨ False) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137414469531234965267507351467 : ((p4 ∧ (((((p1 ∧ p3) ∧ ((p1 ∧ (p3 → True)) → p1)) ∧ True) → ((((p5 ∨ True) ∨ p2) ∧ p3) ∧ False)) ∧ p5)) ∨ (p3 → (p4 → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171401461821047649448213447474 : (((((p3 ∧ (p2 ∨ False)) ∨ p5) ∨ (((p2 ∧ p4) ∨ (p4 ∨ p3)) → p5)) ∧ True) ∨ ((p5 ∧ False) → (p1 ∧ ((p5 ∧ (p2 ∨ p3)) → p3)))) := by
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
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249193793269104918829894667172 : ((p4 ∨ p3) ∨ ((p1 ∨ (p5 ∨ (((p3 ∧ False) ∨ p4) ∧ False))) ∨ ((((p4 → p2) ∧ (p5 ∧ p2)) ∧ (p2 ∨ (p3 → p2))) → (p2 → True)))) := by
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
theorem thm_5_vars_66261272415897519665844644918 : ((p5 ∨ ((p1 → ((p3 ∨ p3) → p1)) → (((True → ((p3 ∧ (p3 ∨ p4)) ∧ p5)) ∧ p1) ∨ (p3 ∧ (p2 ∨ (p3 ∨ (p5 ∨ p5))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157886186338055304990203976311 : (((True ∧ ((p4 → p1) → (p2 ∨ ((p5 ∧ p5) ∨ p3)))) ∨ (((p4 ∨ p3) → (False ∨ p4)) ∨ p5)) ∨ (p3 → ((True → (True ∨ p5)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244538369277785401389430214316 : ((False ∧ p3) ∨ (p3 ∨ ((False ∨ p2) ∨ (p5 ∨ (((p1 ∧ (p3 ∧ True)) → (False ∧ p1)) ∨ (((True ∨ p4) ∧ (False → (p4 ∨ p1))) ∨ p2)))))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49728994429965303835191565448 : (((p1 ∧ (True → ((p5 ∨ (p3 ∨ p1)) ∨ ((((p2 ∨ False) → p1) ∨ p1) → (((False ∨ p2) → True) ∨ p5))))) → (False ∨ (p3 ∧ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_750425809178205624352365857870 : (((True ∧ ((((p4 ∨ (((p2 → p3) → (p1 ∨ ((True ∨ True) ∧ (p1 ∧ (p4 ∨ True))))) → p4)) ∨ p4) ∧ p3) ∨ ((p1 → p4) ∨ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37818773665070661824083236700 : ((((p5 ∧ (((((p4 ∨ (p2 → (p5 ∨ p2))) → True) ∨ p5) ∧ (p2 ∨ (p2 ∨ (True → True)))) ∧ (p1 ∧ (p2 → True)))) → False) ∧ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305928861365811016608394632144 : (p1 ∨ ((p4 ∨ (p3 → (p4 ∧ (False → False)))) → (((p4 → ((p1 ∧ (p5 ∧ p4)) ∨ (p4 ∨ p3))) ∨ (True ∧ ((p5 ∧ False) → p1))) ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Implications on the right can always be decomposed.
    intro h7
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- False on the left can always be used.
    apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328999212586776000759389951140 : (True → ((False ∧ (((p1 ∨ False) ∧ False) ∨ False)) ∨ (p1 → (p2 → (((True → ((p5 → (False → True)) ∨ ((p1 ∧ True) ∨ p3))) ∨ False) ∨ p4))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h4
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h5
  -- Implications on the right can always be decomposed.
  intro h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231521209460854513680263832884 : (((p4 → p1) ∨ p5) → ((p4 ∨ ((False ∨ True) ∧ ((p4 → p2) ∨ p1))) ∨ ((p4 → p4) ∨ (p1 ∨ ((p1 ∧ (p5 ∧ p3)) ∨ (p1 → p2)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_311771266178519823461034758424 : (p2 ∨ (False ∨ ((p1 ∧ ((p1 ∧ p5) ∨ p1)) ∨ ((p1 ∧ (p1 ∧ ((False ∨ (((p2 ∨ (p2 → p4)) → p1) ∧ True)) ∧ p5))) → (False ∨ p5))))) := by
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
  let h4 := h3.left
  let h5 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h8 =>
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116475150154772614336036035221 : (((p1 ∧ p1) ∧ (((p1 ∧ True) → False) → ((((p1 → ((True ∧ p5) → ((p5 ∨ (p2 → p5)) ∨ p2))) ∨ p2) ∧ p3) → False))) ∨ (p2 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178232167607127499593235018126 : (((p3 → (p3 ∧ ((p5 ∧ p5) ∧ ((p3 ∧ False) → (p2 ∧ p4))))) → p4) ∨ ((p4 ∧ ((((p4 ∧ p2) ∧ (p2 → False)) → p4) → False)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_201340026793584304471979111792 : ((p5 → ((p1 ∨ False) → ((p5 ∧ False) ∨ p1))) → ((((p2 → True) → ((p3 ∧ False) ∨ p1)) ∧ ((True ∨ p2) ∧ ((p1 ∧ p4) ∨ p3))) → p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- One of the premise coincides with the conclusion.
      exact h9
    case inr h11 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h12 : (p2 → True) := by
        -- Implications on the right can always be decomposed.
        intro h13
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h14 := h3 h12
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h15 =>
        -- Conjunctions on the left can always be decomposed.
        let h16 := h15.left
        let h17 := h15.right
        -- False on the left can always be used.
        apply False.elim h17
      case inr h18 =>
        -- One of the premise coincides with the conclusion.
        exact h18
  case inr h19 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h20 =>
      -- Conjunctions on the left can always be decomposed.
      let h21 := h20.left
      let h22 := h20.right
      -- One of the premise coincides with the conclusion.
      exact h21
    case inr h23 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h24 : (p2 → True) := by
        -- Implications on the right can always be decomposed.
        intro h25
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h26 := h3 h24
      -- Disjunctions on the left can always be decomposed.
      cases h26
      case inl h27 =>
        -- Conjunctions on the left can always be decomposed.
        let h28 := h27.left
        let h29 := h27.right
        -- False on the left can always be used.
        apply False.elim h29
      case inr h30 =>
        -- One of the premise coincides with the conclusion.
        exact h30



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58779475320319108431612693914 : (((p4 → p4) ∧ ((((p3 ∨ p4) → p2) ∧ p2) → ((((p5 → (p1 ∧ p2)) ∨ ((p1 ∨ p4) ∧ (p3 → False))) ∨ p2) ∨ (True ∨ p1)))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40601804265199335505205725747 : (((((((p4 ∧ (p2 → ((p1 ∨ ((False ∨ False) ∧ p5)) → (p4 → (p3 → True))))) ∧ ((p5 → p1) → p1)) ∨ p1) ∨ p5) → False) ∨ True) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_745725648286874255425076124326 : ((((True ∨ p5) → (((p3 → p1) ∧ p1) ∧ ((((p4 ∧ p1) ∧ p2) → (p3 ∧ (False ∨ (((p2 ∧ True) → p1) → (p3 ∨ p3))))) → False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136836439737383680728077804650 : (((p1 ∧ p4) ∨ ((p2 ∧ (((p4 → (p4 ∧ p2)) → p2) ∧ ((((p3 → False) → p1) ∨ False) ∨ p1))) ∨ (False ∧ p2))) ∨ (p2 → (p3 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319163442051623285291456315435 : (p4 ∨ ((((p3 → True) → ((p1 ∨ (p5 ∧ ((p4 ∧ p4) ∨ p5))) → ((True ∨ p5) ∨ p4))) → p3) ∨ (False → ((p2 ∨ (p1 ∨ p4)) ∨ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_626663620538674734919459357501 : ((((p4 → (p4 → ((p5 ∨ ((p3 → (p2 ∨ ((False ∨ (p1 ∧ ((p2 ∧ ((True ∨ p1) ∧ True)) ∧ True))) ∧ p5))) → True)) → p5))) ∨ True) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_58956511440928143598007338712 : (((p2 ∧ p1) ∨ ((False ∧ ((p5 ∨ (p2 ∨ p3)) ∨ ((p4 → (False → ((p5 → p4) ∧ ((True → p1) → (True ∧ True))))) → p3))) ∧ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115435806421653981556949329787 : ((((p5 ∧ (False ∨ ((p1 ∨ p3) → p4))) → p2) ∨ (p5 ∧ ((p2 → (((True → p3) ∧ p1) → (p1 → (False → p5)))) ∧ False))) ∨ (False → False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55185801403943544551233306148 : (((((p3 → p5) ∨ (p4 ∨ p2)) → p5) ∨ (((p2 → (p2 → (p2 → p1))) → ((p2 ∧ (p3 → (p2 ∨ (p1 ∧ p1)))) → False)) ∨ True)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48586584008374574237977293637 : ((((((p3 ∧ (p4 → ((p1 ∧ (p5 → (p3 ∨ p4))) ∨ (p3 → False)))) ∧ (p5 → p5)) → False) ∧ (False ∨ p3)) ∧ (p1 ∨ (False → True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_728195464087294450474461946348 : ((((True → (p1 ∧ p5)) ∨ (p1 ∨ (((((p1 → (p5 → False)) ∧ (True ∨ (False ∨ (False → (p3 ∨ p2))))) ∧ (True ∧ False)) → False) → False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190682474641368427739163294005 : (((p4 → (False ∧ ((p3 ∨ (p1 ∧ True)) → p2))) → p4) ∨ (((p5 ∨ p2) → (p2 ∨ (p5 ∧ ((p4 ∧ (False ∧ True)) ∧ (p2 ∧ False))))) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314469387707016510363032970652 : (p3 ∨ ((((((True ∨ p5) ∨ False) ∧ True) ∨ (False ∧ p2)) ∧ ((p5 ∧ (((False → p4) → p4) ∧ p3)) ∨ p4)) → (((p2 ∧ False) ∨ p2) ∨ p4))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Disjunctions on the left can always be decomposed.
        cases h3
        case inl h9 =>
          -- Conjunctions on the left can always be decomposed.
          let h10 := h9.left
          let h11 := h9.right
          -- Conjunctions on the left can always be decomposed.
          let h12 := h11.left
          let h13 := h11.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
          have h14 : (False → p4) := by
            -- Implications on the right can always be decomposed.
            intro h15
            -- False on the left can always be used.
            apply False.elim h15
          -- We have shown the premise of h12, we can now drive its conclusion.
          let h16 := h12 h14
          -- One of the premise coincides with the conclusion.
          exact h16
        case inr h17 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h17
      case inr h18 =>
        -- Disjunctions on the left can always be decomposed.
        cases h3
        case inl h19 =>
          -- Conjunctions on the left can always be decomposed.
          let h20 := h19.left
          let h21 := h19.right
          -- Conjunctions on the left can always be decomposed.
          let h22 := h21.left
          let h23 := h21.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- We want to use the implication h22 based on <expert-advice>. So we show its premise.
          have h24 : (False → p4) := by
            -- Implications on the right can always be decomposed.
            intro h25
            -- False on the left can always be used.
            apply False.elim h25
          -- We have shown the premise of h22, we can now drive its conclusion.
          let h26 := h22 h24
          -- One of the premise coincides with the conclusion.
          exact h26
        case inr h27 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h27
    case inr h28 =>
      -- False on the left can always be used.
      apply False.elim h28
  case inr h29 =>
    -- Conjunctions on the left can always be decomposed.
    let h30 := h29.left
    let h31 := h29.right
    -- False on the left can always be used.
    apply False.elim h30



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41900679402970138593572015683 : (((((True → False) ∧ True) → (p3 ∨ (((p5 → False) → (((False ∨ False) ∨ ((p2 → True) ∨ p4)) ∧ (p1 ∧ p5))) ∨ (p5 ∨ p4)))) ∨ False) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_652417124982328981358340136390 : ((((p5 ∧ (((True → True) → (((True ∨ p3) ∧ (((False ∧ (p4 ∧ p4)) ∧ True) → p1)) → ((p5 → True) → p1))) ∨ p1)) ∧ (p1 → p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_668167964218781822432099995196 : ((((p1 → ((p1 ∧ (((p1 → (((p1 → True) ∧ p2) ∨ p3)) ∨ ((p5 ∨ (p4 ∨ True)) ∨ False)) ∨ p4)) → p3)) ∧ ((True ∨ True) ∨ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148474352408038924013970154905 : (((True → (p3 ∨ ((True ∨ ((p3 ∧ p5) ∨ p1)) ∧ (False ∧ True)))) ∧ (p3 → ((True ∧ (p1 ∨ False)) ∨ p3))) ∨ (True ∨ ((False ∧ p5) ∧ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_685348546688960663163155316599 : ((((p4 → ((p1 ∧ (p4 ∧ ((True ∨ True) ∨ p3))) → (p3 ∨ ((True ∧ True) → (p5 ∧ p1))))) ∨ (False ∧ ((p5 ∧ p3) ∧ (p2 → p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227447621110362006373366178960 : (((p5 → p5) → p2) ∨ ((((p4 ∨ p1) ∨ p1) ∨ (p4 ∨ (False → ((False ∨ False) ∧ p1)))) ∨ (p5 → ((p4 ∨ p2) ∨ ((p3 ∧ False) → p1))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_320446875892416336462342632153 : (p4 ∨ ((p4 ∨ False) → (p2 → ((p2 ∧ ((p3 ∧ (((((p3 ∨ ((p3 → (p4 ∨ p3)) ∨ p1)) → p1) ∧ False) ∨ p5) ∧ p3)) ∨ p2)) ∧ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h4 =>
    -- False on the left can always be used.
    apply False.elim h4
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h6 =>
    -- False on the left can always be used.
    apply False.elim h6
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h7 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h8 =>
    -- False on the left can always be used.
    apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113497522656381716205154444305 : ((((p2 ∧ ((p5 ∨ p1) ∧ (((p4 ∧ (True ∨ (p5 ∧ (True ∨ p1)))) ∨ p2) ∧ p3))) ∨ (p1 ∨ (p3 ∧ p3))) ∨ (True ∨ True)) ∨ (False → p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_620748836052084297892204512796 : (((((p4 ∧ True) → ((p2 ∨ (((p1 ∨ ((False ∨ False) ∧ p5)) ∨ False) ∧ (p1 → ((p3 ∧ (True → (True ∧ True))) ∨ False)))) → False)) ∨ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_609400082824550804941851444713 : ((((((True ∨ p2) → (p2 → (((False ∧ p2) ∧ ((True ∨ ((p1 ∨ ((p1 → False) → (p4 ∧ p1))) ∧ p4)) ∧ False)) ∨ p3))) ∨ p5) ∨ True) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_200975967007445322820524563203 : ((p2 ∨ (p5 ∨ (p3 ∧ (p1 → (False ∨ p5))))) → ((False ∧ False) ∨ (True ∧ (p1 → (True → (p3 ∨ ((((False ∨ p2) ∧ p5) ∧ p4) ∨ p1))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- Implications on the right can always be decomposed.
      intro h7
      -- Implications on the right can always be decomposed.
      intro h8
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- Implications on the right can always be decomposed.
      intro h12
      -- Implications on the right can always be decomposed.
      intro h13
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_424488636464473974930888660148 : (((((p2 ∧ (p5 → ((False ∧ True) ∧ p5))) → (((((p3 → (p5 → p3)) → p3) → (p4 ∧ p3)) ∧ p1) ∨ (p1 ∨ p2))) ∧ (True ∨ p4)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



