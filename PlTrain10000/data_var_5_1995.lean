variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337111990152738083809762952991 : (p1 → (((p1 → p5) ∧ (p5 ∨ (p2 ∧ ((((True ∧ p5) ∨ (p2 → p3)) → p2) ∧ (((p3 ∧ (p4 ∨ p4)) → False) ∨ False))))) ∨ (False → p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149585493771617028243109284089 : ((p3 ∧ ((((p5 ∧ p3) ∨ True) → ((p4 ∧ (((p2 ∧ (False → (p4 → False))) → p3) ∧ p4)) → p2)) ∨ p5)) ∨ (False → (p2 ∨ (p5 ∨ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263552070486241701272872681029 : (True ∧ ((((((p2 → (True → p1)) ∨ ((p1 ∧ p4) ∧ (True → (True ∧ p2)))) ∨ p4) ∧ (p3 ∧ p1)) ∨ p1) ∨ ((p1 ∨ False) → (p3 ∨ True)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- False on the left can always be used.
    apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51029962751434684365328569554 : (((p4 ∧ (p5 ∨ (((p4 ∨ (p5 → p2)) ∨ False) ∧ (((p3 → p4) → (True ∨ p4)) ∧ p4)))) ∧ (((p1 ∨ True) → False) → (p1 ∧ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_602750296221165482119323741336 : ((((False ∨ (p4 ∧ ((False ∧ (((p3 ∧ (((((p4 → p1) ∨ p4) ∧ p1) ∨ True) → p2)) ∧ (p4 → p1)) ∧ (p3 → p1))) ∧ p1))) ∧ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192633618884301071359430160496 : (((((((p4 ∧ False) ∧ p5) ∧ p5) → p2) ∨ p4) → p5) → (((((p1 ∧ p5) ∧ (p1 → True)) → (p5 ∨ p1)) → ((p5 → p1) ∨ p5)) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : (((((p4 ∧ False) ∧ p5) ∧ p5) → p2) ∨ p4) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h9 := h7.left
    let h10 := h7.right
    -- False on the left can always be used.
    apply False.elim h10
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h11 := h1 h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133915257784558948912637310300 : (((p3 ∨ (p1 ∧ (p2 ∨ (p3 → ((((False ∧ True) ∨ (False ∧ (False ∧ (p1 → True)))) ∨ (p1 ∧ p3)) ∨ p1))))) ∧ False) ∨ ((p5 ∨ p3) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232126977379132926248135676100 : (((p5 ∨ p4) → p3) → ((True → (p4 ∨ p5)) ∨ ((p2 → (p4 ∨ (((True → p5) ∨ p5) ∨ True))) ∨ ((p1 → (p5 → p5)) → (False → p2))))) := by
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
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58974088598207504035779806257 : (((p2 ∧ p4) ∨ (((False → (p2 → ((p4 ∨ (True ∨ (True ∨ p1))) ∨ (p3 ∨ ((p1 → True) ∧ (p5 ∨ (p1 → p4))))))) ∧ p2) → p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356585379622704249827697570368 : (p5 → (((((p3 ∧ False) ∧ (p4 → True)) ∧ p1) → p2) ∧ ((((p2 ∨ (p1 ∨ True)) ∧ ((p2 ∨ False) → (False ∧ False))) → (p3 ∨ p1)) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- False on the left can always be used.
  apply False.elim h8
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231057544683779091896949062207 : (((True ∨ p3) ∨ p2) → ((p1 ∨ (p4 ∧ (p3 ∧ ((False → (((p4 ∨ False) → True) ∨ ((p1 ∨ True) → p3))) ∨ (True ∨ p3))))) ∨ (p5 ∨ True))) := by
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
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193696539335858783413604917042 : ((p1 ∧ (p1 ∧ (p5 ∧ ((p2 ∨ p4) → (True ∨ p4))))) → ((p2 ∨ p3) ∨ (((p5 → True) → (False ∨ ((p3 ∨ p4) ∧ (True → p4)))) ∨ p1))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322500375964734657410899563644 : (p5 ∨ (((False → p1) → ((((((p1 ∨ (False ∧ ((False ∧ p5) ∨ p1))) ∧ (p2 ∧ True)) → (p5 → p5)) → p5) ∧ (False ∨ p1)) ∧ p5)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66292646663738958658676415641 : ((p5 ∨ ((p1 ∧ p2) ∨ ((((p2 ∧ True) → (((False ∧ p5) ∨ False) ∨ (((p2 ∧ True) → p1) ∨ (p3 ∨ p2)))) ∨ (p2 → p4)) ∧ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_90922822439621303362261780448 : (((True → False) ∧ (True ∨ ((((p3 ∨ p5) → (True ∨ (p5 ∧ (p2 ∨ p1)))) ∧ False) ∨ ((((False → False) → (p4 → p2)) → p5) ∨ True)))) → p5) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h5 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h6 := h2 h5
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- False on the left can always be used.
      apply False.elim h10
    case inr h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h13 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h14 := h2 h13
        -- False on the left can always be used.
        apply False.elim h14
      case inr h15 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h16 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h17 := h2 h16
        -- False on the left can always be used.
        apply False.elim h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213158003651468125857772860495 : ((((p2 ∧ p3) ∨ False) ∧ False) ∨ (p3 → (((((p2 ∨ p3) → p3) ∨ ((p1 → (((False ∧ False) ∧ p2) ∨ p3)) → True)) → False) → (p5 → p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (((p2 ∨ p3) → p3) ∨ ((p1 → (((False ∧ False) ∧ p2) ∨ p3)) → True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h4
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161655016560666176164731560502 : ((p1 ∨ ((p3 ∧ ((False ∨ True) ∨ (p3 → (False → p5)))) ∧ ((p1 ∧ (p1 → True)) ∨ (p3 ∧ p3)))) → ((((p2 → True) → p2) ∧ p2) ∨ True)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- False on the left can always be used.
        apply False.elim h9
      case inr h10 =>
        -- Disjunctions on the left can always be decomposed.
        cases h5
        case inl h11 =>
          -- Conjunctions on the left can always be decomposed.
          let h12 := h11.left
          let h13 := h11.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h14 =>
          -- Conjunctions on the left can always be decomposed.
          let h15 := h14.left
          let h16 := h14.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
    case inr h17 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h18 =>
        -- Conjunctions on the left can always be decomposed.
        let h19 := h18.left
        let h20 := h18.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h21 =>
        -- Conjunctions on the left can always be decomposed.
        let h22 := h21.left
        let h23 := h21.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_123753310410210672514163840498 : (((p1 ∨ (p1 ∧ (True → (((p4 ∧ (p5 ∧ p4)) ∨ (p2 → p1)) ∧ p4)))) ∧ (((p5 → (p2 ∧ p2)) → p1) ∨ (False → p3))) → (p3 ∨ p1)) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62513950234367596453750418801 : ((p3 ∧ (p3 ∧ ((p1 → p1) → ((False ∧ ((p2 → (((p1 → (True ∨ True)) ∧ False) ∧ (p1 ∨ ((p2 → p3) → p5)))) → False)) ∨ True)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_683322152512625008219153013487 : ((((p3 ∨ (p5 ∧ (((((False → p5) → (True ∨ p4)) → p2) ∧ (False ∨ p5)) ∧ (p1 ∧ False)))) ∧ ((((p1 ∧ False) ∧ p5) ∨ p2) ∨ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257823951962051219580790997165 : ((p3 ∨ p5) → ((False → (p5 ∨ False)) → (((((p5 ∧ ((False ∧ (p5 ∨ p4)) ∧ (p1 → (p2 ∨ p1)))) ∧ p4) ∧ False) ∨ (False → p5)) ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351233482757211463587886470232 : (p4 → (((((p5 ∨ (p4 → False)) ∨ (p3 → p5)) → (((p3 → True) ∨ True) → p5)) ∨ (((True ∨ p3) → p4) ∨ p4)) ∨ ((True → True) → False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149385487138116717425395306906 : (((p4 → p3) → ((p2 ∨ True) ∧ ((p5 ∨ p5) → ((p1 ∧ ((p3 ∧ p5) → True)) → (p5 ∧ (p5 → p2)))))) ∨ (p1 ∨ ((False → p4) ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65461203334664220566503122053 : ((p3 ∨ ((p2 → False) → (((((p4 ∨ ((p3 ∨ p1) ∧ p1)) ∨ p3) ∨ (True ∨ (True ∨ p2))) ∨ p4) ∧ (False ∨ ((False ∨ True) → p4))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_89354104735013764518122057508 : (((p5 ∨ (p4 ∨ p2)) ∧ (((False → p3) ∧ (((True → False) ∧ (p1 ∧ (p3 ∧ (True ∨ p2)))) → ((p3 ∧ (True → False)) ∧ p2))) → False)) → False) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h5 : ((False → p3) ∧ (((True → False) ∧ (p1 ∧ (p3 ∧ (True ∨ p2)))) → ((p3 ∧ (True → False)) ∧ p2))) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h6
      -- False on the left can always be used.
      apply False.elim h6
      -- Implications on the right can always be decomposed.
      intro h7
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h14 =>
        -- One of the premise coincides with the conclusion.
        exact h12
      case inr h15 =>
        -- One of the premise coincides with the conclusion.
        exact h12
      -- Implications on the right can always be decomposed.
      intro h16
      -- Conjunctions on the left can always be decomposed.
      let h17 := h7.left
      let h18 := h7.right
      -- Conjunctions on the left can always be decomposed.
      let h19 := h18.left
      let h20 := h18.right
      -- Conjunctions on the left can always be decomposed.
      let h21 := h20.left
      let h22 := h20.right
      -- Disjunctions on the left can always be decomposed.
      cases h22
      case inl h23 =>
        -- We want to use the implication h17 based on <expert-advice>. So we show its premise.
        have h24 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h17, we can now drive its conclusion.
        let h25 := h17 h24
        -- False on the left can always be used.
        apply False.elim h25
      case inr h26 =>
        -- We want to use the implication h17 based on <expert-advice>. So we show its premise.
        have h27 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h17, we can now drive its conclusion.
        let h28 := h17 h27
        -- False on the left can always be used.
        apply False.elim h28
      -- Conjunctions on the left can always be decomposed.
      let h29 := h7.left
      let h30 := h7.right
      -- Conjunctions on the left can always be decomposed.
      let h31 := h30.left
      let h32 := h30.right
      -- Conjunctions on the left can always be decomposed.
      let h33 := h32.left
      let h34 := h32.right
      -- Disjunctions on the left can always be decomposed.
      cases h34
      case inl h35 =>
        -- We want to use the implication h29 based on <expert-advice>. So we show its premise.
        have h36 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h29, we can now drive its conclusion.
        let h37 := h29 h36
        -- False on the left can always be used.
        apply False.elim h37
      case inr h38 =>
        -- One of the premise coincides with the conclusion.
        exact h38
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h39 := h3 h5
    -- False on the left can always be used.
    apply False.elim h39
  case inr h40 =>
    -- Disjunctions on the left can always be decomposed.
    cases h40
    case inl h41 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h42 : ((False → p3) ∧ (((True → False) ∧ (p1 ∧ (p3 ∧ (True ∨ p2)))) → ((p3 ∧ (True → False)) ∧ p2))) := by
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Implications on the right can always be decomposed.
        intro h43
        -- False on the left can always be used.
        apply False.elim h43
        -- Implications on the right can always be decomposed.
        intro h44
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Conjunctions on the left can always be decomposed.
        let h45 := h44.left
        let h46 := h44.right
        -- Conjunctions on the left can always be decomposed.
        let h47 := h46.left
        let h48 := h46.right
        -- Conjunctions on the left can always be decomposed.
        let h49 := h48.left
        let h50 := h48.right
        -- Disjunctions on the left can always be decomposed.
        cases h50
        case inl h51 =>
          -- One of the premise coincides with the conclusion.
          exact h49
        case inr h52 =>
          -- One of the premise coincides with the conclusion.
          exact h49
        -- Implications on the right can always be decomposed.
        intro h53
        -- Conjunctions on the left can always be decomposed.
        let h54 := h44.left
        let h55 := h44.right
        -- Conjunctions on the left can always be decomposed.
        let h56 := h55.left
        let h57 := h55.right
        -- Conjunctions on the left can always be decomposed.
        let h58 := h57.left
        let h59 := h57.right
        -- Disjunctions on the left can always be decomposed.
        cases h59
        case inl h60 =>
          -- We want to use the implication h54 based on <expert-advice>. So we show its premise.
          have h61 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h54, we can now drive its conclusion.
          let h62 := h54 h61
          -- False on the left can always be used.
          apply False.elim h62
        case inr h63 =>
          -- We want to use the implication h54 based on <expert-advice>. So we show its premise.
          have h64 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h54, we can now drive its conclusion.
          let h65 := h54 h64
          -- False on the left can always be used.
          apply False.elim h65
        -- Conjunctions on the left can always be decomposed.
        let h66 := h44.left
        let h67 := h44.right
        -- Conjunctions on the left can always be decomposed.
        let h68 := h67.left
        let h69 := h67.right
        -- Conjunctions on the left can always be decomposed.
        let h70 := h69.left
        let h71 := h69.right
        -- Disjunctions on the left can always be decomposed.
        cases h71
        case inl h72 =>
          -- We want to use the implication h66 based on <expert-advice>. So we show its premise.
          have h73 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h66, we can now drive its conclusion.
          let h74 := h66 h73
          -- False on the left can always be used.
          apply False.elim h74
        case inr h75 =>
          -- One of the premise coincides with the conclusion.
          exact h75
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h76 := h3 h42
      -- False on the left can always be used.
      apply False.elim h76
    case inr h77 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h78 : ((False → p3) ∧ (((True → False) ∧ (p1 ∧ (p3 ∧ (True ∨ p2)))) → ((p3 ∧ (True → False)) ∧ p2))) := by
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Implications on the right can always be decomposed.
        intro h79
        -- False on the left can always be used.
        apply False.elim h79
        -- Implications on the right can always be decomposed.
        intro h80
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Conjunctions on the left can always be decomposed.
        let h81 := h80.left
        let h82 := h80.right
        -- Conjunctions on the left can always be decomposed.
        let h83 := h82.left
        let h84 := h82.right
        -- Conjunctions on the left can always be decomposed.
        let h85 := h84.left
        let h86 := h84.right
        -- Disjunctions on the left can always be decomposed.
        cases h86
        case inl h87 =>
          -- One of the premise coincides with the conclusion.
          exact h85
        case inr h88 =>
          -- One of the premise coincides with the conclusion.
          exact h85
        -- Implications on the right can always be decomposed.
        intro h89
        -- Conjunctions on the left can always be decomposed.
        let h90 := h80.left
        let h91 := h80.right
        -- Conjunctions on the left can always be decomposed.
        let h92 := h91.left
        let h93 := h91.right
        -- Conjunctions on the left can always be decomposed.
        let h94 := h93.left
        let h95 := h93.right
        -- Disjunctions on the left can always be decomposed.
        cases h95
        case inl h96 =>
          -- We want to use the implication h90 based on <expert-advice>. So we show its premise.
          have h97 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h90, we can now drive its conclusion.
          let h98 := h90 h97
          -- False on the left can always be used.
          apply False.elim h98
        case inr h99 =>
          -- We want to use the implication h90 based on <expert-advice>. So we show its premise.
          have h100 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h90, we can now drive its conclusion.
          let h101 := h90 h100
          -- False on the left can always be used.
          apply False.elim h101
        -- Conjunctions on the left can always be decomposed.
        let h102 := h80.left
        let h103 := h80.right
        -- Conjunctions on the left can always be decomposed.
        let h104 := h103.left
        let h105 := h103.right
        -- Conjunctions on the left can always be decomposed.
        let h106 := h105.left
        let h107 := h105.right
        -- Disjunctions on the left can always be decomposed.
        cases h107
        case inl h108 =>
          -- One of the premise coincides with the conclusion.
          exact h77
        case inr h109 =>
          -- One of the premise coincides with the conclusion.
          exact h109
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h110 := h3 h78
      -- False on the left can always be used.
      apply False.elim h110



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116092882810897046638162414373 : ((((True → True) ∨ False) ∧ ((p5 ∧ (p3 ∧ ((p5 → ((p5 ∨ (p1 ∨ False)) ∧ (((p5 ∨ True) ∧ p2) ∧ False))) ∨ False))) → p1)) ∨ (False ∧ p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h7 =>
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h8 : p5 := by
      -- One of the premise coincides with the conclusion.
      exact h3
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h9 := h7 h8
    -- We need to get the right conjuct of h9 based on <expert-advice>.
    let h10 := h9.right
    -- We need to get the right conjuct of h10 based on <expert-advice>.
    let h11 := h10.right
    -- False on the left can always be used.
    apply False.elim h11
  case inr h12 =>
    -- False on the left can always be used.
    apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61341075966237136390103374795 : ((p1 ∧ (((p2 → (p3 → (False → (p3 → (True → (((False ∨ (True ∨ (p1 → (p2 → p1)))) → False) ∧ (False → p1))))))) → p1) ∧ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52234034018177837310269158654 : (((p2 ∧ ((True ∨ p4) ∧ (p3 → (True ∨ (p3 → (False ∧ ((False ∨ p1) ∨ p3))))))) → (((p2 ∧ (p4 ∧ p4)) → (True → True)) ∧ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157379781445277960078452540500 : ((((((p3 ∨ (p3 ∧ p2)) ∨ (True ∨ p1)) ∧ (((False → False) ∧ p2) → True)) ∧ p3) ∧ (p3 ∨ p4)) ∨ (p1 ∨ (True → ((p5 ∧ p1) ∨ True)))) := by
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
theorem thm_5_vars_40939908936988404020354856220 : (((((p5 → ((((p4 ∨ p2) → (p2 ∧ (p1 ∧ p4))) ∨ False) → ((p3 ∧ ((True ∨ p5) ∧ p4)) ∧ p5))) ∨ p2) ∨ (True ∨ p2)) ∨ p1) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_663476113165236967376040406391 : (((((False → p4) → ((((p3 ∨ (True ∧ p4)) → p1) ∨ (((False → (True ∧ (p4 ∨ False))) ∨ p3) → p3)) ∧ (False → p1))) → (p3 ∨ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58022434993722611012111108192 : (((True ∧ p2) ∧ (p2 → ((True → True) ∧ (p4 ∨ ((((True ∧ p3) → False) → (p3 ∨ p4)) → (((p4 ∧ (False → False)) ∧ p4) → False)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148959216246475482578692727992 : ((((p2 ∧ False) ∨ p2) ∧ (((False ∧ p1) ∨ (p2 → p5)) ∨ (p2 ∨ ((p4 → p4) ∨ (True ∨ (p4 ∧ p4)))))) ∨ ((p4 ∧ False) → (p1 → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117017876845623325527467094639 : (((p1 ∨ p3) → ((p3 ∧ (((p4 ∨ p4) ∨ ((True ∧ False) ∨ ((p1 → ((p5 → False) ∧ p3)) ∧ False))) ∧ False)) ∨ (p4 ∨ p4))) ∨ (p3 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46428720507777667702700625078 : ((((p1 ∧ ((p1 ∧ (p5 → p5)) → p1)) ∨ ((p4 ∧ False) ∨ ((p2 ∧ (p1 ∧ p4)) → ((True ∧ p5) → (p3 → True))))) ∧ (False ∧ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_682758076304016308243417880929 : (((((((False ∨ p4) ∨ False) → p4) → (((p2 → (p4 → p4)) → (p1 ∨ (p4 ∧ True))) ∨ True)) ∧ (p4 → (p1 → ((p4 → False) → p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64442052536269901388553490763 : ((p1 ∨ (((p5 ∨ (True → p3)) → (((p3 ∨ p2) ∨ p2) → (p3 → (p5 ∧ (p3 ∧ (p3 ∧ (True ∨ (p2 ∧ p4)))))))) ∨ (p3 ∧ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47783728403165313318327491602 : (((((((p1 ∨ ((p4 ∧ (p5 → (p4 ∧ (True ∧ p4)))) → False)) ∨ p5) ∧ (p5 → ((p2 → p2) ∧ True))) ∧ True) → p3) → (p4 ∧ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_627196821246166436027923621034 : (((((((((((True ∧ p4) → (p5 → p2)) ∧ ((True → (p3 ∧ True)) ∨ p2)) ∧ p1) ∨ False) → ((p5 ∧ False) → p5)) ∨ True) ∧ p2) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_790676271098481127005729760313 : (((p5 ∨ (p5 ∨ ((p2 → (p3 → ((((p2 ∨ (p5 → p3)) ∨ p1) ∨ (False → p5)) → (False ∨ ((p5 ∨ p2) → (p4 → p2)))))) ∨ p1))) ∨ False) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
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
        -- Implications on the right can always be decomposed.
        intro h7
        -- Implications on the right can always be decomposed.
        intro h8
        -- Disjunctions on the left can always be decomposed.
        cases h7
        case inl h9 =>
          -- One of the premise coincides with the conclusion.
          exact h1
        case inr h10 =>
          -- One of the premise coincides with the conclusion.
          exact h10
      case inr h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h12
        -- Implications on the right can always be decomposed.
        intro h13
        -- Disjunctions on the left can always be decomposed.
        cases h12
        case inl h14 =>
          -- One of the premise coincides with the conclusion.
          exact h1
        case inr h15 =>
          -- One of the premise coincides with the conclusion.
          exact h15
    case inr h16 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h17
      -- Implications on the right can always be decomposed.
      intro h18
      -- Disjunctions on the left can always be decomposed.
      cases h17
      case inl h19 =>
        -- One of the premise coincides with the conclusion.
        exact h1
      case inr h20 =>
        -- One of the premise coincides with the conclusion.
        exact h20
  case inr h21 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h22
    -- Implications on the right can always be decomposed.
    intro h23
    -- Disjunctions on the left can always be decomposed.
    cases h22
    case inl h24 =>
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h25 =>
      -- One of the premise coincides with the conclusion.
      exact h25
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_530195596664709936976151146 : ((((((((p4 ∨ False) → (p2 ∨ p3)) ∨ (p1 ∧ (True ∨ p3))) ∨ ((((p4 → p5) ∧ p3) ∧ p5) → p4)) ∨ True) ∨ p2) ∨ p4) ∨ p2) := by
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
theorem thm_5_vars_678335486874309276572817266520 : ((((((True ∧ p1) ∧ (False ∧ (p1 ∧ p1))) ∧ ((p5 → True) ∨ (p2 ∧ (p2 → ((False ∨ True) ∧ False))))) ∨ (p4 → ((p3 ∨ p1) ∨ True))) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64576027079737454873140461471 : ((p1 ∨ (((p4 ∧ p1) → False) → ((((p3 ∨ p2) ∨ p4) ∨ ((p2 → p4) ∧ (True ∨ (p1 ∧ p1)))) ∨ ((p3 ∧ p5) → (True ∨ p3))))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_254629506700346170346082308526 : ((p3 ∧ p2) → (((((p1 ∨ p1) ∧ ((p1 ∨ ((p1 → p1) ∧ p1)) ∨ (p1 ∧ p2))) → False) ∨ ((p2 → (p5 ∨ (p1 → p1))) ∨ p3)) ∧ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_632727712002405798256583280462 : (((((p5 → (p1 ∨ ((((True ∨ p3) ∨ True) → (p1 ∧ (True → True))) → (p2 ∨ ((p3 ∧ p1) → ((True ∧ p5) ∨ p1)))))) → p2) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_3278750480435789085578516828 : ((p3 → p4) ∨ (((p4 → (p4 ∨ True)) → (p2 → (p5 ∨ p1))) ∨ ((((False ∨ p4) ∨ (p5 ∧ p3)) ∧ ((p3 ∨ p3) ∧ p1)) → p1))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- False on the left can always be used.
      apply False.elim h5
    case inr h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h3.left
      let h8 := h3.right
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h9 =>
        -- One of the premise coincides with the conclusion.
        exact h8
      case inr h10 =>
        -- One of the premise coincides with the conclusion.
        exact h8
  case inr h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- Conjunctions on the left can always be decomposed.
    let h14 := h3.left
    let h15 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h14
    case inl h16 =>
      -- One of the premise coincides with the conclusion.
      exact h15
    case inr h17 =>
      -- One of the premise coincides with the conclusion.
      exact h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135380359630011912044043254449 : ((((((((p4 → p4) ∨ ((p1 → p3) → ((p5 → True) ∧ False))) ∧ p5) ∨ p4) ∧ p5) → p1) ∨ ((p4 ∨ p4) → p4)) ∨ ((p2 ∧ p1) ∨ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_381429222125734303866831269980 : (((((p2 → ((p3 ∨ p5) ∨ (((((p3 ∧ p4) ∨ ((True ∨ (p5 ∧ p1)) ∨ True)) ∨ p5) ∨ (p2 ∨ (p4 ∧ True))) ∧ p3))) ∧ True) ∨ True) ∧ True) ∧ True) := by
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
theorem thm_5_vars_324093830119439388382445583490 : (p5 ∨ ((p4 ∨ (True ∧ (((p2 ∨ (p5 ∧ p4)) ∨ p5) ∧ (p2 → p2)))) ∨ (((False ∧ p2) ∨ (False ∨ (p4 ∧ ((p4 ∧ False) ∨ p5)))) → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    apply False.elim h3
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- False on the left can always be used.
      apply False.elim h6
    case inr h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Conjunctions on the left can always be decomposed.
        let h11 := h10.left
        let h12 := h10.right
        -- False on the left can always be used.
        apply False.elim h12
      case inr h13 =>
        -- One of the premise coincides with the conclusion.
        exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_210225099891712688712762935511 : ((((p2 ∧ False) → p4) ∨ p4) ∧ ((True → False) → ((p1 ∧ False) ∨ (p1 ∨ ((False ∧ ((p2 ∨ p1) ∧ p3)) ∧ (p4 ∧ ((True → p5) ∧ p2))))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h5 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h6 := h4 h5
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64914785256228159415357098240 : ((p2 ∨ ((((((p1 → p2) ∧ p1) → False) ∧ (p4 ∨ (p3 ∧ ((p2 ∧ p5) ∨ p2)))) ∨ p1) ∧ (p3 ∨ (p4 → ((p4 → True) → False))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166540691004038264629490447380 : ((p5 ∨ ((((True → p2) ∨ p5) → (((p4 ∧ False) ∨ p2) ∨ (False → (p3 → p5)))) ∨ p5)) ∨ (p1 ∨ (p2 → ((p2 → (False ∧ p3)) ∨ False)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- False on the left can always be used.
    apply False.elim h3
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- Implications on the right can always be decomposed.
    intro h7
    -- False on the left can always be used.
    apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_682050911992054976127963035760 : (((((p2 ∨ ((p3 ∧ p2) ∨ (True ∧ (((False ∨ (p2 ∧ (True ∨ p2))) → False) ∨ p4)))) ∨ p2) ∧ ((((p4 ∨ p2) → p1) ∧ p3) → p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_719455859993285413249081657792 : ((((p1 ∨ (p1 ∧ (p2 ∨ p4))) ∨ ((p3 ∨ (False → ((True ∧ p1) ∨ p2))) ∧ (p3 ∧ ((((True ∧ (p2 ∧ True)) → p2) ∧ p3) ∧ p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40341318080311480052471224748 : ((((((p4 → p1) → ((p3 ∧ ((((p3 ∨ p3) → p2) → ((p1 ∧ ((p2 → p3) ∨ p4)) ∨ p1)) ∧ p5)) ∧ False)) ∨ p4) ∨ True) ∨ p5) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_801260777054737337776774857157 : (((p2 → (((p3 ∨ p3) ∨ (False ∧ ((False ∨ (p4 ∧ (p5 → (p5 ∨ False)))) → (p4 ∨ False)))) → (p2 → (p4 ∨ (False ∨ (False ∨ p3)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135853521032532781210853448751 : (((((p1 ∧ (p5 ∧ p3)) ∧ (p1 ∧ ((False ∧ True) ∧ False))) ∧ p1) ∨ ((((True ∨ p2) ∨ (False ∧ p1)) ∧ p2) → True)) ∨ ((p4 → p4) → p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118243705116121913315038337217 : ((p1 ∨ (((True → ((False ∨ (p2 → (p4 ∨ p5))) ∨ (p5 ∧ p5))) ∧ (p5 ∧ (p5 → ((p5 ∧ p4) ∨ p3)))) ∨ (False → p2))) ∨ (False ∧ False)) := by
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
theorem thm_5_vars_157008283660228656819080634969 : (((((p5 ∨ True) ∧ p4) ∨ (p2 ∧ (p2 ∧ (((p2 ∧ p5) ∨ (False ∧ (p2 → False))) → False)))) ∨ p3) ∨ ((p2 ∨ (p1 → (p1 → False))) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323780405759999925065157201446 : (p5 ∨ ((((((p3 ∨ (p4 ∨ (p4 ∨ p5))) → (((False ∨ False) ∨ False) ∨ p1)) ∨ p2) ∧ p2) ∨ p3) ∨ ((p5 ∧ (True → False)) → (p4 → p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h5 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h6 := h4 h5
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_378670691385708518357352766807 : ((((p2 → ((False ∨ p5) ∨ (((p4 ∧ (p5 ∨ ((p2 ∧ (True ∧ True)) → (True → (p5 ∧ False))))) ∨ (p5 ∧ (True → p3))) ∨ p2))) ∧ True) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_254698143265410190452702600953 : ((p3 ∧ p3) → ((p2 ∨ ((p2 → (False ∨ ((((True ∧ p5) ∧ p1) → False) → (p4 ∨ ((((p4 ∨ True) ∨ p5) ∨ p4) → p4))))) ∧ p4)) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_320454656611521802008804213855 : (p4 ∨ ((p5 ∨ p3) → ((True ∧ (p3 ∨ p2)) → ((((True ∨ ((True → p5) ∨ (p5 → p4))) → False) ∨ False) → ((False ∨ (True ∨ p1)) → p1))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h8 =>
        -- Conjunctions on the left can always be decomposed.
        let h9 := h2.left
        let h10 := h2.right
        -- Disjunctions on the left can always be decomposed.
        cases h10
        case inl h11 =>
          -- Disjunctions on the left can always be decomposed.
          cases h1
          case inl h12 =>
            -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
            have h13 : (True ∨ ((True → p5) ∨ (p5 → p4))) := by
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h8, we can now drive its conclusion.
            let h14 := h8 h13
            -- False on the left can always be used.
            apply False.elim h14
          case inr h15 =>
            -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
            have h16 : (True ∨ ((True → p5) ∨ (p5 → p4))) := by
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h8, we can now drive its conclusion.
            let h17 := h8 h16
            -- False on the left can always be used.
            apply False.elim h17
        case inr h18 =>
          -- Disjunctions on the left can always be decomposed.
          cases h1
          case inl h19 =>
            -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
            have h20 : (True ∨ ((True → p5) ∨ (p5 → p4))) := by
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h8, we can now drive its conclusion.
            let h21 := h8 h20
            -- False on the left can always be used.
            apply False.elim h21
          case inr h22 =>
            -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
            have h23 : (True ∨ ((True → p5) ∨ (p5 → p4))) := by
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h8, we can now drive its conclusion.
            let h24 := h8 h23
            -- False on the left can always be used.
            apply False.elim h24
      case inr h25 =>
        -- False on the left can always be used.
        apply False.elim h25
    case inr h26 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h27 =>
        -- Conjunctions on the left can always be decomposed.
        let h28 := h2.left
        let h29 := h2.right
        -- Disjunctions on the left can always be decomposed.
        cases h29
        case inl h30 =>
          -- Disjunctions on the left can always be decomposed.
          cases h1
          case inl h31 =>
            -- One of the premise coincides with the conclusion.
            exact h26
          case inr h32 =>
            -- One of the premise coincides with the conclusion.
            exact h26
        case inr h33 =>
          -- Disjunctions on the left can always be decomposed.
          cases h1
          case inl h34 =>
            -- One of the premise coincides with the conclusion.
            exact h26
          case inr h35 =>
            -- One of the premise coincides with the conclusion.
            exact h26
      case inr h36 =>
        -- False on the left can always be used.
        apply False.elim h36



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51271221791663152243139596463 : (((True ∧ (((p4 ∨ ((False ∧ p1) ∨ (p2 ∧ p2))) → (False ∨ ((p1 ∧ p2) ∨ p5))) → False)) ∨ ((True ∧ (p5 ∧ p5)) ∨ (True ∧ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_679987633631564431448793586194 : (((((((p5 → (p2 → p4)) → p5) ∧ ((((p1 ∧ (p3 ∧ False)) → p1) ∧ (p2 ∨ p1)) → False)) → p5) → ((p5 ∨ p5) ∨ (True ∧ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204442541220142843892446792814 : (((((p4 → False) ∨ p5) ∧ True) ∨ p3) ∨ (True → ((p2 → (((p4 → (False ∧ (True → (p5 ∧ p2)))) ∨ True) ∨ ((True → p1) → p3))) ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157109427920674698397757231452 : (((p4 → (((p2 ∨ p3) ∧ (p1 → p4)) ∧ ((((p5 ∧ p5) ∧ (p4 ∧ False)) ∧ p2) ∧ p1))) ∨ False) ∨ ((p2 → (p3 ∧ (False ∧ p4))) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_798899315781223314756610758890 : (((p1 → ((p4 ∨ p2) ∧ (p5 ∨ ((p4 ∨ (((p2 ∨ False) ∧ ((True ∨ (p4 → (p3 → p4))) ∧ p4)) → (True → (p5 → p1)))) → p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206537060558299711883367394992 : ((True → (((p1 → p4) → p1) → False)) ∨ (((p5 → False) → ((True ∧ p4) ∨ (True ∧ (p1 ∧ p5)))) ∨ ((p5 ∧ (p5 ∧ p4)) → (p5 → True)))) := by
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
theorem thm_5_vars_56680119943935126054939769561 : ((((p3 → p3) ∧ p4) ∧ (((((False ∧ ((p2 ∨ (False → (p1 → p2))) → False)) ∨ p3) ∨ p3) ∧ (True → (p4 ∧ (p3 ∨ True)))) ∨ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_689952984608595061110288773353 : ((((False ∧ ((((((p4 ∧ True) ∨ (p4 ∧ False)) ∧ p1) ∨ (False ∨ p2)) ∧ p4) ∧ p5)) ∨ (((p4 ∨ p3) ∨ ((True ∧ p3) → p3)) ∨ p2)) ∨ False) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310402513621281859200307152142 : (p2 ∨ ((False ∧ (p5 ∧ (((p2 ∧ True) ∨ p1) ∧ p3))) ∨ (((True ∨ True) → (((p5 ∨ p1) ∧ (p5 ∧ p5)) → (p5 → (p1 ∨ True)))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_791348003596927765466837515618 : (((True → ((((((p3 ∧ False) ∨ p4) → False) ∨ ((p1 ∧ True) ∧ ((True ∨ (((True ∨ True) → True) ∧ p4)) ∧ p2))) ∨ (p1 ∨ p5)) ∨ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213777934664577922847483074778 : (((False ∧ (p1 ∨ p1)) ∨ p4) ∨ ((((p5 → True) → (p5 ∧ p3)) ∨ p3) → (p5 ∨ (p4 → ((p3 ∧ (p5 ∨ (p3 ∨ False))) ∨ (p2 ∨ p5)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h3 : (p5 → True) := by
      -- Implications on the right can always be decomposed.
      intro h4
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h5 := h2 h3
    -- We need to get the left conjuct of h5 based on <expert-advice>.
    let h6 := h5.left
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h7
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_195169195324195609243840538497 : (((((p5 ∧ p2) ∧ p5) ∧ p3) ∨ (p5 → True)) ∧ ((((p5 ∨ p4) → (p5 ∨ True)) ∧ (True ∧ (True ∨ p4))) ∨ (((p5 ∧ p2) → False) ∧ p1))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_747772274744383974583244519801 : ((((False → p1) → ((False ∨ ((p1 → p2) → True)) → ((p4 ∧ p4) ∧ ((p5 ∧ False) ∧ ((p2 ∧ ((p4 ∨ False) ∨ (p3 ∨ True))) ∧ p4))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351827701030894572283599183851 : (p4 → ((p1 ∧ (((p4 ∨ (p4 ∨ (True ∨ p1))) ∧ p2) → (False ∨ p3))) ∨ (((p2 ∨ (((p1 ∨ p2) ∨ (p5 → p2)) → p4)) ∨ p3) ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66797698241855512838626948752 : ((True → (p2 ∨ ((((p5 → p2) ∨ p2) → (p5 ∨ (False ∧ p3))) ∨ (p5 → (p1 ∨ (((p2 ∧ p4) → (p4 ∨ (p2 → p2))) → p5)))))) ∨ p5) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337937732859639820306946390350 : (p1 → (((((((p2 ∧ p3) ∨ p1) ∨ False) → (False ∨ p5)) ∨ p5) ∧ False) ∨ (p4 ∨ ((True ∧ p2) → ((True → p2) → (p2 ∨ (p1 ∨ p2))))))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67722869119104032970945524268 : ((p2 → ((((((True ∧ (p4 → (False → True))) ∨ p1) → (False ∧ (p1 ∧ p1))) ∧ (p3 ∧ p3)) ∧ ((p4 ∨ (True → False)) ∧ p1)) ∧ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205450830855225136547657400186 : (((p5 ∨ (p3 ∧ True)) → (p3 ∧ False)) ∨ (((False ∨ p3) ∨ p1) ∨ ((((p5 ∨ (p4 ∨ p3)) → (((True → False) ∧ p4) ∧ p3)) ∧ p1) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217501053543240852709840130102 : ((((p1 ∨ p4) ∧ p1) → p5) → (p4 ∨ ((((p3 → True) ∨ p3) ∧ p5) → ((((False → False) ∨ (((p3 ∨ True) ∧ p5) ∨ p4)) → False) → p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h7 : ((False → False) ∨ (((p3 ∨ True) ∧ p5) ∨ p4)) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h8
      -- False on the left can always be used.
      apply False.elim h8
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h9 := h3 h7
    -- False on the left can always be used.
    apply False.elim h9
  case inr h10 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h11 : ((False → False) ∨ (((p3 ∨ True) ∧ p5) ∨ p4)) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h12
      -- False on the left can always be used.
      apply False.elim h12
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h13 := h3 h11
    -- False on the left can always be used.
    apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345522958962739987660224866432 : (p3 → ((((True ∨ p2) ∧ (p4 ∨ ((((False → False) ∧ p3) → p5) → p1))) → (((p1 ∨ (p1 → (False → (True ∨ p5)))) → p2) ∨ p2)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172787290680179231420140809449 : (((False → False) → (True → ((p3 ∧ (((p5 ∨ p1) ∨ (p2 → p3)) ∨ p3)) ∨ True))) ∨ (True → (True ∨ (p4 → (((False → p4) → False) ∧ p3))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_318903896986466995439638828432 : (p4 ∨ ((True → ((((p3 ∨ (((((p4 → p5) ∧ p2) ∧ (True ∧ (p4 ∨ p4))) → p5) ∧ p1)) → p3) ∨ True) ∨ True)) ∨ (p4 ∧ (p4 ∨ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263690320925606280156340232623 : (True ∧ (((((((((p4 ∧ p2) ∨ p4) → p3) ∨ p3) ∨ True) ∨ (p2 ∧ p2)) → p3) → (p1 ∧ False)) ∨ (p4 ∨ (p4 → (p2 → (p1 ∨ True)))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_195487024404304440137681383480 : (((p2 ∨ (p4 → p3)) ∨ (True ∨ (p1 ∧ True))) ∧ ((p4 ∨ p5) ∨ (((((p1 ∧ p1) → (False ∧ True)) ∨ ((p4 ∨ p5) ∨ False)) ∧ p4) ∨ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47917674049410426159258319806 : ((((p1 ∧ ((((True → p5) ∧ ((p4 ∧ True) ∨ p3)) ∧ (p3 → ((p3 ∨ p4) ∧ (p4 ∧ p3)))) → p3)) → (p5 ∧ True)) → (p5 ∧ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_671162417386406288286037507105 : ((((p2 ∨ ((True ∧ (p4 → p5)) → (((((False ∨ p5) ∧ p4) → ((p3 ∨ (True → p5)) ∧ p2)) ∧ p1) ∧ True))) ∨ ((False → p2) ∨ p5)) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_53883127781483745464600669194 : ((((p2 ∨ True) → (False ∨ ((p3 ∧ p2) ∨ (p4 ∨ False)))) ∨ ((p4 ∨ (p3 ∧ ((p1 ∨ (p5 ∨ (p5 ∨ (p4 ∧ p2)))) ∨ True))) → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_789528110921895050885269325732 : (((p5 ∨ (((p4 → (p3 → True)) ∧ ((p1 ∨ p1) → (p2 ∧ True))) ∨ ((False ∨ (True ∨ p3)) → ((True → ((True ∧ p1) ∧ p5)) ∧ p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49882250881071922318723924262 : (((((((p1 ∧ p3) ∨ (p4 ∧ (False ∧ False))) ∨ ((p1 → True) ∧ (False ∨ False))) ∧ (p2 ∨ p1)) ∨ p3) ∧ (p5 ∧ (p3 ∨ (p2 ∧ False)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_326109574437599927377953761584 : (p5 ∨ (p1 → ((((((p4 ∧ ((p3 ∨ p2) ∧ ((p5 → False) ∧ p2))) ∧ True) ∨ ((p1 → False) ∧ True)) ∧ p4) ∨ (p3 → True)) ∨ (p5 ∨ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40029678425960278051038764066 : ((((((((p3 ∨ False) ∧ ((p1 → (((p1 ∨ p4) ∨ ((True ∨ False) ∧ p2)) ∨ True)) → p5)) ∧ False) ∨ (False ∧ p5)) ∧ True) ∧ False) ∨ True) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192178229405890049396077655302 : (((((p3 ∧ ((p4 ∧ p2) → p5)) ∨ p5) ∨ p4) ∧ True) → ((p3 ∨ ((((p2 → True) → (p3 → ((p2 → False) ∧ p2))) → p4) ∨ False)) ∨ True)) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
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
theorem thm_5_vars_202029107628134951384112091185 : (((((p2 → p3) → p2) ∧ False) → True) ∧ ((p3 ∨ (p4 ∧ ((p5 → p2) → ((False ∧ (p1 ∨ p4)) ∧ p2)))) ∨ (False → ((True → p2) ∧ True)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184379981790414170211608096346 : (((False → (((p5 ∧ False) → (p3 → False)) ∧ (True ∨ True))) → p3) ∨ (False → (p1 → ((True ∨ p5) → ((p1 ∨ (p2 ∧ p4)) → (True ∨ False)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
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
    cases h3
    case inl h6 =>
      -- False on the left can always be used.
      apply False.elim h1
    case inr h7 =>
      -- False on the left can always be used.
      apply False.elim h1
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h11 =>
      -- False on the left can always be used.
      apply False.elim h1
    case inr h12 =>
      -- False on the left can always be used.
      apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_590960122602711729866301063278 : (((((p1 → ((False → p3) ∨ (((((p3 → False) ∧ (p4 → p1)) ∨ p4) ∧ True) ∧ ((False ∧ (p2 ∧ p4)) ∧ (False ∨ p5))))) → p4) ∧ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44624898110663622046314954557 : (((((p3 ∧ (p2 → False)) ∧ (p3 → True)) ∧ ((True ∧ True) ∧ (p4 ∨ (p4 ∧ ((p4 → p1) ∧ (True → (p1 → (True ∨ True)))))))) → p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136266501856102007082603985879 : ((((p5 ∧ (p4 → (p1 → p5))) ∨ p1) → ((False ∨ (p4 → p5)) → (((False ∧ (False ∨ (p5 ∧ False))) ∨ False) ∧ False))) ∨ (p5 → (True ∧ True))) := by
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



