variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150306994664033994718960094655 : ((p4 → ((p5 ∨ (p1 → p1)) ∧ ((p5 ∨ p5) ∧ ((((False ∨ (p2 ∧ p3)) ∨ p4) → p2) ∨ (p1 ∧ p5))))) ∨ ((p3 → (p4 ∨ p3)) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51525233497269191272878172761 : ((((False ∧ p5) → (((False ∧ (True ∧ False)) ∧ True) → (p5 ∨ ((True ∨ p3) ∨ (True → False))))) → ((p2 ∧ ((False ∧ p1) ∨ p5)) ∧ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118425333300641874298517729521 : ((p2 ∨ (p2 ∨ (((True → True) ∨ ((False → (((p3 ∧ p5) ∨ p5) → (p4 ∨ (False ∧ True)))) → (False ∧ (p5 → p4)))) → p4))) ∨ (p4 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_708400220670748010102119981475 : ((((((p1 ∨ p2) → ((p1 → False) ∧ False)) ∧ p5) → (((True ∧ ((True → p2) ∨ (p2 → p4))) ∨ (p4 → (p2 ∧ False))) → (p4 ∨ p5))) ∨ p3) ∧ True) := by
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
    cases h5
    case inl h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h1.left
      let h8 := h1.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h1.left
      let h11 := h1.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h11
  case inr h12 =>
    -- Conjunctions on the left can always be decomposed.
    let h13 := h1.left
    let h14 := h1.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h14
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192694518946852666384873812625 : ((((p3 ∨ (False ∨ (p5 ∨ p5))) ∨ (p2 → True)) → False) → ((((((True → True) ∨ p5) → (p1 → False)) ∨ (p5 ∧ p3)) ∨ p1) ∧ (False → p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p3 ∨ (False ∨ (p5 ∨ p5))) ∨ (p2 → True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- False on the left can always be used.
  apply False.elim h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40418631731053429384384298410 : (((((((True ∧ (False ∧ p4)) ∨ (False → (p2 ∨ False))) ∧ ((p5 ∧ p5) ∧ True)) ∧ (p4 ∨ (True → ((False ∧ False) ∧ p5)))) ∨ False) ∨ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_32329723402083325285626750310 : ((p1 ∨ (p5 ∨ (p4 ∨ (((((((True → p5) → False) ∧ p2) ∧ (p2 ∧ p1)) ∧ (p3 ∨ p3)) ∧ ((True → False) ∨ p5)) ∨ (p4 ∨ True))))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53097446194834413587168617090 : (((p4 ∨ ((True ∨ ((p2 → p4) ∨ (p3 ∨ (p3 ∧ p4)))) ∧ p5)) ∧ (p1 ∨ ((p5 → ((((p1 ∨ p1) ∨ True) ∨ p5) ∧ p3)) ∧ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214191320499396337129027800127 : ((((p3 ∨ p5) → True) → p2) ∨ ((((False → ((p3 ∨ p2) ∨ ((p5 ∧ (p2 ∨ (p1 ∧ p1))) ∨ p3))) → False) → ((p4 ∨ p1) → p5)) ∨ False)) := by
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
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h4 : (False → ((p3 ∨ p2) ∨ ((p5 ∧ (p2 ∨ (p1 ∧ p1))) ∨ p3))) := by
      -- Implications on the right can always be decomposed.
      intro h5
      -- False on the left can always be used.
      apply False.elim h5
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h6 := h1 h4
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h8 : (False → ((p3 ∨ p2) ∨ ((p5 ∧ (p2 ∨ (p1 ∧ p1))) ∨ p3))) := by
      -- Implications on the right can always be decomposed.
      intro h9
      -- False on the left can always be used.
      apply False.elim h9
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h10 := h1 h8
    -- False on the left can always be used.
    apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_801426859143920514835675953713 : (((p2 → ((((p5 ∧ (p2 → (p3 → False))) ∧ p5) ∧ (False ∨ False)) ∨ (p3 ∨ ((((((True ∨ p5) → p3) ∨ p1) → p1) → True) ∨ p5)))) ∨ False) ∧ True) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_151062983954102217597926790700 : (((((False ∧ (((True ∨ False) → ((p5 → ((p1 ∨ p5) → (True → p1))) ∨ p3)) ∧ p1)) ∨ p5) ∨ True) → False) → ((p4 ∨ (p5 → p1)) ∧ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((False ∧ (((True ∨ False) → ((p5 → ((p1 ∨ p5) → (True → p1))) ∨ p3)) ∧ p1)) ∨ p5) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h4 : (((False ∧ (((True ∨ False) → ((p5 → ((p1 ∨ p5) → (True → p1))) ∨ p3)) ∧ p1)) ∨ p5) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h4
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_703819477172958523147477627662 : (((((((p4 → ((True ∨ p5) ∧ p1)) → True) ∨ True) ∨ p3) → (p5 ∧ ((((p4 ∨ p1) ∨ p4) ∨ (p5 → (True ∨ (False ∧ p1)))) ∨ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_302836703302327163654802119823 : (False ∨ (p5 ∨ ((p1 → True) → (((True → ((((p5 ∧ p4) ∨ (p5 ∨ (p5 → False))) ∧ p5) ∧ False)) → (p4 → (p2 → (p4 → p1)))) ∨ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h6 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h7 := h2 h6
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172894547889410716659675245132 : ((p2 ∧ ((((p5 ∧ (p2 → (False ∨ ((False → False) ∨ p4)))) ∨ p3) ∧ p2) ∧ p2)) ∨ ((p1 ∨ p1) ∨ (p4 ∨ ((p5 ∧ (p3 ∧ p5)) → p5)))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112652929751852396618677534989 : ((((((p1 ∨ (p3 ∧ p3)) ∨ p3) → ((True ∧ p1) ∧ (p1 ∧ ((p2 ∨ p2) → (p5 → p5))))) ∧ ((p1 ∨ True) → True)) → p1) ∨ (p5 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_139998922159832342575649400825 : ((((p4 ∧ (p4 ∨ ((p4 ∨ p2) ∨ (((True ∨ (p3 ∨ ((False → p2) ∨ p3))) ∧ p4) ∧ p5)))) ∧ p5) ∨ (False → False)) → ((p2 ∨ p3) ∨ True)) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Disjunctions on the left can always be decomposed.
        cases h9
        case inl h10 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h11 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h12 =>
        -- Conjunctions on the left can always be decomposed.
        let h13 := h12.left
        let h14 := h12.right
        -- Conjunctions on the left can always be decomposed.
        let h15 := h13.left
        let h16 := h13.right
        -- Disjunctions on the left can always be decomposed.
        cases h15
        case inl h17 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h18 =>
          -- Disjunctions on the left can always be decomposed.
          cases h18
          case inl h19 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h20 =>
            -- Disjunctions on the left can always be decomposed.
            cases h20
            case inl h21 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- True on the right can always be proven directly.
              apply True.intro
            case inr h22 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- True on the right can always be proven directly.
              apply True.intro
  case inr h23 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_585404176552739010427398876487 : (((((((p5 → True) ∧ ((p2 ∨ p5) ∧ ((p1 ∧ (((p4 → True) → p5) ∨ (p5 ∧ (p3 ∨ (p1 → True))))) ∨ p4))) ∧ p5) ∧ p4) ∧ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148022285323944542684608855590 : (((((p4 → (False ∧ (True ∨ p3))) ∧ False) ∧ ((p1 ∧ True) ∧ ((p4 ∧ p5) ∧ (p5 ∨ p2)))) ∨ (False → p2)) ∨ ((p1 ∨ p1) ∧ (False → p1))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_163300053242708636203519718547 : ((((p5 ∨ (p5 → (p1 → p5))) → p1) ∨ ((True → (False → ((p1 ∧ p3) ∨ False))) ∨ True)) ∧ (False ∨ (True ∧ ((p2 → (p2 ∨ p3)) ∨ True)))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52612480609364326975792160342 : (((((p1 ∨ (p4 ∧ p3)) → p4) → (((p2 ∧ True) ∨ p3) ∨ (p3 ∧ False))) ∨ ((True ∧ (False ∧ (False ∧ p1))) → ((True ∧ p4) → p4))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h1.left
  let h6 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h6.left
  let h8 := h6.right
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_860872137284620822898163933201 : (((((p4 → (p2 ∧ ((((p4 → (p4 ∧ p1)) → p5) ∨ (p2 ∨ p1)) → ((p3 ∧ p2) ∨ (p2 → (False ∨ p1)))))) → (p1 ∨ True)) → p3) → p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p4 → (p2 ∧ ((((p4 → (p4 ∧ p1)) → p5) ∨ (p2 ∨ p1)) → ((p3 ∧ p2) ∨ (p2 → (False ∨ p1)))))) → (p1 ∨ True)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157519437238458198394353163527 : (((p5 ∨ (((p2 ∧ p4) → ((p4 → False) ∧ ((p4 → True) ∧ (p5 ∨ p2)))) ∧ p1)) ∨ (p1 ∨ p4)) ∨ (((p1 ∨ p2) → (p1 ∨ p2)) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_429540926041758489996670789191 : ((((((p2 → p4) ∨ (((p2 ∨ p1) → ((False ∨ p3) → (p3 → False))) → (p4 ∧ p4))) → (p4 ∨ (p2 → (p3 ∧ p3)))) ∨ (p2 → True)) ∧ True) ∧ True) := by
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
theorem thm_5_vars_789664072649556640461506793933 : (((p5 ∨ (((p3 ∧ p5) ∧ ((p1 ∨ p2) ∧ p5)) ∨ (((False ∨ ((p2 ∨ ((((True → p1) ∧ p2) → True) ∨ p5)) → True)) → False) → p1))) ∨ p3) ∧ True) := by
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
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (False ∨ ((p2 ∨ ((((True → p1) ∧ p2) → True) ∨ p5)) → True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- False on the left can always be used.
  apply False.elim h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50196312128606127822146632446 : ((((p4 ∨ (p1 ∧ ((((p2 ∨ ((p3 ∧ p3) ∧ (True ∨ p5))) ∧ False) ∨ p2) → (p3 → True)))) ∧ p2) ∨ (False ∧ (p2 ∨ (p5 → p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165298708259498376978913048411 : ((((False ∧ p5) ∨ (p5 → (((p3 → False) ∧ p4) → ((p1 ∨ True) → False)))) → (p1 ∧ p1)) ∨ (True ∧ ((p4 ∨ ((p5 ∨ True) → p4)) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134083874697008866385999603792 : (((((p2 → (p4 ∧ (p2 → (p3 ∧ p5)))) → ((((p2 → (False → p4)) ∧ p5) ∨ p5) ∨ (False ∧ p2))) → False) ∨ p1) ∨ (False → (p4 ∧ p4))) := by
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
theorem thm_5_vars_68268242675883305871190653400 : ((p3 → (((p5 ∨ p2) ∧ (((((False ∨ p3) ∧ (p3 ∧ p2)) ∨ ((p4 → p2) ∧ p1)) ∧ ((p3 → p5) ∨ True)) → p1)) ∨ (True ∨ p4))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_718915486873036477477108297754 : (((((p3 ∧ True) → (True ∧ p5)) ∨ (((p2 ∨ p5) ∧ (p2 ∨ (((p5 ∧ ((p3 → (p5 → False)) → p4)) → p2) ∧ p4))) → (p4 → p2))) ∨ p2) ∧ True) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- One of the premise coincides with the conclusion.
      exact h5
  case inr h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h11 =>
      -- One of the premise coincides with the conclusion.
      exact h11
    case inr h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h12.left
      let h14 := h12.right
      -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
      have h15 : (p5 ∧ ((p3 → (p5 → False)) → p4)) := by
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h10
        -- Implications on the right can always be decomposed.
        intro h16
        -- One of the premise coincides with the conclusion.
        exact h14
      -- We have shown the premise of h13, we can now drive its conclusion.
      let h17 := h13 h15
      -- One of the premise coincides with the conclusion.
      exact h17
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54332809428187840682671140875 : (((p3 ∧ (p4 ∨ ((True ∧ False) ∧ (p3 ∧ p4)))) ∧ (((False → ((False ∧ False) ∨ (True ∧ p2))) ∧ p3) → ((False → True) → (p2 → p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190765935358812410734188969607 : ((((((p3 ∨ p1) → p1) → p3) ∧ False) ∨ (False ∧ p1)) ∨ (((((p5 ∨ p1) ∧ False) ∧ (p1 ∨ ((p2 → p2) ∨ p5))) ∨ (p2 → p2)) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51704587357790997401718951277 : (((((((p4 ∨ False) ∨ p2) → p5) ∧ ((p1 ∧ p4) → p4)) → ((p1 ∧ p4) ∨ p5)) ∧ (p3 → (((False → (True ∨ True)) ∧ p1) → p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_226662074814456503570024858864 : (((True ∧ p5) → p4) ∨ ((p1 ∧ ((p3 → p1) ∨ p5)) ∨ (((((p2 ∧ False) ∨ (True ∨ True)) ∨ p3) ∨ (p5 ∧ p4)) ∨ ((p1 ∨ p2) ∨ p3)))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_662017455408948951588306896558 : ((((((p5 → p4) → ((p1 ∨ p1) ∧ (p1 → (((True ∨ False) → p1) ∨ p3)))) → (p4 ∨ ((p5 ∧ p5) ∧ (p4 ∨ p1)))) → (p4 ∧ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_937049091268927491826113090676 : (((((p2 → ((p2 → p2) ∧ p5)) → False) ∧ (((p4 ∨ False) ∧ p5) ∧ (p3 → (((True ∧ (True ∧ p4)) → p3) ∨ ((p1 → False) ∧ p4))))) → p1) ∧ True) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h8 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h9 : (p2 → ((p2 → p2) ∧ p5)) := by
      -- Implications on the right can always be decomposed.
      intro h10
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h11
      -- One of the premise coincides with the conclusion.
      exact h10
      -- One of the premise coincides with the conclusion.
      exact h7
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h12 := h2 h9
    -- False on the left can always be used.
    apply False.elim h12
  case inr h13 =>
    -- False on the left can always be used.
    apply False.elim h13
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_722634526674259840541247743389 : (((((False → False) ∧ p1) ∧ (((((((p2 → p1) ∨ (p4 ∨ p5)) ∧ (p5 → (p3 ∨ p3))) → p4) ∧ True) ∨ (True ∧ (p2 ∧ p1))) ∧ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_907182824997402493775656448923 : (((((p2 ∧ ((p1 ∧ (False ∨ p1)) ∨ p3)) ∨ (((((p2 → p2) → True) → p4) → True) ∨ (p3 ∨ p3))) → (((p3 ∨ True) ∨ p5) → False)) → p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p2 ∧ ((p1 ∧ (False ∨ p1)) ∨ p3)) ∨ (((((p2 → p2) → True) → p4) → True) ∨ (p3 ∨ p3))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h5 : ((p3 ∨ True) ∨ p5) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h6 := h4 h5
  -- False on the left can always be used.
  apply False.elim h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149270276220281522031575923593 : (((True → p4) ∨ ((((((p2 ∧ True) ∨ ((True ∧ True) → True)) ∧ p4) → False) ∧ p1) ∨ (p2 → (p4 ∨ p3)))) ∨ ((True ∨ (p3 ∨ p3)) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172901202247687751262501020084 : ((p2 ∧ ((((p2 → ((p4 ∧ True) ∨ ((True → False) → True))) → p3) → p4) → p2)) ∨ (p3 ∨ (p4 → (((p2 ∨ (False ∧ p5)) ∨ True) ∧ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171920375676374066398763790991 : (((p5 → ((p5 ∨ (((False ∨ (p5 ∨ p2)) ∨ p3) → p2)) ∧ (p1 ∨ p3))) → p2) ∨ (((True ∨ p4) → (True → ((False ∨ p3) ∨ True))) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42861991130525941258806784576 : (((p2 → (((p4 ∨ True) ∨ ((p5 → p2) ∨ p2)) → (p3 ∨ (((((p4 → True) → p2) ∨ p4) → ((p5 ∧ p2) ∨ p4)) → False)))) ∨ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245743195022630057309133554202 : ((p3 ∧ p2) ∨ ((False → p4) → (p3 ∨ ((False ∨ ((((p5 ∧ (p5 → ((p2 ∧ p2) ∨ False))) → p2) ∨ (False → True)) ∨ p4)) ∧ (True ∨ False))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63213879603916524867767824924 : ((p5 ∧ (((((p5 → p5) ∧ (((p1 ∧ p5) ∧ True) ∨ ((p3 → p5) ∨ False))) ∨ p5) ∧ False) ∧ ((((p5 → p2) → p2) ∧ False) ∨ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165433253147422926252963127204 : (((p3 ∧ ((((p5 → p1) ∨ False) ∧ p4) → (p5 ∧ (p2 ∨ True)))) → (True ∧ (p1 ∨ p5))) ∨ ((True ∨ (p1 ∧ p3)) ∨ (p3 → (False ∧ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_681536086152370338262133755953 : ((((True → (p5 → ((p1 ∨ p3) → ((p3 → p2) → (True ∨ ((p1 ∨ ((p4 ∧ True) ∧ p4)) → p1)))))) → ((p3 ∧ (p3 ∨ False)) ∧ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323500537140255903633870705867 : (p5 ∨ (((True → (((p2 → (False ∧ p2)) → p3) ∧ True)) ∧ ((True → (False ∧ (False ∧ False))) ∨ (p5 ∨ (True ∧ p1)))) ∨ (p4 → (True ∨ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300066331267043857764264371643 : (False ∨ ((((p4 ∨ ((p2 → (p5 ∧ p5)) ∧ True)) ∧ (((((p5 → p4) ∧ p5) ∨ p2) ∨ p5) → ((p5 → p1) ∧ True))) ∨ True) ∨ (True ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_613187815348746516511841761973 : (((((((((False ∨ (p2 ∧ (p4 ∨ ((True → p1) → p1)))) ∧ (True ∧ False)) ∧ False) → p4) ∨ ((p2 → p1) → p4)) → (p4 ∧ p2)) ∨ True) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_149779154851921348319420350895 : ((False ∨ (((((False → ((p2 ∨ False) → p4)) → p4) ∨ p4) → ((False ∧ (p5 ∧ p5)) ∧ True)) ∧ (p4 ∧ p5))) ∨ (((p4 ∧ p3) ∧ False) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134006818060346855733533643662 : ((((p3 ∧ (False ∧ (p4 → ((((False → p3) ∧ True) ∧ (False ∨ p3)) ∧ (p5 → (False ∨ (p2 ∧ p2))))))) ∧ p5) ∨ True) ∨ ((p1 ∨ p1) ∨ p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256064218906577372559892312990 : ((True ∨ p4) → ((p2 → p2) ∧ ((p1 ∨ p3) ∨ (((True ∧ p2) ∨ (p3 ∧ (True ∨ ((p2 ∧ p1) ∧ ((p4 ∨ (p4 → True)) ∨ p1))))) ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Disjunctions on the left can always be decomposed.
  cases h1
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_386031596353768739244910870040 : ((((((((True ∧ (((p5 ∨ (p5 ∧ p2)) ∧ p1) ∧ (((True → False) → False) → p1))) → False) → (p3 → p4)) → p5) ∨ (p5 ∨ True)) ∨ p5) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_654356481597703091338496137563 : ((((((p4 ∧ (p3 ∧ ((((p5 → (p1 ∧ p1)) ∨ p4) ∨ p3) → p2))) → ((p1 ∨ (p4 ∨ (p5 ∧ True))) → p5)) ∨ p4) ∨ (p4 ∧ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_262313690736916572107793296011 : (True ∧ ((((p3 ∧ ((p4 ∧ p1) ∧ p5)) ∨ ((False → p3) ∧ p4)) ∨ ((p1 → ((p2 ∨ p3) → ((p2 → p1) ∧ (p3 ∧ p4)))) → p5)) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_606840275590804851504607869289 : ((((((((p4 ∨ ((p3 ∨ p2) ∧ ((p1 ∧ (p2 → p1)) ∧ (p1 ∧ (p4 ∨ p4))))) ∨ True) ∨ p3) ∨ (p5 ∧ (p5 → p4))) ∧ True) ∨ True) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_197134576029895654112265248214 : (((p5 ∨ ((p5 ∨ p5) ∧ (p1 → False))) ∨ False) ∨ (((p1 ∧ (False ∧ False)) → True) ∨ ((False ∨ (True ∧ (((True ∨ p3) → p4) → p3))) → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_250054344503990190600381167340 : ((True → p3) ∨ ((True ∨ True) → ((((p4 → ((p2 ∧ ((p5 → (True ∨ True)) ∧ p3)) ∨ p3)) → p1) → p4) ∨ (p1 → (p3 → (p3 ∨ p5)))))) := by
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
    -- Implications on the right can always be decomposed.
    intro h4
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- Implications on the right can always be decomposed.
    intro h7
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_121542579025597320015920889310 : (((((p1 → (True ∧ True)) ∧ ((True ∨ ((p1 → p4) → (p5 ∧ (p1 ∧ True)))) ∧ (False → (p4 ∧ p1)))) ∨ (p2 → False)) → p3) → (p4 ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_145125478960313843907727946597 : (((p1 ∧ (((p2 → (True ∧ p3)) ∨ p4) → (p3 ∨ p4))) ∨ ((((p3 → (p2 → p3)) → True) ∧ False) → p3)) ∧ ((False → (p5 ∧ p2)) ∨ False)) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h4
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_888485926889345217681885799743 : ((((((p1 ∨ (p5 ∧ (p1 → True))) ∨ (((p3 ∧ p1) ∧ p4) ∨ (p1 ∧ p3))) ∨ ((True ∨ (False ∨ (False ∧ p1))) ∨ False)) → (True → False)) → p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p1 ∨ (p5 ∧ (p1 → True))) ∨ (((p3 ∧ p1) ∧ p4) ∨ (p1 ∧ p3))) ∨ ((True ∨ (False ∨ (False ∧ p1))) ∨ False)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- False on the left can always be used.
  apply False.elim h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_131950842933405441079324041473 : (((True → p3) ∨ (((p5 ∧ p4) ∨ ((False → p1) ∧ ((p1 ∨ p4) ∨ p4))) → (((p2 ∨ p1) ∨ True) ∨ (p3 ∧ p4)))) ∧ ((True ∧ False) → p5)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h10 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h11 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  -- Implications on the right can always be decomposed.
  intro h12
  -- Conjunctions on the left can always be decomposed.
  let h13 := h12.left
  let h14 := h12.right
  -- False on the left can always be used.
  apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336322385783320286825920623733 : (p1 → ((((p3 ∨ p4) ∨ p4) ∧ (p4 → (((False ∨ (p2 ∨ (((p3 → (p5 → p2)) ∨ p1) ∨ True))) ∧ (p2 ∧ p2)) ∧ (p3 ∨ p1)))) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310220646978886529432294475258 : (p2 ∨ ((p2 ∧ ((((p4 ∧ True) → (p1 → False)) → (p2 ∧ p4)) → p2)) ∨ (((True ∨ True) → False) → ((p1 ∧ (p4 ∨ p4)) ∨ (p2 → p5))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (True ∨ True) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346391959475357768333709384481 : (p3 → ((p2 → ((True → (False ∧ ((p4 → p5) → (((p4 ∧ p2) ∨ p5) ∨ ((p4 ∨ (p4 → (p5 ∧ p1))) ∨ p5))))) ∨ p3)) ∨ (p5 → p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_250138829070373705692096980120 : ((True → p5) ∨ (((((((p4 ∧ p3) ∧ (p4 → p3)) ∧ (False → (p2 ∨ True))) ∨ (True → p1)) ∧ ((False ∨ p3) ∨ (p2 ∧ p3))) ∧ p2) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64804334131732753375595082641 : ((p2 ∨ ((p2 ∨ ((p1 → (p2 ∧ p5)) ∧ ((p4 → True) → (((False ∧ (p1 → p3)) ∨ (True → p5)) ∨ ((p1 ∧ p5) ∧ p3))))) ∨ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158632591323744378316209316133 : ((p1 ∧ ((((True ∧ ((p5 ∨ p1) → (p5 ∨ ((p5 ∨ p3) ∧ p1)))) → (p4 ∨ p5)) ∨ p3) ∨ True)) ∨ (False → (False ∨ (True ∨ (p2 → p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_196911698788054847524167941818 : ((((((False ∨ p5) ∨ p2) ∨ p3) ∧ p2) ∨ False) ∨ ((((True ∨ (p4 ∨ ((p5 → True) ∧ (False → True)))) ∨ False) ∧ True) ∨ (p3 → (p2 ∨ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1951823321476981514741693073 : (((p1 ∧ (False ∧ (True ∧ ((((p4 ∧ True) ∨ (p3 → p1)) → p5) ∨ (p3 → p3))))) ∨ (p4 → p3)) ∨ ((p5 ∨ p4) ∨ (False ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_600372013563690799975709710258 : ((((True ∧ (((p5 ∧ False) ∨ ((False ∨ (p2 ∨ ((p2 ∧ p5) → p4))) → ((p3 → ((p1 → True) ∨ (p2 ∧ p1))) → p5))) ∨ True)) ∧ True) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308501646467053933015471139383 : (p2 ∨ (((((p5 ∨ (p1 → (p5 ∨ ((((p5 → p4) ∧ p1) ∧ False) ∧ p3)))) ∨ (p5 ∧ p2)) ∧ True) ∨ ((False ∧ p4) → (p4 → True))) ∨ p4)) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135430872672763979316456651120 : (((p3 ∨ ((p5 → (p1 ∨ (p4 ∧ p4))) ∨ (p5 ∧ (((p3 → p3) → (p1 ∧ p2)) → True)))) ∨ (p2 ∨ (False ∧ p1))) ∨ (p3 → (p4 → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52953748329080614972377058534 : (((((p5 ∨ p4) ∨ ((p2 ∧ p3) ∧ (p4 → (p2 ∨ False)))) ∨ True) ∧ ((p2 ∨ True) ∨ (p4 → ((p3 ∨ (p4 ∨ (False ∨ p1))) ∧ p3)))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39121096743050309463964752943 : ((((True ∧ p5) → ((((((p3 → (p3 ∨ p5)) ∨ ((p2 ∨ p2) → (p5 ∧ p5))) ∧ p5) → p2) ∨ (True ∨ (p4 ∨ True))) ∧ p2)) ∧ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65955467276539202147178947652 : ((p4 ∨ (p3 ∨ (p1 → (p5 ∧ ((((p2 ∧ True) ∧ p1) ∨ ((((p1 ∧ (p5 → p4)) → p1) ∨ (False ∨ p4)) ∧ p2)) ∧ (False ∧ p3)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_698610035924791089216354116740 : (((((p3 ∧ (p2 ∧ False)) ∧ ((p1 → (True ∨ p2)) → (p3 ∨ p5))) ∨ ((p2 ∨ p1) ∨ (False → (((p1 ∨ (p1 ∧ p1)) ∨ True) ∨ p5)))) ∨ p4) ∧ True) := by
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
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_767577048795451296465701076012 : (((p5 ∧ ((((p3 ∧ (((((p4 ∨ (p5 → True)) ∧ p4) ∨ p2) ∧ False) → p5)) → p1) ∨ ((p2 ∨ (p2 → p2)) → (p2 ∧ p1))) ∨ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356279925706118749299722717424 : (p5 → ((((p2 ∨ p3) → ((((p3 ∨ (True ∨ p1)) → True) ∧ p5) → (p3 ∨ True))) ∧ p2) → ((p2 ∧ False) ∨ ((True → (False ∧ False)) ∨ p2)))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_21467820303533634563444388302 : (((((p4 → (False ∧ p4)) → (p4 → p5)) → (p4 ∧ p4)) ∨ ((True → True) → ((((p3 → p3) ∨ p4) ∨ ((True ∧ p2) ∨ p3)) ∨ p5))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314563213521110022898391618647 : (p3 ∨ ((p3 ∨ ((p5 ∧ p4) ∨ ((p3 ∨ ((True ∧ ((p4 ∧ p3) → (True ∧ True))) ∧ True)) ∨ p5))) ∨ (p5 ∧ (((p4 ∧ p1) ∨ True) ∨ p4)))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_932569934289101801653872699424 : (((((p4 → p4) ∧ ((p1 ∨ (True ∨ p3)) ∨ p5)) ∧ ((p3 ∨ (p4 → (((((p2 ∨ p3) → (p4 ∧ p2)) ∧ p4) ∨ p4) ∨ True))) → False)) → p1) ∧ True) := by
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
    cases h6
    case inl h7 =>
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
        have h10 : (p3 ∨ (p4 → (((((p2 ∨ p3) → (p4 ∧ p2)) ∧ p4) ∨ p4) ∨ True))) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h11
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h3, we can now drive its conclusion.
        let h12 := h3 h10
        -- False on the left can always be used.
        apply False.elim h12
      case inr h13 =>
        -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
        have h14 : (p3 ∨ (p4 → (((((p2 ∨ p3) → (p4 ∧ p2)) ∧ p4) ∨ p4) ∨ True))) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h13
        -- We have shown the premise of h3, we can now drive its conclusion.
        let h15 := h3 h14
        -- False on the left can always be used.
        apply False.elim h15
  case inr h16 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h17 : (p3 ∨ (p4 → (((((p2 ∨ p3) → (p4 ∧ p2)) ∧ p4) ∨ p4) ∨ True))) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h18
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h19 := h3 h17
    -- False on the left can always be used.
    apply False.elim h19
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117005598481627010573717550643 : (((False ∨ p2) → (((p5 ∨ p3) ∧ ((p1 → p2) ∧ p4)) ∧ ((((p3 ∨ p4) ∧ True) → ((p1 ∧ (p4 ∧ p5)) ∨ p3)) ∧ p5))) ∨ (True ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37188486474321669298086907254 : (((((p1 ∧ ((p4 ∧ ((p2 → False) → p3)) → True)) ∧ ((((True ∧ (p2 ∨ False)) → (True ∧ (True ∧ False))) → p5) ∨ p1)) ∧ p3) ∧ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208993219411382408676103566051 : ((False ∨ ((p2 ∨ (p1 ∨ p2)) ∧ p5)) → ((True → ((p5 → (p1 → (p2 ∧ ((p3 ∧ False) ∧ (((p5 → p5) ∨ True) ∨ p2))))) ∧ p2)) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- False on the left can always be used.
    apply False.elim h2
  case inr h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h5
      case inr h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58312980194136113605221310752 : (((True ∨ p5) ∧ ((p4 → (p3 ∧ p2)) ∨ (((p5 → (p3 → True)) ∨ ((False ∧ p5) → ((p1 → False) ∧ ((False → p2) ∧ p4)))) → p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321361059396479498780925113738 : (p4 ∨ (True → (((p2 ∨ p2) ∧ (p4 ∧ (((True ∧ p1) ∨ p2) ∧ ((p2 ∧ (p2 → p3)) ∧ (p1 → (True → (True ∧ (False → p5)))))))) → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
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
      let h13 := h9.left
      let h14 := h9.right
      -- Conjunctions on the left can always be decomposed.
      let h15 := h13.left
      let h16 := h13.right
      -- We want to use the implication h16 based on <expert-advice>. So we show its premise.
      have h17 : p2 := by
        -- One of the premise coincides with the conclusion.
        exact h15
      -- We have shown the premise of h16, we can now drive its conclusion.
      let h18 := h16 h17
      -- One of the premise coincides with the conclusion.
      exact h18
    case inr h19 =>
      -- Conjunctions on the left can always be decomposed.
      let h20 := h9.left
      let h21 := h9.right
      -- Conjunctions on the left can always be decomposed.
      let h22 := h20.left
      let h23 := h20.right
      -- We want to use the implication h23 based on <expert-advice>. So we show its premise.
      have h24 : p2 := by
        -- One of the premise coincides with the conclusion.
        exact h22
      -- We have shown the premise of h23, we can now drive its conclusion.
      let h25 := h23 h24
      -- One of the premise coincides with the conclusion.
      exact h25
  case inr h26 =>
    -- Conjunctions on the left can always be decomposed.
    let h27 := h4.left
    let h28 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h29 := h28.left
    let h30 := h28.right
    -- Disjunctions on the left can always be decomposed.
    cases h29
    case inl h31 =>
      -- Conjunctions on the left can always be decomposed.
      let h32 := h31.left
      let h33 := h31.right
      -- Conjunctions on the left can always be decomposed.
      let h34 := h30.left
      let h35 := h30.right
      -- Conjunctions on the left can always be decomposed.
      let h36 := h34.left
      let h37 := h34.right
      -- We want to use the implication h37 based on <expert-advice>. So we show its premise.
      have h38 : p2 := by
        -- One of the premise coincides with the conclusion.
        exact h36
      -- We have shown the premise of h37, we can now drive its conclusion.
      let h39 := h37 h38
      -- One of the premise coincides with the conclusion.
      exact h39
    case inr h40 =>
      -- Conjunctions on the left can always be decomposed.
      let h41 := h30.left
      let h42 := h30.right
      -- Conjunctions on the left can always be decomposed.
      let h43 := h41.left
      let h44 := h41.right
      -- We want to use the implication h44 based on <expert-advice>. So we show its premise.
      have h45 : p2 := by
        -- One of the premise coincides with the conclusion.
        exact h43
      -- We have shown the premise of h44, we can now drive its conclusion.
      let h46 := h44 h45
      -- One of the premise coincides with the conclusion.
      exact h46



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_326321498404589119127568566015 : (p5 ∨ (p4 → (p4 ∧ (p4 → (p1 ∨ ((((False → ((p4 ∧ p4) → (p1 → p1))) → True) ∧ ((((p1 → p1) → False) ∨ p4) ∧ False)) ∨ True)))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51637072299495944907921151238 : ((((((p5 ∧ p2) ∧ (p1 ∨ ((p3 → (p5 ∨ True)) ∧ p2))) ∧ (True → p2)) ∨ True) ∧ ((True ∨ p2) ∨ (p3 ∨ ((p3 → True) → p1)))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_51837091877701096728908674734 : (((((p4 → ((((p4 → p2) ∧ (False → (False ∨ p1))) ∧ True) → p5)) ∧ p5) ∧ p3) ∨ ((p3 → p4) ∨ (((p3 ∧ False) ∧ True) → p2))) ∨ p2) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323512981312113664899143826442 : (p5 ∨ (((p3 ∧ p1) → ((p5 ∨ p2) ∧ (False ∨ ((p5 ∧ ((p5 ∧ (True ∧ (True → (p5 ∧ p4)))) ∨ p2)) → p1)))) ∨ (False ∨ (p1 → p1)))) := by
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
theorem thm_5_vars_831322088433842791189851878088 : ((((p1 → (((((p2 ∧ p4) ∧ (False ∧ p5)) ∨ ((p3 ∨ (p3 → (False ∧ False))) ∨ ((p1 ∨ (p4 → p5)) ∨ False))) ∨ p5) → False)) ∧ p1) → p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : p1 := by
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h6 : ((((p2 ∧ p4) ∧ (False ∧ p5)) ∨ ((p3 ∨ (p3 → (False ∧ False))) ∨ ((p1 ∨ (p4 → p5)) ∨ False))) ∨ p5) := by
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
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h7 := h5 h6
  -- False on the left can always be used.
  apply False.elim h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39319055380848294070123209070 : (((p2 ∧ (((p1 → (p3 ∨ True)) ∧ (p4 ∧ ((p5 → ((p2 → p5) ∨ ((True ∨ p3) → (p3 ∨ True)))) → (p1 ∧ p1)))) ∨ p1)) ∧ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167544268485483707773117552920 : (((((p4 ∧ ((False ∨ (False ∨ ((p5 → p1) → p2))) ∨ p2)) ∧ p1) ∧ p2) ∨ (p4 ∨ p3)) → (p3 ∨ (p3 ∨ ((False → p1) ∧ (p3 → p4))))) := by
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
    cases h8
    case inl h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- False on the left can always be used.
        apply False.elim h10
      case inr h11 =>
        -- Disjunctions on the left can always be decomposed.
        cases h11
        case inl h12 =>
          -- False on the left can always be used.
          apply False.elim h12
        case inr h13 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- Implications on the right can always be decomposed.
          intro h14
          -- False on the left can always be used.
          apply False.elim h14
          -- Implications on the right can always be decomposed.
          intro h15
          -- One of the premise coincides with the conclusion.
          exact h7
    case inr h16 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h17
      -- False on the left can always be used.
      apply False.elim h17
      -- Implications on the right can always be decomposed.
      intro h18
      -- One of the premise coincides with the conclusion.
      exact h7
  case inr h19 =>
    -- Disjunctions on the left can always be decomposed.
    cases h19
    case inl h20 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h21
      -- False on the left can always be used.
      apply False.elim h21
      -- Implications on the right can always be decomposed.
      intro h22
      -- One of the premise coincides with the conclusion.
      exact h20
    case inr h23 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h23



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_614836152118143723058601325603 : (((((False ∨ ((p1 ∨ False) ∧ (((p2 ∨ p5) ∧ p5) ∧ (p5 ∨ ((p3 ∧ p2) ∨ (True ∧ p1)))))) ∨ (p5 ∨ (True ∨ (p4 ∨ p2)))) ∨ False) ∨ p3) ∧ True) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_352296766055857352371120824328 : (p4 → ((p4 ∨ ((p1 ∧ p1) ∨ p5)) → ((((p1 → p3) ∧ (p5 ∨ (((p2 → p5) ∨ False) → (False → p2)))) ∧ ((False → p2) ∧ p1)) → p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h5.left
    let h10 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h11 =>
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h12 : p1 := by
        -- One of the premise coincides with the conclusion.
        exact h10
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h13 := h6 h12
      -- One of the premise coincides with the conclusion.
      exact h13
    case inr h14 =>
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h15 =>
        -- Conjunctions on the left can always be decomposed.
        let h16 := h15.left
        let h17 := h15.right
        -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
        have h18 : p1 := by
          -- One of the premise coincides with the conclusion.
          exact h17
        -- We have shown the premise of h6, we can now drive its conclusion.
        let h19 := h6 h18
        -- One of the premise coincides with the conclusion.
        exact h19
      case inr h20 =>
        -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
        have h21 : p1 := by
          -- One of the premise coincides with the conclusion.
          exact h10
        -- We have shown the premise of h6, we can now drive its conclusion.
        let h22 := h6 h21
        -- One of the premise coincides with the conclusion.
        exact h22
  case inr h23 =>
    -- Conjunctions on the left can always be decomposed.
    let h24 := h5.left
    let h25 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h26 =>
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h27 : p1 := by
        -- One of the premise coincides with the conclusion.
        exact h25
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h28 := h6 h27
      -- One of the premise coincides with the conclusion.
      exact h28
    case inr h29 =>
      -- Disjunctions on the left can always be decomposed.
      cases h29
      case inl h30 =>
        -- Conjunctions on the left can always be decomposed.
        let h31 := h30.left
        let h32 := h30.right
        -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
        have h33 : p1 := by
          -- One of the premise coincides with the conclusion.
          exact h32
        -- We have shown the premise of h6, we can now drive its conclusion.
        let h34 := h6 h33
        -- One of the premise coincides with the conclusion.
        exact h34
      case inr h35 =>
        -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
        have h36 : p1 := by
          -- One of the premise coincides with the conclusion.
          exact h25
        -- We have shown the premise of h6, we can now drive its conclusion.
        let h37 := h6 h36
        -- One of the premise coincides with the conclusion.
        exact h37



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_78268196989566167036565116162 : (((p4 → ((((p2 ∨ p4) → (((p3 ∨ (p3 ∨ ((p3 ∧ p3) → p3))) → False) ∨ (p4 → p2))) ∨ (p3 ∧ p2)) ∨ (p2 → p2))) → p3) → p3) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p4 → ((((p2 ∨ p4) → (((p3 ∨ (p3 ∨ ((p3 ∧ p3) → p3))) → False) ∨ (p4 → p2))) ∨ (p3 ∧ p2)) ∨ (p2 → p2))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52217833455443287897967865194 : ((((p5 ∧ False) → (p4 → (((((p3 ∨ False) → True) ∧ p2) → True) → (p2 ∨ p1)))) → ((p1 ∨ (p5 ∨ p4)) ∨ ((p1 → p2) ∨ True))) ∨ p2) := by
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
theorem thm_5_vars_780694292555299452541422131487 : (((p2 ∨ ((False ∨ ((p5 → p4) → (p2 → (p5 ∧ p4)))) → ((p1 ∧ (p1 ∧ ((p2 → p4) ∧ p4))) → (((True ∧ True) ∧ False) ∨ p4)))) ∨ p1) ∧ True) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h6.left
  let h8 := h6.right
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h9 =>
    -- False on the left can always be used.
    apply False.elim h9
  case inr h10 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h8
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_797262424073309334877789955735 : (((p1 → (((p5 → (p1 → (p5 → (((p4 → False) → p3) ∨ ((((True ∨ p5) ∨ (p3 → (p3 → p4))) → False) ∨ p5))))) ∨ p5) ∨ p4)) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258643866796351741584603727520 : ((p5 ∨ p5) → (((p1 ∧ (p4 ∧ ((False ∧ p2) → False))) ∨ ((((p1 → (True → p3)) → (((p4 ∨ False) ∧ p3) ∧ p4)) → True) ∧ p2)) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3



