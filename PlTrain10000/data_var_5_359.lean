variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147186722058988257790127065089 : (((p3 ∨ (p1 ∧ (((((p3 → p5) ∨ p3) ∨ p4) ∨ (p3 ∨ p3)) ∨ (p2 → ((p4 → p5) → p2))))) ∧ p1) ∨ (p2 → (p1 → (p3 ∨ True)))) := by
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
theorem thm_5_vars_162492735501171722979369456812 : (((p5 ∧ (((True ∨ p5) → ((False ∨ (p2 ∨ (p1 → p3))) ∧ (p1 → p2))) ∧ False)) ∨ True) ∧ ((p1 → ((False ∨ False) → (p5 → False))) ∨ False)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
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
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347378763748792016252915251674 : (p3 → (((p1 ∨ (False → (p1 ∨ True))) → (p5 ∨ p4)) ∨ ((((p1 ∧ (False ∧ p2)) → (p5 ∧ False)) → ((True ∨ True) ∨ p2)) ∧ (p2 ∨ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173305037619119197177862997101 : ((p1 → ((p1 ∨ p2) → (False ∧ (p2 ∧ ((((p1 → True) ∨ True) → p5) ∨ p2))))) ∨ ((((p5 → False) ∨ p1) ∧ (p1 → (p4 → p5))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218914068406321069409384629484 : ((p3 ∧ ((p1 ∨ p4) → p2)) → ((p4 ∧ ((True → ((((p4 ∨ False) → p4) ∧ True) → (p4 ∧ (True ∨ False)))) ∧ p3)) ∨ (False ∨ (p1 → p2)))) := by
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
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h5 : (p1 ∨ p4) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h5
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1520553899179555398693887886 : (((((True ∨ p1) ∨ (p4 ∨ p1)) ∨ p2) → ((False ∨ (True → False)) ∨ ((p3 ∨ (((p2 → p1) ∨ True) ∨ True)) → True))) ∨ (p2 ∧ p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h7
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h10
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h12
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h13 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h14
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_201273509159233129057581593276 : ((p3 → (p3 ∨ ((True → (p1 ∨ p3)) → p2))) → ((p1 ∨ (p2 ∨ (False ∨ (False ∨ ((((p3 → p4) ∨ p1) ∨ (p4 ∨ p4)) → p1))))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_85950946248343575209560352623 : (((((p2 ∨ (p1 ∨ False)) ∨ (False → (p4 ∨ False))) → False) ∧ ((((True → ((p3 → p2) → False)) ∧ p2) ∧ (p1 ∨ (False ∧ p4))) → p2)) → p5) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : ((p2 ∨ (p1 ∨ False)) ∨ (False → (p4 ∨ False))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- False on the left can always be used.
    apply False.elim h5
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h4
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119086885211469752718976771930 : ((p1 → ((((p1 ∧ False) ∧ (p4 ∨ (True ∧ (False ∧ p2)))) → (p4 ∧ (False ∧ p1))) → ((p3 ∨ ((p4 ∧ p2) ∧ False)) → p4))) ∨ (False → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60086567427245100807074201983 : (((p3 ∨ True) → (((p3 ∧ ((p5 ∧ (p1 → (p5 ∧ ((p5 ∨ p4) → (p1 → False))))) → (p2 ∨ p4))) ∧ (p5 ∨ (p1 ∧ p3))) ∧ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157268722848727069140610986615 : ((((True → (False ∧ p4)) ∧ ((p4 ∧ p3) ∨ (((((p1 ∧ p1) → p5) ∨ p2) ∨ p4) ∨ True))) → p1) ∨ (((True ∧ p5) → False) ∨ (p4 ∧ True))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- Disjunctions on the left can always be decomposed.
        cases h12
        case inl h13 =>
          -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
          have h14 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h2, we can now drive its conclusion.
          let h15 := h2 h14
          -- We need to get the left conjuct of h15 based on <expert-advice>.
          let h16 := h15.left
          -- False on the left can always be used.
          apply False.elim h16
        case inr h17 =>
          -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
          have h18 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h2, we can now drive its conclusion.
          let h19 := h2 h18
          -- We need to get the left conjuct of h19 based on <expert-advice>.
          let h20 := h19.left
          -- False on the left can always be used.
          apply False.elim h20
      case inr h21 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h22 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h23 := h2 h22
        -- We need to get the left conjuct of h23 based on <expert-advice>.
        let h24 := h23.left
        -- False on the left can always be used.
        apply False.elim h24
    case inr h25 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h26 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h27 := h2 h26
      -- We need to get the left conjuct of h27 based on <expert-advice>.
      let h28 := h27.left
      -- False on the left can always be used.
      apply False.elim h28



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147539170624799907551126026512 : (((p2 → (((((((p2 ∧ False) ∧ False) → p5) ∨ p3) ∨ p2) ∨ p5) → (((p4 ∧ p4) ∧ True) ∧ p3))) ∨ p1) ∨ (((p4 ∧ p2) ∨ p5) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_721323535937619474239812439294 : (((((p5 → p1) → (False ∨ p1)) → (p1 → (((p5 ∨ (((p4 → p4) ∧ p5) ∧ p5)) ∨ (p2 ∨ (((p4 ∧ False) ∨ False) ∨ p1))) ∨ True))) ∨ False) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299355396067215469454085945171 : (False ∨ (((True ∧ p3) ∧ (((p4 → (p5 ∨ (p4 → ((False ∨ ((p1 → p3) ∧ p4)) → ((p2 → p3) → p3))))) ∧ False) ∨ (p1 → p3))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68274795954045224840696470238 : ((p3 → ((((p3 ∧ p4) ∧ (True ∨ ((((p4 → p5) → p1) ∨ False) ∨ ((True ∨ (p2 → (p4 ∨ p1))) ∧ True)))) → p5) → (p4 ∧ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45935094742300088285341178056 : (((p5 → (((((((p1 → False) ∨ ((p1 → p5) ∨ p3)) ∨ (p2 ∧ False)) ∨ (False ∧ True)) → (p2 ∧ False)) → (False ∧ p4)) ∧ True)) → p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228232558911577881527281052694 : ((p5 ∧ (p5 ∨ True)) ∨ (((p5 ∨ p2) ∨ p4) ∨ ((((p2 → (p5 ∨ True)) ∨ (((p1 ∨ p5) ∧ (p2 ∨ (p1 ∨ False))) ∧ False)) ∧ True) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42555255986749429039187508826 : (((p1 ∨ (p2 ∧ ((True ∨ (p3 ∧ ((((p3 ∧ False) → p3) → p2) ∨ p1))) ∧ (((p4 ∨ False) ∧ (p5 → (p5 → p2))) ∧ p2)))) ∨ True) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_656779938262575467205139644559 : ((((((((p4 ∨ False) → p1) ∧ p3) → p5) → (False ∧ (((p5 ∧ (((False ∧ (p2 ∧ p3)) ∧ p4) → False)) → p2) ∧ p5))) ∨ (True → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53323212366765738231141098169 : (((p4 → ((p4 ∧ ((((p5 → p3) ∧ p3) ∨ False) ∨ p3)) ∧ p4)) ∨ (p2 → (False ∧ (((True ∨ p3) ∨ (True → p3)) → (True ∧ p4))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66352411772374249586072871009 : ((p5 ∨ (p5 ∧ (p1 → ((p2 ∧ ((((p5 ∨ ((p3 → True) → True)) → True) → p1) → ((p5 ∨ (p2 ∧ p5)) ∨ (p4 ∧ p4)))) ∨ p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39288186668936243044510721308 : (((p1 ∧ ((((p1 ∧ p5) → ((((p1 → p2) → p4) → p5) ∧ (p2 ∨ p3))) → (p1 → (p1 → False))) ∧ ((p5 ∨ p3) ∨ True))) ∧ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118785118009112056485161686274 : ((p5 ∨ (p5 ∨ (p2 ∧ (((p1 ∨ (((p2 ∧ ((True → p5) → p4)) ∧ p5) → p5)) ∧ p4) ∧ (((p5 ∧ p1) ∧ p3) ∨ p3))))) ∨ (False → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_658641485537482975012769337564 : ((((p3 ∨ (p1 ∨ ((((((((False ∧ (p4 → True)) ∧ p4) → (p3 ∧ p2)) ∧ False) → p4) ∧ False) ∧ (p3 ∨ p4)) ∨ False))) ∨ (False → p5)) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_336272434623270876663512104822 : (p1 → (((((((False ∧ p4) → False) ∨ (True ∧ (True ∨ p2))) → p4) ∨ True) ∨ ((True ∧ p3) → ((p2 → p3) ∨ (p4 → (True ∨ p4))))) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_608188206665303491873147804645 : ((((((p5 ∧ (((((p4 → False) ∧ False) ∨ (p2 ∧ p2)) → (p5 ∨ (p4 → (((p3 → p1) ∧ False) ∨ False)))) → p3)) ∧ p2) ∨ True) ∨ p5) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48066946250608649373665521656 : (((((False ∧ False) → (p2 ∨ (False ∧ (p5 → p2)))) → (((p2 ∨ False) → (p1 ∨ (True ∧ ((p4 ∨ True) → True)))) → True)) → (p2 ∧ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53980601480924795593242682965 : (((((p2 ∨ (p3 ∨ (p1 → (p5 → p4)))) ∨ p1) ∨ p3) → ((((True → False) → p3) ∨ (True ∧ ((p4 ∧ p2) ∨ (True ∧ p4)))) ∧ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_19092756823051725340832959003 : ((((((p4 ∨ (p2 → (True ∧ (p4 → p1)))) ∨ (p1 → True)) → p5) → (p2 ∨ (p4 → p1))) → ((False ∨ (p1 ∨ (p4 ∧ False))) ∨ True)) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_758641468839704504447696973761 : (((p2 ∧ ((((p5 ∨ ((((p2 → (p3 ∨ ((False → p4) → p2))) ∨ p2) → False) → p1)) → p5) ∨ (((p2 → p5) → False) → False)) ∨ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49324478031659083560227129927 : (((p4 ∨ ((p5 → ((((p5 ∨ ((p2 → (p5 ∧ p4)) → ((p4 ∧ False) → p2))) ∨ p3) → False) ∧ p3)) → p3)) ∨ (False ∨ (True ∧ True))) ∨ p3) := by
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
theorem thm_5_vars_728996637596468061886017059149 : (((((p2 ∨ p3) ∧ True) → ((((p2 ∧ (True ∨ ((((p5 ∨ p1) → p1) → False) ∨ p2))) → (True ∧ p3)) ∨ p2) → ((p4 → p2) → p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_3003346926251013864791397043 : (((p5 ∧ p2) ∨ p5) → (((((p5 ∨ (p2 ∧ p2)) ∨ False) ∨ p2) → ((p3 → (p5 ∧ (p3 ∨ False))) ∧ p3)) ∨ (p1 ∨ (p4 ∨ p5)))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178840261639759442715605449340 : ((((True → p3) ∨ p5) → ((False ∨ p5) ∧ (((True → p3) → p2) → p4))) ∨ (False → ((((p2 ∧ p5) ∨ p1) ∨ p4) ∧ ((True ∨ p2) ∨ True)))) := by
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
theorem thm_5_vars_53657818334075309650452653644 : ((((False ∨ p5) ∧ ((True → (True → (p4 ∨ p5))) ∨ False)) ∧ ((False ∧ ((False ∨ (p2 ∧ True)) ∨ (p3 ∧ (True ∧ p5)))) ∧ (p3 → True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_352414162424434810407295648002 : (p4 → ((p5 ∧ (p4 ∨ False)) ∨ ((((p4 ∧ (p2 ∨ ((p4 → p3) ∨ True))) ∨ (p5 ∨ (p1 ∧ ((p4 ∨ p5) ∧ p2)))) → False) ∨ (False → p4)))) := by
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
theorem thm_5_vars_261147513801593003869655270850 : ((p4 → p4) → ((p3 → ((p1 ∧ ((False ∧ (p5 → (p4 ∨ False))) ∨ p4)) ∨ (p1 ∨ ((p5 → (p3 ∨ p1)) ∨ True)))) ∧ (p1 ∨ (p5 → p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299302226648235723513202823172 : (False ∨ (((p3 ∨ (((p3 ∨ (p3 → (p3 ∨ p4))) → p3) → p1)) → (p2 ∨ (p5 ∨ (p4 ∧ ((p2 ∨ ((False → p4) → False)) ∧ p4))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_221242845362939039575271733151 : (((p2 ∨ p1) ∨ True) ∧ (((True → (False ∧ (((p4 ∧ False) ∨ (False ∨ p5)) ∨ ((p2 ∨ p4) ∨ p3)))) → (p4 → True)) → ((True → False) → p5))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_124094004827188991043239416082 : (((((False ∨ ((p5 → (p2 ∧ p1)) ∧ p5)) ∧ p3) ∨ False) ∧ ((p1 ∨ (((p2 → p2) ∧ ((p5 ∨ True) → p5)) ∨ p5)) → p4)) → (p4 ∧ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
      -- False on the left can always be used.
      apply False.elim h7
    case inr h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h11 : (p1 ∨ (((p2 → p2) ∧ ((p5 ∨ True) → p5)) ∨ p5)) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h10
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h12 := h3 h11
      -- One of the premise coincides with the conclusion.
      exact h12
  case inr h13 =>
    -- False on the left can always be used.
    apply False.elim h13
  -- Conjunctions on the left can always be decomposed.
  let h14 := h1.left
  let h15 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h14
  case inl h16 =>
    -- Conjunctions on the left can always be decomposed.
    let h17 := h16.left
    let h18 := h16.right
    -- Disjunctions on the left can always be decomposed.
    cases h17
    case inl h19 =>
      -- False on the left can always be used.
      apply False.elim h19
    case inr h20 =>
      -- Conjunctions on the left can always be decomposed.
      let h21 := h20.left
      let h22 := h20.right
      -- We want to use the implication h21 based on <expert-advice>. So we show its premise.
      have h23 : p5 := by
        -- One of the premise coincides with the conclusion.
        exact h22
      -- We have shown the premise of h21, we can now drive its conclusion.
      let h24 := h21 h23
      -- We need to get the right conjuct of h24 based on <expert-advice>.
      let h25 := h24.right
      -- One of the premise coincides with the conclusion.
      exact h25
  case inr h26 =>
    -- False on the left can always be used.
    apply False.elim h26



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_247468246908544507889773564240 : ((False ∨ p3) ∨ ((((((True → False) ∧ ((p4 ∨ (((p5 → p4) ∧ (p2 ∨ p3)) ∨ False)) ∨ p3)) ∧ (p2 ∨ p3)) ∨ True) ∨ (p3 ∨ False)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171939625877059913333773717060 : (((((True → p1) → (p2 ∧ ((p5 → False) ∨ (p3 ∨ p5)))) → p5) ∧ (False ∧ p5)) ∨ (((((False → p2) ∧ p4) ∨ (True ∨ False)) → p4) → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((False → p2) ∧ p4) ∨ (True ∨ False)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305581392604981085736772650797 : (p1 ∨ (((False ∨ (p1 ∧ ((p4 ∨ p3) → ((p1 ∨ p5) → p5)))) ∨ p2) ∨ (((p4 → (p3 ∨ ((p2 ∧ p5) → p4))) ∧ True) ∧ (True ∨ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56629195441068229830108821962 : ((((p3 ∧ p4) ∧ p3) ∧ (True → ((False ∨ ((p1 → p3) ∨ (True → p1))) → ((p3 → (p3 → p4)) ∧ (p3 → ((p1 ∨ True) ∧ True)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_704567857752424686966488585280 : (((((p3 ∨ p4) ∨ (p5 ∨ (((p1 → True) → p3) ∧ True))) → (((p3 ∨ p5) ∨ True) ∨ (p5 ∨ (False ∨ ((p5 → (False ∨ True)) ∨ True))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227943241452167027215711565622 : ((p3 ∧ (p2 ∧ p3)) ∨ ((p5 → ((((p2 ∨ True) ∧ (p2 ∨ ((p3 ∧ False) ∧ p5))) ∧ p5) ∧ True)) ∨ ((p5 ∧ p5) ∨ ((p2 → True) ∨ p2)))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200805524055824777410639679670 : ((p5 ∧ ((p1 ∧ (True ∨ (p4 ∧ p5))) → p5)) → ((True ∧ (p5 → (p2 ∨ (False ∨ p3)))) ∨ ((False ∧ False) → (p3 ∨ ((True → p1) ∨ False))))) := by
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
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158475300723178209541596888163 : (((p5 → False) ∨ (p2 ∧ (((True ∨ ((((False ∨ (p2 ∨ False)) ∨ True) ∧ False) ∨ p3)) → p5) ∨ p2))) ∨ (p2 → (((p2 ∨ p1) → True) ∧ p2))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50728756002350794593882246926 : ((((p4 → p3) → (((p1 → ((False ∨ p2) ∨ ((p2 ∨ p1) ∨ (p5 ∨ p4)))) ∨ (False ∨ False)) ∨ p4)) → (((False → p3) → p1) ∨ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_176274722655783335710123690697 : (((((p1 → (p4 → (p1 ∧ p1))) ∨ p5) ∧ (p2 ∧ False)) ∨ (p1 → p1)) ∧ ((p1 ∨ (False ∧ p1)) ∨ (((False ∧ True) ∧ p5) → (p1 ∨ p3)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246790027387854267195540497924 : ((p5 ∧ p5) ∨ (p2 → ((p1 ∨ (((p4 ∧ (p4 ∧ (True ∧ p3))) → (p1 ∧ p1)) ∧ p2)) ∨ (True ∨ (((p1 ∧ (False → p3)) → p1) ∧ p3))))) := by
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
theorem thm_5_vars_171337134260554097107607962346 : ((((((((p3 ∨ (p1 ∧ p5)) ∨ p4) ∧ p3) ∧ (p3 → p3)) ∨ True) → False) ∧ p1) ∨ (False → (True ∧ (True → (p4 → ((p2 ∨ True) ∧ p5)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53157404149281999869106134304 : (((((p2 ∧ True) ∧ (p5 ∧ (p5 → (p4 ∨ (p2 ∧ p4))))) ∨ True) ∨ ((p3 → ((p1 → p4) ∨ (p3 ∨ (True ∨ p5)))) → (p4 → p4))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157673874853360684687812141233 : (((((p1 → p3) → False) ∨ ((p2 → (((p2 → True) → False) ∧ p5)) ∧ False)) ∨ (p3 ∧ (p5 ∧ p4))) ∨ (((p4 ∧ p5) → (p1 ∧ p1)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_358176505252023431159164437707 : (p5 → (p3 ∨ (((((p4 ∧ (p5 → (p4 ∨ p3))) → ((p4 ∧ p5) → p4)) → p2) ∧ p1) ∨ ((False ∨ ((p4 ∧ False) ∨ p3)) → (p5 ∨ p2))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- False on the left can always be used.
      apply False.elim h7
    case inr h8 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_639546162751570229351695765574 : ((((((p2 → False) ∨ True) ∧ ((((p2 ∨ False) → p5) → False) → ((((p4 ∧ p3) ∧ ((p2 ∧ (p2 ∨ p3)) ∨ p3)) → p3) ∧ p3))) → p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149801952740174789574371255166 : ((False ∨ (p4 ∧ ((True ∨ (p5 → (p5 ∨ ((p2 ∨ (p4 ∨ (p5 ∧ p5))) ∧ (p2 ∨ p5))))) ∧ (p5 → False)))) ∨ (p2 ∨ (p3 ∨ (p3 ∨ True)))) := by
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
theorem thm_5_vars_310937741919861084159005159083 : (p2 ∨ ((True ∨ p2) ∧ ((((p5 ∧ p1) → p3) ∧ ((p1 ∧ (p1 → p3)) ∨ p2)) ∨ (((p2 ∨ p2) ∧ p5) ∨ (((p2 → p5) ∨ True) ∨ False))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
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
theorem thm_5_vars_624850261354267764630293127586 : ((((p5 ∨ (((p4 → (p5 → (((p3 ∧ False) ∧ ((p5 ∧ False) ∧ True)) ∧ p2))) → ((p1 → p2) ∧ True)) → ((p4 ∧ p4) → p5))) ∨ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46934424873003783010496501278 : ((((p1 ∧ (((p4 ∨ p5) → (((False → p1) → (p1 ∨ True)) ∨ (p4 ∧ ((p4 → (False → p2)) ∧ p1)))) ∧ False)) ∨ p2) ∨ (False ∧ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185561881127322902931854313587 : ((p4 ∨ ((False ∨ (p2 ∨ False)) ∨ ((p1 ∧ p1) ∨ (p1 → p2)))) ∨ ((((p1 ∧ p1) → p1) → p3) ∨ (p4 ∨ (((True ∧ p3) ∧ p2) → True)))) := by
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
theorem thm_5_vars_2206566575213461538623420784 : ((p5 → ((True ∧ True) → ((p5 → False) ∨ ((p5 → p1) → ((p2 ∨ p5) → False))))) ∨ (p2 ∨ ((p3 ∨ p4) ∨ ((True ∧ False) → True)))) := by
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
theorem thm_5_vars_156888010407795085143839574767 : ((((((((p1 → (p5 ∨ (False → p2))) ∧ p5) ∨ True) ∧ p4) ∧ (p4 ∧ (p1 ∧ p2))) ∨ p2) ∨ False) ∨ (True ∨ ((p4 ∨ (p4 ∨ p3)) ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_663870962521322209092915677866 : ((((p3 ∧ (((p2 ∧ p3) ∨ p3) → ((((p4 → p2) ∧ p5) ∧ ((((p5 ∧ (p4 ∨ p5)) ∨ p2) ∧ p2) ∧ False)) → True))) → (p1 → p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48452917677246857025472088910 : (((p5 → (p5 → ((((True → p2) ∧ p3) → p1) → (((p5 ∨ p2) ∧ (p5 → (False → (p3 → (p3 ∨ p1))))) ∨ p1)))) → (p3 ∨ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305866382794541285746117664577 : (p1 ∨ (((True ∧ ((p4 → p3) → p1)) ∨ p2) ∨ ((p2 → (True ∨ ((p1 ∨ ((p4 → ((p2 → p2) → True)) → p3)) → p5))) ∨ (p3 ∧ False)))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165993712266872685845027688444 : (((p3 ∧ p1) ∨ (((True ∨ (p3 → p1)) ∧ ((p4 ∨ p4) → (p4 ∧ (p3 ∨ p3)))) ∨ True)) ∨ (((p4 ∨ p2) ∧ (p5 → p3)) ∧ (p2 ∨ False))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_673873647488483053576831603513 : (((((p4 ∧ False) → ((((True ∧ (False ∧ p5)) ∨ ((p5 ∧ False) ∧ (p4 ∨ True))) → ((p5 ∨ p2) ∨ False)) ∨ p5)) → ((True → p5) → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313928280390516548300779697539 : (p3 ∨ (((p4 ∨ (((p2 ∧ (p3 → p4)) ∨ (((((p2 ∨ p5) → p5) → p4) ∧ p2) → ((False → p1) ∧ True))) → False)) ∧ p4) ∨ (p3 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41367354663865318827218640379 : (((((((True ∧ (p5 ∧ p3)) ∨ p1) → p1) → (True ∧ ((p5 ∨ (p1 ∨ False)) ∧ p3))) → (p5 ∧ ((p5 ∨ (p5 ∧ p4)) → p4))) ∨ True) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_682320914213373648427502289099 : (((((((((p4 → False) → p4) ∨ (p2 → (p3 ∨ p1))) ∧ p3) ∧ (p5 ∨ p2)) ∨ (p2 ∨ True)) ∧ (True ∨ (False ∧ (p4 ∨ (p5 ∧ p3))))) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_809246700574510004979208018689 : (((p5 → (((((p3 ∨ p5) ∧ (((p2 ∧ (p4 → p3)) ∨ True) ∨ False)) ∨ p3) → (p5 → ((p1 → (p4 ∧ (p3 ∨ p2))) ∧ p4))) ∨ p5)) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_652402915406832164953099138620 : ((((p4 ∧ (p4 → (((p5 → (p1 ∨ p5)) → (p1 → (((True ∧ p5) ∨ (False ∨ ((p2 ∨ p2) → True))) ∨ p1))) → False))) ∧ (p2 → p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206865153113108027460027059727 : (((((p4 ∧ p1) → p5) ∧ p2) ∧ p5) → (True ∧ (((((True ∧ ((p3 ∨ p4) → False)) ∧ True) ∨ p2) ∧ ((False ∧ (True ∨ p2)) ∨ p3)) ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46887697744650946031225965847 : (((((((True → False) ∨ (p1 → ((False ∧ (p2 → p4)) ∨ False))) → ((((p5 → p5) → p1) ∧ True) ∨ False)) ∨ p2) ∨ p3) ∨ (p2 ∨ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_766763385735899694611190438346 : (((p4 ∧ (p2 ∨ ((((p2 → p5) ∧ p3) ∧ ((p1 ∧ (p3 → (p4 ∧ p5))) ∨ p4)) ∧ ((((False → p2) → p3) ∨ p3) ∧ (p5 → False))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111624615540259629115620167824 : (((((((p4 → (p5 ∨ p3)) ∧ p2) ∨ ((p5 → p1) ∨ (((p3 ∨ (p5 ∧ p1)) → p1) ∧ p3))) ∨ (p4 ∧ p3)) ∨ True) ∨ p3) ∨ (p5 ∧ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_781433056532143525140080041172 : (((p2 ∨ (p4 ∧ (((p5 ∧ p1) ∨ ((p5 ∨ (((p2 → ((((True → p1) → p1) ∧ (p1 ∨ True)) ∨ False)) → p5) ∨ False)) ∨ p4)) ∨ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45095311537873891384832921981 : ((((True ∨ True) → (((True → p5) ∧ ((((p1 ∧ (p3 ∧ ((True ∨ p3) ∧ p1))) ∨ (p1 ∨ p4)) ∧ p4) ∧ p1)) ∧ (p3 → p3))) → p4) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- We need to get the left conjuct of h3 based on <expert-advice>.
  let h4 := h3.left
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_209251387940325594324828669717 : ((p5 ∨ (False ∧ ((False ∧ p2) → p5))) → ((p3 → (((p3 → False) → (p2 ∧ (False ∧ ((p2 ∨ (p4 → (p2 ∨ False))) ∨ False)))) ∧ p5)) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h5 : p3 := by
      -- One of the premise coincides with the conclusion.
      exact h3
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h6 := h4 h5
    -- False on the left can always be used.
    apply False.elim h6
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h7 : p3 := by
      -- One of the premise coincides with the conclusion.
      exact h3
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h8 := h4 h7
    -- False on the left can always be used.
    apply False.elim h8
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h9 : p3 := by
      -- One of the premise coincides with the conclusion.
      exact h3
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h10 := h4 h9
    -- False on the left can always be used.
    apply False.elim h10
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- False on the left can always be used.
    apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40537127319326605154192792044 : ((((p3 ∨ ((p2 ∨ ((p2 → p2) → (p4 ∨ ((p5 ∨ p4) → ((((p5 ∧ p3) → p5) ∨ False) → p4))))) ∧ (p3 → p4))) ∨ True) ∨ False) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_194283340754021215888933781846 : ((p5 → (True ∨ (p2 ∧ ((p3 ∨ (p3 ∧ p4)) ∧ p1)))) → (((p5 ∧ ((p4 ∧ (True → p3)) ∧ p2)) → p1) ∨ (p3 → (p3 → (p3 ∨ p1))))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66464335547671553489376459451 : ((True → ((False ∨ ((((p1 ∨ p3) ∨ p5) ∨ p1) ∨ ((p5 ∧ (p2 ∨ ((True ∨ (p5 ∨ (False ∧ p5))) ∨ True))) ∧ (True → True)))) ∧ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_733666889719137536613769877244 : ((((p5 ∧ False) ∧ ((((p1 → p4) ∨ (p3 ∧ True)) → ((False → False) ∨ (p2 ∧ (((True → False) → p1) ∨ (p2 ∨ (False ∨ p5)))))) → p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59785081148645722837140165603 : (((p2 ∧ p1) → ((((p4 ∨ (False ∨ False)) → ((False ∨ p3) ∧ (p5 → p3))) ∧ ((False ∨ False) ∨ p4)) ∨ ((p4 → p1) ∨ (p3 ∨ False)))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h4
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135855562616719072585618856871 : ((((((True → ((p3 ∧ False) ∧ (p5 ∨ p4))) ∧ p1) ∧ p2) ∨ True) ∨ ((False → ((p3 → p3) ∧ True)) ∨ (p1 ∨ False))) ∨ ((p1 ∨ p1) → True)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_670506054721008116053246766977 : (((((p1 → p2) ∧ ((p3 → (p2 ∧ (False ∧ (p4 → False)))) ∨ (p2 ∨ (False ∧ (p5 → (p3 → (False ∨ p1))))))) ∨ ((True ∨ False) ∨ p3)) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39994760550188935947265650449 : (((p5 → ((((((False → p3) ∨ (p1 ∨ (p5 ∧ (True → p1)))) → (True → False)) → p1) ∧ (p4 ∧ (p1 → False))) ∨ (p3 ∧ p2))) ∧ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65529193682885663918701509331 : ((p3 ∨ (p3 ∨ (False ∧ (((p5 → True) ∨ (((p3 ∧ (True → True)) ∨ ((True ∧ ((p1 ∨ (False → p1)) ∧ True)) → p3)) ∨ True)) → p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135457296414532251407985417451 : ((((((p5 ∨ p1) ∨ (p3 ∧ ((p4 → True) ∨ (p2 ∨ (p1 ∧ True))))) ∧ (p1 ∧ p1)) → p1) → (p1 ∨ (p3 → False))) ∨ ((False → p1) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345693962788633731812935765671 : (p3 → ((p5 ∨ ((p2 ∧ ((p2 → ((p5 ∧ (p5 ∨ p4)) → (p1 ∨ (True → p2)))) ∨ (False ∨ (p1 ∨ p1)))) → (False ∨ (p4 → False)))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53296180720390068771035071718 : (((p2 ∨ (((p2 → False) → ((p5 ∨ p1) ∧ (p2 ∧ p4))) ∧ p1)) ∨ ((False ∨ (((p1 → p1) ∧ p2) → (p2 ∨ p3))) ∨ (p5 ∧ p2))) ∨ False) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_140415773467580921410163812885 : ((((((True ∨ p5) ∧ ((False → ((p1 → (p3 → (False → p3))) → True)) ∨ p5)) ∨ p2) → True) → ((p3 ∧ p2) ∨ p2)) → (p4 ∨ (p1 ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((((True ∨ p5) ∧ ((False → ((p1 → (p3 → (False → p3))) → True)) ∨ p5)) ∨ p2) → True) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_330943871584134988650480826656 : (True → (p4 → (p4 ∧ ((((p1 ∨ (p3 → True)) ∨ p5) ∧ (p1 ∨ ((((p4 → True) ∧ p1) ∧ p1) ∧ (p2 → (p3 ∨ (p4 ∨ p4)))))) ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_4025198467571021933247252360 : (p2 ∨ (((p1 → (p3 ∧ (True ∨ ((p4 → p2) → p2)))) → ((p3 ∧ ((p2 ∧ False) ∨ ((p3 → (False ∧ p1)) ∧ p5))) ∨ True)) ∨ p1)) := by
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
theorem thm_5_vars_344349381263524319833942933603 : (p2 → (p4 ∨ (((p5 ∨ p1) ∨ ((((p4 → p3) ∨ p4) ∨ ((p2 → (p4 ∨ p1)) ∧ p5)) ∧ (p4 ∧ ((True ∨ p3) ∧ (p5 ∨ p1))))) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_318887959985733228660143541709 : (p4 ∨ (((p1 ∧ True) ∨ ((False ∧ (p2 ∧ p5)) ∨ ((p4 ∨ p5) ∧ ((p4 → (((p4 ∧ p2) ∧ False) ∨ p1)) → p5)))) ∨ ((p5 ∧ p5) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215385130686978193494229521127 : ((p2 ∧ (False ∧ (p4 → False))) ∨ ((p5 → p2) ∨ (((p5 → ((True ∨ p2) ∧ ((p4 ∨ (p3 ∨ p4)) ∧ True))) → p5) ∨ ((p2 ∧ p2) → p2)))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324117516164597332121201377544 : (p5 ∨ (((p3 → False) → ((((p4 ∨ p3) ∧ (p4 ∨ p2)) → p5) ∧ p3)) → ((((p3 ∧ False) → p4) → p1) ∨ (True ∨ ((False → p5) ∧ p3))))) := by
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
theorem thm_5_vars_637882049265106530693942607516 : ((((((p5 → (p4 ∧ p3)) ∨ (p2 → (p1 ∧ p1))) ∧ ((((((p5 ∧ p1) ∧ p5) → p4) ∨ (p2 ∨ p4)) ∨ (p3 → p1)) ∨ p1)) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



