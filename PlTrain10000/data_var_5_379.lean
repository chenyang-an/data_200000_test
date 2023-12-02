variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178003364546161303295391034323 : (((p2 ∨ (p3 ∧ ((((p3 → (p3 → p1)) ∨ True) → p3) ∧ True))) ∨ p4) ∨ (((((p3 ∧ (True ∨ False)) ∨ p1) → p2) → True) ∨ (p1 ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149896156209733466562233881310 : ((p2 ∨ (p5 ∧ ((p3 → ((p4 ∨ True) → (True → p3))) ∧ (p4 → (True ∧ ((p1 ∨ p4) → (p2 ∨ p5))))))) ∨ ((False ∧ (p1 ∨ p5)) → p3)) := by
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
theorem thm_5_vars_219504374330948448306582472343 : ((p5 ∨ ((True ∧ p2) → p5)) → (((False ∧ (((p2 → p2) ∨ p4) → (p2 ∨ ((p3 ∨ True) ∧ False)))) ∨ (((False ∧ True) → p2) ∧ True)) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- False on the left can always be used.
    apply False.elim h4
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h7
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- False on the left can always be used.
    apply False.elim h8
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52279641029439089139269745664 : (((p2 → (p2 → ((p3 → (p3 ∧ p2)) ∨ (((p2 ∧ False) ∨ (False ∨ p4)) ∨ False)))) → ((True → (False ∧ True)) → (p1 ∧ (p4 ∨ p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59328038246021665131308079790 : (((p4 ∨ p4) ∨ ((((((p4 → False) ∨ False) → p2) ∧ (False → p4)) ∧ (False ∨ ((p5 → (p2 ∨ False)) → (p1 ∧ (False ∨ p2))))) ∨ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41517873706202218516689134353 : ((((((p5 ∧ (False ∧ (True → False))) ∨ p1) → (p2 → p3)) ∧ (((True ∧ p1) ∧ False) ∨ ((p5 ∧ p2) ∨ ((False ∧ False) ∨ False)))) ∨ True) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_87816120319947100857430116996 : ((((False ∨ (p1 ∧ (False ∧ False))) → p2) → ((((False ∨ p3) ∧ p5) ∧ ((p2 ∨ False) → ((((p3 ∧ p5) ∧ False) → True) ∨ True))) ∧ False)) → p1) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((False ∨ (p1 ∧ (False ∧ False))) → p2) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- False on the left can always be used.
      apply False.elim h4
    case inr h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- False on the left can always be used.
      apply False.elim h8
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h10 := h1 h2
  -- We need to get the right conjuct of h10 based on <expert-advice>.
  let h11 := h10.right
  -- False on the left can always be used.
  apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135430697701452932948838068971 : (((p3 ∨ ((p5 ∨ ((p4 ∨ (p5 ∨ ((p4 → p1) ∧ p5))) ∨ (p4 → p3))) → (p3 ∨ True))) ∨ (p3 ∧ (p3 ∧ False))) ∨ (p5 → (p1 ∧ p3))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h5 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h6 =>
        -- Disjunctions on the left can always be decomposed.
        cases h6
        case inl h7 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h8 =>
          -- Conjunctions on the left can always be decomposed.
          let h9 := h8.left
          let h10 := h8.right
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
theorem thm_5_vars_127139593439170065165990633442 : ((p1 ∨ (((p4 → (p1 ∧ (p3 ∨ p2))) ∧ (p3 ∧ (((((True → p5) → p2) → p4) ∨ p2) ∧ ((p4 ∧ True) ∧ p4)))) ∧ p3)) → (p5 ∨ p1)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h11.left
      let h14 := h11.right
      -- Conjunctions on the left can always be decomposed.
      let h15 := h13.left
      let h16 := h13.right
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h17 : p4 := by
        -- One of the premise coincides with the conclusion.
        exact h14
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h18 := h6 h17
      -- We need to get the left conjuct of h18 based on <expert-advice>.
      let h19 := h18.left
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h19
    case inr h20 =>
      -- Conjunctions on the left can always be decomposed.
      let h21 := h11.left
      let h22 := h11.right
      -- Conjunctions on the left can always be decomposed.
      let h23 := h21.left
      let h24 := h21.right
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h25 : p4 := by
        -- One of the premise coincides with the conclusion.
        exact h22
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h26 := h6 h25
      -- We need to get the left conjuct of h26 based on <expert-advice>.
      let h27 := h26.left
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h27



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_765810537261949089976032712745 : (((p4 ∧ (((p2 → False) ∧ ((False → p2) → (p4 ∧ p2))) → (((((((p2 ∧ p5) ∨ True) → p4) ∧ True) ∧ (True ∧ True)) → p5) ∧ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314692626777639702064737305274 : (p3 ∨ (((True ∨ p3) → ((p1 ∧ True) ∧ (p4 ∨ (p2 ∨ (((p4 ∧ True) ∨ p1) ∨ p5))))) → (((p4 ∨ (p2 → (False ∧ True))) ∧ p4) ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (True ∨ p3) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the left conjuct of h3 based on <expert-advice>.
  let h4 := h3.left
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_707619682103194151469935173452 : (((((False → p5) ∧ (p1 ∧ (False ∨ (p2 ∧ True)))) ∨ ((p3 → (p3 ∨ ((p3 → (p3 → p1)) ∨ p3))) → ((p4 ∨ p1) ∨ (False ∧ False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137501443918708492835350193778 : ((p5 ∧ ((p3 ∨ (p3 → (p1 → ((((p2 ∨ p1) → False) → ((p4 → p3) ∧ (p2 ∨ False))) ∧ p4)))) → (p3 ∧ p3))) ∨ (True ∨ (p4 ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46680402082094408413898892269 : (((p2 ∨ ((p4 ∧ (((p2 ∧ (p4 → p2)) → ((p3 ∧ p3) ∧ (p1 ∨ (((p1 ∨ p4) ∨ p2) ∧ p2)))) ∨ False)) ∨ True)) ∧ (p5 ∧ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_175373833077963288566258906017 : ((True → ((((p1 ∨ (((p1 → p2) ∨ p2) ∨ p3)) ∧ p3) ∨ (False → False)) → False)) → ((((False ∨ p5) ∧ p2) ∨ (False ∧ p5)) ∧ (True ∧ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : (((p1 ∨ (((p1 → p2) ∨ p2) ∨ p3)) ∧ p3) ∨ (False → False)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- False on the left can always be used.
    apply False.elim h5
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h4
  -- False on the left can always be used.
  apply False.elim h6
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h7 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h8 := h1 h7
  -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
  have h9 : (((p1 ∨ (((p1 → p2) ∨ p2) ∨ p3)) ∧ p3) ∨ (False → False)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h10
    -- False on the left can always be used.
    apply False.elim h10
  -- We have shown the premise of h8, we can now drive its conclusion.
  let h11 := h8 h9
  -- False on the left can always be used.
  apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64987041627305721397790193213 : ((p2 ∨ (((True → False) ∧ p4) ∧ ((p4 ∨ (p2 ∨ p3)) ∨ ((p3 ∧ ((p3 → p4) ∨ ((p1 → False) ∧ ((p5 → p4) ∧ p1)))) ∧ p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_443965783865437498892736414794 : (((((p5 ∨ p5) ∧ (((p3 ∨ (p1 ∨ p3)) ∧ (p2 ∧ ((True ∧ (p4 ∧ p3)) ∧ (p2 ∨ (p5 → p5))))) ∧ False)) ∨ (True ∨ (False ∨ p4))) ∧ True) ∧ True) := by
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
theorem thm_5_vars_587817500261482169120183514542 : ((((((((p1 ∨ True) ∨ ((True ∨ ((False ∧ (((p3 → p1) ∨ p5) → (p2 → p3))) ∧ p5)) → True)) → p5) ∨ (p1 ∨ True)) ∨ False) ∧ True) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_151683400979528190239709648055 : (((True → (p2 ∧ (p1 ∨ (((((p4 ∨ True) ∧ p5) → p5) ∨ (p4 ∨ p5)) → p2)))) ∧ (True ∧ (True ∧ p5))) → (((p5 → p4) ∨ p1) ∨ p5)) := by
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
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65128811761682971392781782611 : ((p2 ∨ (p1 → (((((False → ((p4 → p5) ∧ (True ∨ (True → (p1 → p2))))) → p4) ∨ p4) → (((p5 ∨ True) ∨ p5) → p3)) ∨ True))) ∨ p1) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65040441502704306989581719390 : ((p2 ∨ (True ∧ (((True → (((p3 ∧ True) → ((False ∧ p3) → p1)) ∨ ((p3 → p2) ∧ False))) → p5) ∨ ((p4 ∧ p2) → (p1 ∧ p5))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164489275681028936460409940261 : (((((p4 ∨ (((True ∧ (p2 ∧ p5)) → ((p1 ∧ p1) ∧ p5)) ∧ p3)) ∨ p3) → p4) ∧ True) ∨ ((((True ∨ p2) ∧ (p4 ∧ p5)) ∧ p1) → p5)) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h5.left
    let h11 := h5.right
    -- One of the premise coincides with the conclusion.
    exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_339758683250238008917482472304 : (p1 → (p4 ∨ ((True → p4) ∨ (((((p3 ∨ ((p1 ∧ p2) ∧ (p3 ∧ (p4 → p4)))) ∧ p5) ∨ (p5 → p1)) ∧ p5) ∨ (True ∨ (p5 ∨ True)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_14521035524573304251659663893 : (((((p1 ∧ (((p4 → p2) ∧ ((p5 ∨ True) ∧ (p5 ∧ (p3 ∨ p1)))) ∨ (True → (True ∨ (p4 ∧ p5))))) ∧ False) ∨ True) ∨ (p1 ∨ p4)) ∧ True) := by
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
theorem thm_5_vars_20335060997188677865530145748 : (((p1 → ((p2 ∧ p4) → (((True ∧ False) → (p3 ∨ True)) → (False ∧ p2)))) ∨ (p3 ∨ (p3 → (p2 ∨ (p3 → (p4 ∨ (p1 → True))))))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159316168181815497103326538285 : ((p5 → (((p2 ∨ (False → ((p1 ∧ True) ∧ (False ∨ p2)))) → (False ∧ True)) ∨ (False ∧ (True ∧ p5)))) ∨ ((p3 ∨ p2) → (p2 ∨ (p3 ∨ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_731010784636508739269912808033 : ((((False ∨ (p5 ∨ p1)) → (((p3 → (p5 → p3)) ∧ (p2 ∨ (True → (((p4 ∨ (p3 ∨ True)) → (False ∨ (p2 → p2))) ∨ False)))) ∨ p3)) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h5
      -- Implications on the right can always be decomposed.
      intro h6
      -- One of the premise coincides with the conclusion.
      exact h5
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h7
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h8
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h10
        -- One of the premise coincides with the conclusion.
        exact h10
      case inr h11 =>
        -- Disjunctions on the left can always be decomposed.
        cases h11
        case inl h12 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h13
          -- One of the premise coincides with the conclusion.
          exact h13
        case inr h14 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h15
          -- One of the premise coincides with the conclusion.
          exact h15
    case inr h16 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h17
      -- Implications on the right can always be decomposed.
      intro h18
      -- One of the premise coincides with the conclusion.
      exact h17
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h19
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h20
      -- Disjunctions on the left can always be decomposed.
      cases h20
      case inl h21 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h22
        -- One of the premise coincides with the conclusion.
        exact h22
      case inr h23 =>
        -- Disjunctions on the left can always be decomposed.
        cases h23
        case inl h24 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h25
          -- One of the premise coincides with the conclusion.
          exact h25
        case inr h26 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h27
          -- One of the premise coincides with the conclusion.
          exact h27
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48973684355288181065385031874 : ((((((p2 → ((p2 ∧ (p3 → p3)) ∨ (False ∧ p2))) ∧ (p3 ∨ ((True → p2) ∧ p2))) ∨ (True ∧ p5)) ∨ p3) ∨ (p4 ∧ (p5 ∧ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_736993623965285412418875993685 : ((((p3 → False) ∧ (p1 ∧ (p1 ∨ ((p1 ∨ p5) ∧ ((((p3 → ((p5 → ((False → p1) ∧ (p1 → p5))) → p5)) → p5) → True) ∨ p1))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134596716880064545370487850392 : ((((((p2 ∧ p2) ∨ (True → ((p3 ∨ p4) → ((p1 → False) ∧ False)))) → ((p3 ∨ False) ∧ p2)) → (p5 ∨ p1)) → p4) ∨ ((p1 ∧ p2) → p2)) := by
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
theorem thm_5_vars_316518594967954896170134865017 : (p3 ∨ (p2 ∨ (((p3 ∧ p1) ∨ p1) → (((((((False → p5) → False) ∨ False) ∧ p5) ∨ ((p2 ∧ True) → p2)) → False) → ((p2 ∧ p1) ∧ p3))))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h6 : (((((False → p5) → False) ∨ False) ∧ p5) ∨ ((p2 ∧ True) → p2)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h7
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- One of the premise coincides with the conclusion.
      exact h8
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h10 := h2 h6
    -- False on the left can always be used.
    apply False.elim h10
  case inr h11 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h12 : (((((False → p5) → False) ∨ False) ∧ p5) ∨ ((p2 ∧ True) → p2)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h13
      -- Conjunctions on the left can always be decomposed.
      let h14 := h13.left
      let h15 := h13.right
      -- One of the premise coincides with the conclusion.
      exact h14
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h16 := h2 h12
    -- False on the left can always be used.
    apply False.elim h16
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h17 =>
    -- Conjunctions on the left can always be decomposed.
    let h18 := h17.left
    let h19 := h17.right
    -- One of the premise coincides with the conclusion.
    exact h19
  case inr h20 =>
    -- One of the premise coincides with the conclusion.
    exact h20
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h21 =>
    -- Conjunctions on the left can always be decomposed.
    let h22 := h21.left
    let h23 := h21.right
    -- One of the premise coincides with the conclusion.
    exact h22
  case inr h24 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h25 : (((((False → p5) → False) ∨ False) ∧ p5) ∨ ((p2 ∧ True) → p2)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h26
      -- Conjunctions on the left can always be decomposed.
      let h27 := h26.left
      let h28 := h26.right
      -- One of the premise coincides with the conclusion.
      exact h27
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h29 := h2 h25
    -- False on the left can always be used.
    apply False.elim h29



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_689423585364384292549347691100 : ((((((((p2 ∧ p3) → p2) ∧ (p1 ∧ (p5 ∧ False))) → p4) ∧ ((p1 ∧ True) ∨ p5)) ∨ ((p4 → ((False ∧ p1) ∧ (p3 → True))) → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149591444439520796777954950415 : ((p3 ∧ ((p2 → (((p2 ∧ ((p5 → (p3 ∨ (p5 ∨ (p4 → p1)))) ∨ True)) → p3) ∨ (p1 ∨ p4))) → p3)) ∨ (True → ((False → p4) ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158340236155497063480615343975 : (((p2 ∧ p4) ∧ ((p4 → (True ∧ p1)) ∨ (((p5 → p2) ∨ p5) ∧ (((p4 ∧ True) ∧ True) ∨ p1)))) ∨ (True ∨ (p3 ∨ ((p4 ∨ p5) ∧ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233193654716919909382630094831 : ((p5 ∧ (p5 ∨ p1)) → ((p5 → (p4 ∧ (((p2 ∨ ((p3 → p2) → True)) ∧ p5) → p4))) → (((p2 → (p2 → (p3 ∨ p4))) → p2) → p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h7 : (p2 → (p2 → (p3 ∨ p4))) := by
      -- Implications on the right can always be decomposed.
      intro h8
      -- Implications on the right can always be decomposed.
      intro h9
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h10 : p5 := by
        -- One of the premise coincides with the conclusion.
        exact h6
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h11 := h2 h10
      -- We need to get the left conjuct of h11 based on <expert-advice>.
      let h12 := h11.left
      -- One of the premise coincides with the conclusion.
      exact h12
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h13 := h3 h7
    -- One of the premise coincides with the conclusion.
    exact h13
  case inr h14 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h15 : (p2 → (p2 → (p3 ∨ p4))) := by
      -- Implications on the right can always be decomposed.
      intro h16
      -- Implications on the right can always be decomposed.
      intro h17
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h18 : p5 := by
        -- One of the premise coincides with the conclusion.
        exact h4
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h19 := h2 h18
      -- We need to get the left conjuct of h19 based on <expert-advice>.
      let h20 := h19.left
      -- One of the premise coincides with the conclusion.
      exact h20
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h21 := h3 h15
    -- One of the premise coincides with the conclusion.
    exact h21



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_615961929647724475129896583134 : ((((((p1 ∨ ((True ∧ (p1 ∧ (p4 ∧ p5))) → (False ∨ (p5 ∨ True)))) ∨ p4) → ((((False ∨ p3) ∨ p3) → (p2 ∨ p1)) → p2)) ∨ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46302319636286534977727648938 : (((((p4 → (p2 ∨ p5)) ∧ (((((p5 ∧ (False ∧ p2)) ∨ p3) ∨ (p3 ∨ p3)) ∨ False) ∧ p1)) → ((False → False) → p2)) ∧ (True → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_229942183851345120890735273436 : (((True ∧ p1) ∧ True) → (p2 ∨ ((((p5 ∨ p1) ∨ (p2 → p3)) → (p1 → (False ∧ True))) ∨ ((p5 ∧ (p5 ∧ p1)) → (p1 → (p4 ∨ p1)))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h6
  -- Implications on the right can always be decomposed.
  intro h7
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- Conjunctions on the left can always be decomposed.
  let h10 := h9.left
  let h11 := h9.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_805395746340969590772812965832 : (((p3 → (p1 ∨ (((((((p2 ∧ p3) ∨ True) ∨ p4) → ((p3 ∨ p3) ∧ p1)) ∨ p2) ∨ ((p1 ∧ p2) → (p4 ∨ (p1 → p2)))) ∨ p4))) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h5
  -- One of the premise coincides with the conclusion.
  exact h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150459857300368327333573398657 : ((((p5 ∧ ((p5 ∧ p5) ∨ ((p4 ∨ (False → (p4 → p2))) ∧ (p4 ∨ (p3 ∧ (p5 → p1)))))) → p3) ∧ p3) → ((p1 → p4) ∨ (False ∨ True))) := by
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
theorem thm_5_vars_750510139395214145015936049826 : (((True ∧ ((p2 → ((((((p1 → True) ∧ p2) ∧ ((p1 → False) → p3)) ∨ False) ∨ True) → (p1 → (p1 → p5)))) → ((p2 → p3) → p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259007483551033379865293332732 : ((True → p4) → (((((p1 → ((p2 → True) ∧ (p3 ∧ p5))) ∧ ((p2 ∧ (p5 ∨ True)) ∧ True)) ∧ p3) ∨ ((p2 ∨ True) ∧ (True → True))) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68749095087639072030196893708 : ((p4 → ((((True → p5) ∨ (False ∨ (p1 → (p5 → p1)))) ∨ ((p1 ∨ p1) → (p1 → True))) → (p3 ∨ ((False ∨ p4) ∧ (False → p1))))) ∨ p2) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1
      -- Implications on the right can always be decomposed.
      intro h5
      -- False on the left can always be used.
      apply False.elim h5
    case inr h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- False on the left can always be used.
        apply False.elim h7
      case inr h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h1
        -- Implications on the right can always be decomposed.
        intro h9
        -- False on the left can always be used.
        apply False.elim h9
  case inr h10 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
    -- Implications on the right can always be decomposed.
    intro h11
    -- False on the left can always be used.
    apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166793718852901134449063568075 : ((p5 → (p2 → ((p4 ∨ (p3 ∧ (True → p1))) → (p3 ∧ (False ∨ ((p4 ∨ p4) → p4)))))) ∨ ((p3 ∧ (p3 ∨ p1)) → (p2 ∨ (True ∨ p3)))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_656565614380721325440954702461 : (((((False → ((p5 → (p5 → False)) → (p5 → p2))) ∧ (((p4 ∧ (p5 → (p3 ∨ p4))) ∨ (p4 ∧ True)) ∨ (False ∧ False))) ∨ (p4 → p4)) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_619887630216550735781824111757 : (((((p5 ∨ p2) ∧ (p1 ∨ (p4 ∧ ((((True ∨ (True ∨ (((((p1 ∧ False) ∧ False) ∨ p4) → p4) → p5))) → False) ∧ False) ∧ False)))) ∨ True) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_231656856076250040837611775546 : (((False ∧ p5) → True) → ((True → ((True → p1) ∧ (((True → p2) ∨ p2) ∨ (p5 ∧ ((True ∧ (False ∨ False)) ∨ True))))) ∨ (p3 → (False → p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67698365974807192140347288684 : ((p1 → (p4 → ((((p1 ∧ ((p5 → (False → p1)) ∨ True)) → p2) ∧ p4) ∨ ((((p2 → False) ∨ (p5 → False)) ∧ (p4 ∧ True)) ∨ p4)))) ∨ p2) := by
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
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_326280094182528612382793323962 : (p5 ∨ (p4 → ((((((False → ((p5 → p2) ∧ (p1 ∧ p2))) ∨ (False ∧ p5)) → True) → (((False ∨ p5) ∧ p3) ∧ p5)) ∧ (False ∨ p2)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62613309159193913610183983555 : ((p4 ∧ ((((((True ∨ p1) ∨ ((p1 → (p3 → False)) ∧ (p4 → ((p3 ∨ (True ∨ p1)) ∨ (p2 → p5))))) → p1) ∨ True) → p5) ∧ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_809973804684788340026661165928 : (((p5 → ((p3 ∧ ((((((True ∧ True) ∨ p1) → (p1 ∧ True)) ∨ (p4 ∨ p4)) ∧ (p3 ∧ (p4 → p5))) → False)) ∨ (p5 ∧ (p5 ∧ p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115785871835587751956463141081 : ((((p3 ∨ (p5 ∨ False)) ∧ p1) ∧ (p5 ∨ ((((((True → ((True → p1) → p2)) ∧ True) ∧ p2) ∧ (p5 ∧ p3)) → p4) ∧ True))) ∨ (True ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_355711844561380839267877640513 : (p5 → (((((p2 ∨ p5) ∧ p3) ∧ True) ∨ ((p1 ∨ p2) ∨ ((((p1 ∧ p1) ∨ (p4 → (p3 ∧ True))) ∨ p1) ∧ (False ∨ p1)))) → (p2 ∨ True))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h13 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h13
    case inr h14 =>
      -- Conjunctions on the left can always be decomposed.
      let h15 := h14.left
      let h16 := h14.right
      -- Disjunctions on the left can always be decomposed.
      cases h15
      case inl h17 =>
        -- Disjunctions on the left can always be decomposed.
        cases h17
        case inl h18 =>
          -- Conjunctions on the left can always be decomposed.
          let h19 := h18.left
          let h20 := h18.right
          -- Disjunctions on the left can always be decomposed.
          cases h16
          case inl h21 =>
            -- False on the left can always be used.
            apply False.elim h21
          case inr h22 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
        case inr h23 =>
          -- Disjunctions on the left can always be decomposed.
          cases h16
          case inl h24 =>
            -- False on the left can always be used.
            apply False.elim h24
          case inr h25 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
      case inr h26 =>
        -- Disjunctions on the left can always be decomposed.
        cases h16
        case inl h27 =>
          -- False on the left can always be used.
          apply False.elim h27
        case inr h28 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_11523240633937960321009514612 : ((((p4 ∧ (((((True → ((p1 ∨ p5) ∧ p1)) → False) ∧ (p5 ∧ (p5 → (p3 ∧ (p2 ∧ p4))))) ∧ p1) ∧ p3)) ∧ (p3 → p3)) → p2) ∧ True) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- Conjunctions on the left can always be decomposed.
  let h10 := h8.left
  let h11 := h8.right
  -- Conjunctions on the left can always be decomposed.
  let h12 := h11.left
  let h13 := h11.right
  -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
  have h14 : p5 := by
    -- One of the premise coincides with the conclusion.
    exact h12
  -- We have shown the premise of h13, we can now drive its conclusion.
  let h15 := h13 h14
  -- We need to get the right conjuct of h15 based on <expert-advice>.
  let h16 := h15.right
  -- We need to get the left conjuct of h16 based on <expert-advice>.
  let h17 := h16.left
  -- One of the premise coincides with the conclusion.
  exact h17
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49338328531305653333345416640 : (((True → ((((p2 → p4) ∧ (p4 ∧ (False ∨ p3))) → False) → ((p2 ∧ (((False ∧ p1) ∧ p5) ∨ p1)) ∧ False))) ∨ ((False → p2) ∨ p1)) ∨ p4) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342472429359593981116859347721 : (p2 → (((((True → (p4 ∨ (p2 ∨ p1))) ∨ p4) → (False ∧ (False ∧ p3))) ∧ True) ∨ (((p5 → ((p5 ∨ p2) → False)) ∧ (p5 ∧ True)) → p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h7 : p5 := by
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h8 := h3 h7
  -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
  have h9 : (p5 ∨ p2) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h8, we can now drive its conclusion.
  let h10 := h8 h9
  -- False on the left can always be used.
  apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_791053530387080183543661345508 : (((True → ((((p3 ∨ p1) → ((False ∨ (p1 → (((p2 → (p5 ∨ (p2 → p4))) → (True ∧ (p5 ∧ p5))) → p3))) ∨ p4)) → p3) ∧ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308514338610468283825271651954 : (p2 ∨ ((((p2 → ((True → p3) ∨ ((((False → p2) → (True ∨ False)) ∨ p3) → p1))) ∧ p1) ∨ ((p1 ∧ (False ∧ (p4 ∧ p4))) ∨ True)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308547123327305062511952251643 : (p2 ∨ ((((((p4 ∨ p4) ∧ p2) ∨ False) ∨ ((p2 ∧ p2) ∧ True)) → (((p5 ∨ p3) ∧ False) ∨ (((p2 ∨ (p1 ∨ True)) ∧ False) → p2))) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
      -- Conjunctions on the left can always be decomposed.
      let h4 := h3.left
      let h5 := h3.right
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h6 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h7
        -- Conjunctions on the left can always be decomposed.
        let h8 := h7.left
        let h9 := h7.right
        -- Disjunctions on the left can always be decomposed.
        cases h8
        case inl h10 =>
          -- False on the left can always be used.
          apply False.elim h9
        case inr h11 =>
          -- Disjunctions on the left can always be decomposed.
          cases h11
          case inl h12 =>
            -- False on the left can always be used.
            apply False.elim h9
          case inr h13 =>
            -- False on the left can always be used.
            apply False.elim h9
      case inr h14 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h15
        -- Conjunctions on the left can always be decomposed.
        let h16 := h15.left
        let h17 := h15.right
        -- Disjunctions on the left can always be decomposed.
        cases h16
        case inl h18 =>
          -- False on the left can always be used.
          apply False.elim h17
        case inr h19 =>
          -- Disjunctions on the left can always be decomposed.
          cases h19
          case inl h20 =>
            -- False on the left can always be used.
            apply False.elim h17
          case inr h21 =>
            -- False on the left can always be used.
            apply False.elim h17
    case inr h22 =>
      -- False on the left can always be used.
      apply False.elim h22
  case inr h23 =>
    -- Conjunctions on the left can always be decomposed.
    let h24 := h23.left
    let h25 := h23.right
    -- Conjunctions on the left can always be decomposed.
    let h26 := h24.left
    let h27 := h24.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h28
    -- Conjunctions on the left can always be decomposed.
    let h29 := h28.left
    let h30 := h28.right
    -- Disjunctions on the left can always be decomposed.
    cases h29
    case inl h31 =>
      -- False on the left can always be used.
      apply False.elim h30
    case inr h32 =>
      -- Disjunctions on the left can always be decomposed.
      cases h32
      case inl h33 =>
        -- False on the left can always be used.
        apply False.elim h30
      case inr h34 =>
        -- False on the left can always be used.
        apply False.elim h30



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51220183478706241171791717252 : (((((False ∨ True) → ((p3 ∨ p3) ∨ p1)) ∨ (((p2 ∨ (p5 → (p5 ∧ False))) → True) → False)) ∨ (True → (((True → p4) → p2) ∨ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_608234122305110808261250356994 : (((((((((True ∧ True) ∧ p5) ∨ ((True → p2) → (((p2 ∧ ((p4 → False) ∨ (p5 → p1))) ∧ p3) ∨ p2))) ∧ False) ∨ p1) ∨ False) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185971232800540445480644181672 : (((p2 ∧ (True → (False ∧ ((False ∧ p3) → (p1 ∧ p1))))) ∧ p5) → ((p4 ∧ (False ∨ ((p3 → (p2 ∨ p3)) ∧ ((False ∨ p3) ∨ False)))) ∨ p2)) := by
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
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_143873981719240923458380708862 : (((((p2 → True) → (True ∨ (True → (((True ∨ p3) ∨ ((p1 ∧ p3) ∨ p2)) ∨ p2)))) → (True → p2)) ∨ True) ∧ ((True → (p2 → True)) ∨ p1)) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_738561966163370289802564879281 : ((((p1 ∧ p5) ∨ (((p4 ∨ p4) → False) ∧ ((((((True ∨ (p5 → False)) ∧ (p5 ∧ p3)) → (p3 → (p3 → p2))) ∨ p3) → False) ∧ True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198740265653174711414517964710 : ((True → (((p4 ∨ p1) ∨ (p1 → p4)) ∧ False)) ∨ (((((p1 ∨ p3) ∨ False) → ((((p1 → (p2 ∨ p3)) → p1) ∨ True) → p3)) → p2) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248339319671063678529332157911 : ((p2 ∨ p3) ∨ (((((((p5 ∧ (p4 → p2)) → p1) ∨ False) ∨ (p3 → p1)) ∨ p1) ∨ p5) ∨ (p4 → ((((p4 ∧ p1) → p5) ∨ False) → p4)))) := by
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
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h4 =>
    -- False on the left can always be used.
    apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_352916740069765973596084259996 : (p4 → (True ∧ (p4 → (((p4 ∨ (p3 ∨ ((p1 ∧ ((p5 ∧ True) ∨ (p3 → p1))) ∧ p4))) ∨ p1) → (((p4 ∧ p2) → False) ∨ (p4 ∨ p3)))))) := by
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
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h1
      case inr h8 =>
        -- Conjunctions on the left can always be decomposed.
        let h9 := h8.left
        let h10 := h8.right
        -- Conjunctions on the left can always be decomposed.
        let h11 := h9.left
        let h12 := h9.right
        -- Disjunctions on the left can always be decomposed.
        cases h12
        case inl h13 =>
          -- Conjunctions on the left can always be decomposed.
          let h14 := h13.left
          let h15 := h13.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h1
        case inr h16 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h1
  case inr h17 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115181797876295155456800730654 : (((((((p1 ∨ True) ∨ p4) ∨ False) ∧ False) ∨ (p1 → p4)) ∧ (((p2 ∧ False) → False) ∧ (True → ((p1 → p4) ∧ (p2 → True))))) ∨ (p4 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_499308263874970575693356758251 : (((((p5 ∨ p4) ∧ False) ∨ (((p5 ∧ (((False → (((False ∨ (p1 → False)) ∨ False) → True)) → (p4 ∧ p4)) ∨ p1)) → (False ∧ p3)) ∨ True)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_804150066317749854311811555374 : (((p3 → ((((((p3 → p5) → p1) → p3) ∧ (p3 ∨ ((p2 ∨ p2) → p1))) ∧ (p3 ∧ (p4 ∧ p4))) → (p5 ∨ ((False → True) ∨ p2)))) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  cases h6
  case inl h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h4.left
    let h9 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h12
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h13 =>
    -- Conjunctions on the left can always be decomposed.
    let h14 := h4.left
    let h15 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h16 := h15.left
    let h17 := h15.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h18
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_713227634057679994408508903354 : ((((p2 ∨ (p3 ∨ (False ∨ (False ∧ False)))) ∨ ((((((p3 ∨ p1) ∨ p3) → (False ∧ p5)) ∧ p5) → (p3 → p3)) ∨ (True → (p2 → p4)))) ∨ p5) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354601701042416579291938826684 : (p5 → (((((p1 ∨ ((((False ∨ p2) → p2) ∨ (p4 ∧ p4)) ∨ ((p5 → p2) → ((p2 ∨ p1) → (p5 ∨ p3))))) → p1) ∨ p4) ∨ p5) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42422013082992848151121759250 : (((p5 ∧ ((((p1 → p1) → ((True → (p5 ∨ True)) → p5)) ∧ ((p2 ∧ (True → p2)) ∧ (True → True))) ∨ (True → (p1 ∧ False)))) ∨ True) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45476993420350889322244989460 : (((False ∨ ((((((p4 ∧ (p3 ∨ p4)) ∧ (p5 ∧ False)) ∧ ((p5 ∧ p2) ∨ False)) ∧ p2) ∨ (True → p5)) → ((p4 ∧ p3) ∧ p2))) → p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_646747487851328108801772061720 : ((((p2 → ((p3 ∨ (((p2 → ((p3 ∧ p1) → (p4 → (False ∧ True)))) ∧ (p2 ∨ p1)) ∨ (((p4 → p2) ∧ True) ∧ p1))) → p3)) → p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245188933384360857296267714530 : ((p2 ∧ False) ∨ ((p1 → (p5 ∧ (p1 ∨ p3))) ∨ ((p1 ∧ ((((p2 ∨ (p1 ∧ p2)) ∨ p5) ∨ (p2 → p2)) → ((False ∧ p5) ∧ p1))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114232783372911884711642020684 : (((p3 ∧ ((True ∧ (((p1 → (((p3 ∨ True) ∨ p4) ∧ (False → p3))) ∧ True) ∨ p4)) ∨ (p1 ∨ p4))) → ((p3 → p4) ∨ p3)) ∨ (p1 → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_183088772870479596714233005023 : (((p4 ∧ p3) → ((p1 ∧ (((True ∨ p5) ∧ p1) ∨ p3)) ∨ p4)) ∧ ((p2 ∨ (((p2 → p1) ∨ ((p2 ∨ (p3 ∧ p3)) ∨ p2)) ∧ True)) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_766919235085493630545109424552 : (((p4 ∧ (True → (((((p5 ∨ p1) ∨ (p5 ∧ (p2 ∧ p4))) ∧ (p5 ∨ ((True ∧ p5) → True))) ∨ p1) → (((p2 → False) ∧ p4) → p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_607331573117069079255995525374 : (((((((p4 → p3) ∨ True) → ((((p5 → (((p1 ∨ p1) → (p5 ∨ p3)) → False)) → p5) → p2) ∧ ((p4 ∧ p2) ∨ p1))) ∧ p3) ∨ True) ∨ False) ∧ True) := by
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
theorem thm_5_vars_103117745717569555011149062541 : (((((p3 ∨ p1) → p5) → (((((p3 ∧ False) ∨ (p5 ∨ ((True → p1) ∨ p5))) ∨ ((True → p1) ∧ p4)) ∨ True) ∨ p4)) ∨ True) ∧ (False → False)) := by
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
theorem thm_5_vars_247592137414644962058388770291 : ((False ∨ p5) ∨ ((False ∧ ((p2 ∨ p5) ∧ ((((p5 → p1) ∨ (((p2 → p3) ∨ p5) ∧ (p4 ∧ p2))) ∨ ((False → p5) ∨ True)) ∧ p1))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60429741871676831730019263740 : (((p4 → p4) → (((p4 → False) ∨ (((((p2 ∧ True) ∨ p1) ∨ ((p5 ∧ (p1 ∧ True)) → p1)) → (False ∨ False)) ∨ (p5 → p5))) ∧ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230242296755468255898383788878 : (((True ∨ p5) ∧ p2) → (((((True → True) → ((False ∨ p3) ∨ p4)) ∨ False) ∧ ((True → p1) → True)) → ((((False → True) ∨ True) → False) → False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
    -- Conjunctions on the left can always be decomposed.
    let h7 := h1.left
    let h8 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h9 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h10 : ((False → True) ∨ True) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h11 := h3 h10
      -- False on the left can always be used.
      apply False.elim h11
    case inr h12 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h13 : ((False → True) ∨ True) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h14 := h3 h13
      -- False on the left can always be used.
      apply False.elim h14
  case inr h15 =>
    -- False on the left can always be used.
    apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_731435436061690443015884615545 : ((((True → (p1 ∧ p5)) → ((p4 → (p2 ∧ (((p2 ∨ (False ∨ (True ∧ p4))) ∧ ((p3 → (p3 ∨ (p3 → p4))) → True)) ∧ p1))) → p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_182027163998588773323333085015 : (((((False ∨ p5) ∨ (p4 ∨ p5)) ∨ ((True ∧ False) ∨ True)) ∨ p5) ∧ (((((p4 → (p1 ∨ (p5 ∧ p4))) → p2) ∧ (p4 ∨ p4)) → p3) ∨ True)) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_730829264248236574478643166840 : ((((p5 ∧ (p4 ∧ p5)) → ((p5 → (((p1 ∧ ((p1 ∨ (p3 ∧ True)) ∨ p3)) ∨ ((p4 ∨ True) → (p4 ∨ True))) → (False ∨ False))) → p1)) ∨ p3) ∧ True) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h7 : p5 := by
    -- One of the premise coincides with the conclusion.
    exact h6
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h8 := h2 h7
  -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
  have h9 : ((p1 ∧ ((p1 ∨ (p3 ∧ True)) ∨ p3)) ∨ ((p4 ∨ True) → (p4 ∨ True))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h10
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h11
    case inr h12 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h5
  -- We have shown the premise of h8, we can now drive its conclusion.
  let h13 := h8 h9
  -- Disjunctions on the left can always be decomposed.
  cases h13
  case inl h14 =>
    -- False on the left can always be used.
    apply False.elim h14
  case inr h15 =>
    -- False on the left can always be used.
    apply False.elim h15
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136116247560159481824100982036 : (((p1 ∧ ((p5 → ((True → p2) → p2)) → p5)) ∨ (((p1 ∨ p1) → (False → p5)) ∧ ((p5 ∨ p3) ∨ (True ∨ False)))) ∨ (p2 → (p5 → p1))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_706972782283028815764976038644 : ((((((p2 → p1) ∧ ((p3 ∨ p4) ∧ p2)) ∨ p3) ∨ (p5 → (False ∨ ((p2 → (True ∧ p1)) ∨ (((False ∨ (p4 ∨ p5)) ∧ p2) → p2))))) ∨ p3) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h8 =>
      -- One of the premise coincides with the conclusion.
      exact h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_316924466536988011194979921886 : (p3 ∨ (p2 → (((((False ∨ ((p1 ∧ False) ∧ p2)) ∨ (p3 → p1)) ∧ p5) ∧ (p1 ∨ (p3 → (p4 ∧ (p1 ∧ (p1 ∨ p1)))))) ∨ (p5 ∨ p2)))) := by
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
theorem thm_5_vars_475874958847851640966917984242 : ((((((p2 ∧ (p3 → True)) ∨ ((p1 ∨ p3) ∨ p3)) ∨ p4) ∨ (p2 → (p1 ∨ ((False ∧ p3) → ((p5 → p4) → (p1 ∧ (p4 ∨ False))))))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- False on the left can always be used.
  apply False.elim h4
  -- Conjunctions on the left can always be decomposed.
  let h6 := h2.left
  let h7 := h2.right
  -- False on the left can always be used.
  apply False.elim h6
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259903358747196231388063414749 : ((p1 → p4) → (p4 ∨ ((((p3 ∧ False) ∨ p4) ∨ ((True → ((False → (p1 ∧ False)) ∧ ((True ∨ p2) → (p5 ∧ p3)))) ∧ (False → p1))) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_761308139296432117043985561545 : (((p3 ∧ ((((p4 ∨ (p3 → p2)) → ((p5 ∧ ((p4 → (False → (p1 ∨ ((True ∨ p2) ∨ True)))) ∧ p2)) ∧ p4)) ∧ (p2 ∨ True)) ∧ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49801005430273722369151203580 : (((True → ((p2 ∨ ((p5 → (False ∨ ((p3 ∧ True) → p1))) ∧ p3)) ∨ ((p3 ∨ (p3 ∧ p5)) → (p5 → True)))) → ((p1 ∧ True) → p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319378488940115465662513796164 : (p4 ∨ ((p2 ∧ (p3 ∨ (((p5 ∨ p5) → p3) → (((p1 ∧ False) → True) → False)))) ∨ ((False → (False ∨ ((p4 → (p4 ∧ p2)) ∨ p3))) ∨ p2))) := by
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
theorem thm_5_vars_249898571102311414363887983470 : ((True → p1) ∨ (((((p3 → ((False ∧ p1) ∨ p3)) ∧ p4) ∧ True) ∧ (((False → True) ∧ p5) ∨ (True → (p2 ∨ (p5 ∧ (p5 → p3)))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2650504471564164002821820570 : (((p4 → (p2 ∨ (p1 ∧ p3))) ∨ p3) ∨ (((((p1 → True) ∨ p4) ∨ p4) ∨ p3) ∧ ((p3 ∨ (p1 ∧ (False ∧ (True ∧ p3)))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_927803253400423350761722378607 : (((((((p5 → (p4 ∧ True)) → p4) ∧ True) → (True ∧ p3)) ∧ ((p2 ∨ (True → (p2 ∨ ((p1 ∨ False) → (p5 ∧ (p2 → p1)))))) ∧ p4)) → p3) ∧ True) := by
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
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h7 : (((p5 → (p4 ∧ True)) → p4) ∧ True) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h8
      -- One of the premise coincides with the conclusion.
      exact h5
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h9 := h2 h7
    -- We need to get the right conjuct of h9 based on <expert-advice>.
    let h10 := h9.right
    -- One of the premise coincides with the conclusion.
    exact h10
  case inr h11 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h12 : (((p5 → (p4 ∧ True)) → p4) ∧ True) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h13
      -- One of the premise coincides with the conclusion.
      exact h5
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h14 := h2 h12
    -- We need to get the right conjuct of h14 based on <expert-advice>.
    let h15 := h14.right
    -- One of the premise coincides with the conclusion.
    exact h15
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263681995424973854725809917543 : (True ∧ ((((p3 ∨ ((((p4 ∨ p1) ∨ (False ∧ (p1 ∧ False))) ∨ p4) → False)) ∨ (p5 → False)) ∨ True) ∨ (((p1 ∧ False) → (p3 → p1)) ∨ p4))) := by
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
theorem thm_5_vars_150312642148148312498199839047 : ((p4 → (True ∧ ((((False ∧ ((p4 ∨ p4) ∧ p3)) ∧ ((p5 ∨ False) ∨ (p2 ∧ (False ∨ p4)))) → False) → p5))) ∨ ((p3 ∨ (True → True)) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



