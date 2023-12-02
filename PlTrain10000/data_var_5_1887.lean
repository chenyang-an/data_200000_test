variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178676448013694466651037719318 : (((p4 ∨ ((p1 → p2) → True)) ∧ (p4 ∧ (((p5 ∧ p3) ∧ p5) ∨ True))) ∨ (True ∨ ((p2 ∧ (p1 ∧ (False ∧ False))) ∧ (True → (p5 → p2))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_14177096522809599556164960287 : ((((p5 ∨ False) ∨ ((((p5 → (((False ∧ True) ∨ p1) ∨ (True ∧ p3))) ∨ (p4 ∨ (p5 → p2))) → False) → (p4 → p2))) ∧ (False → False)) ∧ True) := by
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
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : ((p5 → (((False ∧ True) ∨ p1) ∨ (True ∧ p3))) ∨ (p4 ∨ (p5 → p2))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- False on the left can always be used.
  apply False.elim h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- False on the left can always be used.
  apply False.elim h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204657248267940895278971934591 : (((p4 ∧ ((p3 ∧ p3) ∨ p2)) ∨ p5) ∨ (p5 → (((p2 ∨ (False → (p5 ∧ False))) ∨ ((p5 ∨ p2) ∨ p2)) ∨ (p1 ∧ (p4 → (p5 → True)))))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180932822135982684606134873263 : (((p4 ∧ p1) ∧ (((p2 ∧ p5) ∨ (p1 ∧ p5)) → ((p5 ∧ False) ∧ True))) → (((p3 ∨ ((p4 ∨ p1) → p4)) ∧ ((False ∨ True) → p5)) → False)) := by
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
    let h6 := h1.left
    let h7 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h6.left
    let h9 := h6.right
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h10 : (False ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h11 := h4 h10
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h12 : ((p2 ∧ p5) ∨ (p1 ∧ p5)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h9
      -- One of the premise coincides with the conclusion.
      exact h11
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h13 := h7 h12
    -- We need to get the left conjuct of h13 based on <expert-advice>.
    let h14 := h13.left
    -- We need to get the right conjuct of h14 based on <expert-advice>.
    let h15 := h14.right
    -- False on the left can always be used.
    apply False.elim h15
  case inr h16 =>
    -- Conjunctions on the left can always be decomposed.
    let h17 := h1.left
    let h18 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h19 := h17.left
    let h20 := h17.right
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h21 : (False ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h22 := h4 h21
    -- We want to use the implication h18 based on <expert-advice>. So we show its premise.
    have h23 : ((p2 ∧ p5) ∨ (p1 ∧ p5)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h20
      -- One of the premise coincides with the conclusion.
      exact h22
    -- We have shown the premise of h18, we can now drive its conclusion.
    let h24 := h18 h23
    -- We need to get the left conjuct of h24 based on <expert-advice>.
    let h25 := h24.left
    -- We need to get the right conjuct of h25 based on <expert-advice>.
    let h26 := h25.right
    -- False on the left can always be used.
    apply False.elim h26



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116777679318421635279959165976 : (((False ∨ p4) ∨ (p3 ∧ ((((True ∨ (((p4 ∧ ((p3 ∨ p1) ∧ (p4 ∧ (p4 ∧ p1)))) ∧ True) → False)) ∨ p2) → p3) ∨ p5))) ∨ (p2 → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62167150558412077902188983896 : ((p2 ∧ (p3 → ((p4 → (p2 ∧ p1)) → ((((p4 ∨ (p2 ∨ p3)) → (p4 ∧ p3)) ∧ (True ∧ (p2 ∧ ((p5 ∨ True) → p2)))) ∧ p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_18275401649825713405779931451 : (((((((True ∨ p3) ∧ (p1 → p3)) ∨ ((p3 → False) ∨ True)) ∨ True) ∨ (p2 ∧ (p5 ∧ (p5 → p2)))) → (((p3 → False) → p2) ∨ True)) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
        -- Conjunctions on the left can always be decomposed.
        let h5 := h4.left
        let h6 := h4.right
        -- Disjunctions on the left can always be decomposed.
        cases h5
        case inl h7 =>
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
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
    case inr h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h13 =>
    -- Conjunctions on the left can always be decomposed.
    let h14 := h13.left
    let h15 := h13.right
    -- Conjunctions on the left can always be decomposed.
    let h16 := h15.left
    let h17 := h15.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148789868399237436899531826784 : (((p2 ∨ ((p3 ∧ (p5 ∨ False)) ∧ True)) ∨ ((p1 → (False ∨ (p4 ∨ (False ∨ p3)))) ∧ (p1 ∧ (p2 → True)))) ∨ ((p2 → (False → p5)) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336685518448357973428441516522 : (p1 → ((((p3 ∨ (True → ((p5 → (p3 → p3)) ∧ ((p1 ∨ p2) ∨ p1)))) → False) ∧ (((p5 ∨ True) → False) → (p5 ∨ (p1 ∨ p1)))) → p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h5 : (p3 ∨ (True → ((p5 → (p3 → p3)) ∧ ((p1 ∨ p2) ∨ p1)))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h7
    -- Implications on the right can always be decomposed.
    intro h8
    -- One of the premise coincides with the conclusion.
    exact h8
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h9 := h3 h5
  -- False on the left can always be used.
  apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42677679016318931098324547436 : (((p4 ∨ (p3 ∨ (p1 ∧ (((p2 → p4) ∨ ((p5 → (p1 ∧ ((((p2 ∧ p1) ∨ p5) ∨ p3) → (p2 → p1)))) ∧ p4)) ∧ p4)))) ∨ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185074045584476377231367183187 : (((p5 ∧ p5) ∨ (p3 ∧ ((((p5 → True) ∨ p1) ∨ p2) → p1))) ∨ ((p1 ∨ True) → ((p4 ∧ False) → ((((p2 → p4) ∨ True) ∧ False) ∧ True)))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h2.left
  let h6 := h2.right
  -- False on the left can always be used.
  apply False.elim h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_751922261911857881804027118771 : (((True ∧ (p3 ∨ ((p4 ∨ ((((True ∧ False) ∨ (((p3 ∧ p3) ∨ (p1 → False)) ∧ p3)) ∧ p5) ∨ True)) ∨ ((p5 ∨ (True ∨ p4)) → p4)))) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_627049461731882328242138227878 : (((((((p1 → (p4 ∨ (False ∨ p2))) ∨ (p3 ∨ (((p5 ∧ (p5 ∨ False)) ∧ (p2 → p3)) ∨ ((p4 → p1) ∨ p5)))) ∧ p4) ∧ p5) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_201330003581250071356728718166 : ((p5 → ((p1 → (p2 → (p5 ∧ True))) → p1)) → (p2 ∨ (((True ∨ ((p1 ∨ p2) → p4)) → (p2 ∧ p1)) ∨ (p1 → (p4 → (False ∨ p4)))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_106374664828665037041112607801 : ((((((p5 ∧ True) ∨ p2) ∧ ((False ∧ p1) ∧ True)) → True) → ((((p5 ∨ p5) ∨ ((p4 ∧ (False ∧ True)) ∧ p5)) ∨ True) ∨ True)) ∧ (True ∨ p5)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165752623199706624106678717969 : (((p3 ∧ (p4 → (p5 ∧ p5))) ∨ ((p1 → ((False ∧ p3) ∧ p3)) ∨ ((p1 → p3) ∧ p4))) ∨ ((p1 ∨ ((p2 → (True → p2)) → p1)) → p1)) := by
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
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h4 : (p2 → (True → p2)) := by
      -- Implications on the right can always be decomposed.
      intro h5
      -- Implications on the right can always be decomposed.
      intro h6
      -- One of the premise coincides with the conclusion.
      exact h5
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h7 := h3 h4
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187726209318385061421416910654 : ((p1 → ((((p4 → p2) ∧ p4) ∨ False) ∧ (p5 → (p3 ∧ p5)))) → (p4 → ((((True ∧ p1) → p5) ∧ (True ∧ (True ∨ (True ∧ p4)))) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50340843234103385746164360790 : (((((p2 ∧ (False → (p3 ∨ False))) ∧ p5) ∨ (((p1 ∨ (p4 ∧ False)) ∧ (p2 ∧ p5)) ∨ (True ∧ p4))) ∨ ((p3 → p5) ∨ (p1 ∨ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301000224427327310859611046281 : (False ∨ (((True → p5) ∧ (((False ∨ p1) ∧ True) → ((p4 ∨ p5) ∨ True))) → (p4 ∨ (((((p2 ∨ p1) → p4) → (True → p5)) ∧ p5) ∨ p4)))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- One of the premise coincides with the conclusion.
  exact h7
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h8 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h9 := h2 h8
  -- One of the premise coincides with the conclusion.
  exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_628964866898377536996412919332 : (((((((((False ∧ p3) → (p3 ∧ False)) ∨ (p2 ∧ p3)) ∧ (((p1 → (p5 → p4)) ∧ ((p5 → p5) ∧ True)) → p1)) ∧ p1) ∨ p1) → False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42920449335358183449010582173 : (((p4 → ((((p1 → (((True → (p2 ∨ p4)) ∧ True) ∨ False)) ∧ p3) ∧ (((p4 → p4) → ((p2 ∨ p5) ∧ p5)) ∨ p2)) ∧ p3)) ∨ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_669474301889190804131748878836 : ((((((((p4 ∨ ((p5 ∨ (True ∧ p2)) ∨ (True → (p1 ∨ p2)))) ∨ (True → False)) ∨ p4) ∨ True) → (False ∨ True)) ∨ ((p5 ∨ False) ∧ p3)) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
            -- Disjunctions on the left can always be decomposed.
            cases h7
            case inl h8 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- True on the right can always be proven directly.
              apply True.intro
            case inr h9 =>
              -- Conjunctions on the left can always be decomposed.
              let h10 := h9.left
              let h11 := h9.right
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- True on the right can always be proven directly.
              apply True.intro
          case inr h12 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
      case inr h13 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h14 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h15 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197319206245860890631318138472 : ((((p5 ∨ True) ∨ ((p2 ∨ True) ∨ True)) → False) ∨ (p2 ∨ (((p4 ∨ (p5 → True)) → True) → (p4 → (True ∧ ((p4 ∨ p3) → (p1 → p1))))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h6 =>
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_707899360613363582665646793855 : ((((p4 ∧ ((True ∧ (p2 → p2)) → (True ∧ p4))) ∨ ((((p2 ∨ (((((p3 → p5) ∧ p2) ∧ p2) → False) → p4)) ∨ p5) ∧ p1) ∨ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_182655917019578685548529414300 : (((((True → False) ∧ True) ∧ (False ∨ p5)) → (p3 ∧ (False → True))) ∧ ((p3 ∧ ((p4 ∨ False) → p5)) → ((p5 ∨ ((True → p1) → p5)) → p3))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  cases h3
  case inl h6 =>
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h8 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h9 := h4 h8
    -- False on the left can always be used.
    apply False.elim h9
  -- Implications on the right can always be decomposed.
  intro h10
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h11
  -- Implications on the right can always be decomposed.
  intro h12
  -- Disjunctions on the left can always be decomposed.
  cases h12
  case inl h13 =>
    -- Conjunctions on the left can always be decomposed.
    let h14 := h11.left
    let h15 := h11.right
    -- One of the premise coincides with the conclusion.
    exact h14
  case inr h16 =>
    -- Conjunctions on the left can always be decomposed.
    let h17 := h11.left
    let h18 := h11.right
    -- One of the premise coincides with the conclusion.
    exact h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49285966799297649317531335841 : (((p5 ∧ (((p3 ∧ (((p1 ∨ ((True ∨ p4) ∨ False)) ∧ (p2 ∨ p3)) ∨ (p1 ∨ (True ∨ p3)))) ∧ False) ∨ p4)) ∨ ((p4 ∧ True) ∧ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_326124099755612852614407562572 : (p5 ∨ (p1 → ((p4 ∨ (p3 ∨ (p1 → (p2 → p2)))) ∧ ((((p4 ∧ p1) ∧ p4) → (True ∧ (True ∧ (p3 ∧ (True ∨ p3))))) ∨ (False ∨ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172027006999416619224155269778 : ((((True ∧ p3) → (p1 ∨ (((p2 ∧ p2) ∨ p1) ∨ (p1 ∧ True)))) ∨ (False ∨ p2)) ∨ ((((((p1 ∧ p3) ∨ False) ∧ True) ∧ True) → True) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_82299500444440091965619601216 : ((((((p4 ∨ (p4 ∧ p3)) ∧ ((p1 ∧ (p3 → p2)) ∨ (False ∨ p1))) ∨ (p1 ∨ p4)) ∧ (p1 → False)) ∧ (((False ∨ False) → p2) ∨ True)) → p4) := by
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
    let h7 := h6.left
    let h8 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h10 =>
        -- Conjunctions on the left can always be decomposed.
        let h11 := h10.left
        let h12 := h10.right
        -- Disjunctions on the left can always be decomposed.
        cases h3
        case inl h13 =>
          -- One of the premise coincides with the conclusion.
          exact h9
        case inr h14 =>
          -- One of the premise coincides with the conclusion.
          exact h9
      case inr h15 =>
        -- Disjunctions on the left can always be decomposed.
        cases h15
        case inl h16 =>
          -- False on the left can always be used.
          apply False.elim h16
        case inr h17 =>
          -- Disjunctions on the left can always be decomposed.
          cases h3
          case inl h18 =>
            -- One of the premise coincides with the conclusion.
            exact h9
          case inr h19 =>
            -- One of the premise coincides with the conclusion.
            exact h9
    case inr h20 =>
      -- Conjunctions on the left can always be decomposed.
      let h21 := h20.left
      let h22 := h20.right
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h23 =>
        -- Conjunctions on the left can always be decomposed.
        let h24 := h23.left
        let h25 := h23.right
        -- Disjunctions on the left can always be decomposed.
        cases h3
        case inl h26 =>
          -- One of the premise coincides with the conclusion.
          exact h21
        case inr h27 =>
          -- One of the premise coincides with the conclusion.
          exact h21
      case inr h28 =>
        -- Disjunctions on the left can always be decomposed.
        cases h28
        case inl h29 =>
          -- False on the left can always be used.
          apply False.elim h29
        case inr h30 =>
          -- Disjunctions on the left can always be decomposed.
          cases h3
          case inl h31 =>
            -- One of the premise coincides with the conclusion.
            exact h21
          case inr h32 =>
            -- One of the premise coincides with the conclusion.
            exact h21
  case inr h33 =>
    -- Disjunctions on the left can always be decomposed.
    cases h33
    case inl h34 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h35 =>
        -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
        have h36 : p1 := by
          -- One of the premise coincides with the conclusion.
          exact h34
        -- We have shown the premise of h5, we can now drive its conclusion.
        let h37 := h5 h36
        -- False on the left can always be used.
        apply False.elim h37
      case inr h38 =>
        -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
        have h39 : p1 := by
          -- One of the premise coincides with the conclusion.
          exact h34
        -- We have shown the premise of h5, we can now drive its conclusion.
        let h40 := h5 h39
        -- False on the left can always be used.
        apply False.elim h40
    case inr h41 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h42 =>
        -- One of the premise coincides with the conclusion.
        exact h41
      case inr h43 =>
        -- One of the premise coincides with the conclusion.
        exact h41



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111756477010392043812750922728 : (((((((p4 → (p3 ∨ (p2 ∨ True))) ∧ (((p4 ∨ (p4 ∨ True)) ∧ (p5 ∨ p1)) ∨ p3)) → p5) ∨ p4) ∧ (p1 ∨ p4)) ∨ p4) ∨ (False ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_124641949435909126132271393930 : (((((True → True) → (p5 → p5)) ∨ p2) → ((p5 ∨ p1) ∧ (((p5 ∧ p1) → (((p2 → p2) ∨ p2) ∨ p2)) ∧ (p4 ∧ False)))) → (p2 ∧ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((True → True) → (p5 → p5)) ∨ p2) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h2
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- False on the left can always be used.
  apply False.elim h8
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h9 : (((True → True) → (p5 → p5)) ∨ p2) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h10
    -- Implications on the right can always be decomposed.
    intro h11
    -- One of the premise coincides with the conclusion.
    exact h11
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h12 := h1 h9
  -- We need to get the right conjuct of h12 based on <expert-advice>.
  let h13 := h12.right
  -- We need to get the right conjuct of h13 based on <expert-advice>.
  let h14 := h13.right
  -- We need to get the right conjuct of h14 based on <expert-advice>.
  let h15 := h14.right
  -- False on the left can always be used.
  apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117722549794864834471522757500 : ((p3 ∧ (p5 ∨ (p4 ∨ (True → (p5 ∨ ((((((True → p3) ∧ p5) ∨ (p5 ∧ ((p4 → p1) ∧ p2))) → p2) ∨ p3) ∨ False)))))) ∨ (p4 → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215390626926742576910708843865 : ((p2 ∧ (p4 ∧ (False ∨ p2))) ∨ (p1 ∨ (((((p4 ∨ True) → p3) ∧ p1) ∨ (True ∨ ((p4 ∨ False) ∨ (p5 ∧ p4)))) ∨ (p4 ∨ (p2 → p2))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_598987771816254266358521287847 : (((((p2 ∨ p4) ∧ (True → ((p3 ∧ (((p4 ∧ ((p1 ∧ True) → p3)) → p4) → ((p1 ∨ p1) ∨ (p1 ∧ p1)))) ∨ (p5 ∨ p2)))) ∧ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137122594092275509140341502490 : ((True ∧ ((p4 ∧ (p5 ∨ p5)) → ((p1 ∧ (((p4 → (p5 → (p1 ∧ p5))) ∧ p4) ∨ p2)) ∨ (p4 ∨ (True ∨ p2))))) ∨ (False ∧ (True → p3))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
theorem thm_5_vars_455927995253485567829708145923 : ((((((p4 ∧ (p2 → p2)) ∧ (((p1 → False) ∧ True) ∧ (p5 ∨ p4))) ∨ ((p2 ∧ p4) → p2)) ∧ (p1 → (p5 ∨ (True → (p1 ∨ p3))))) ∧ True) ∧ True) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Implications on the right can always be decomposed.
  intro h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h5
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h4
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166589276289827415650937310406 : ((True → ((p3 ∧ p1) ∨ ((True ∧ ((p1 ∧ (p1 ∨ (False → p1))) ∨ (p4 ∧ p4))) ∧ p2))) ∨ ((p3 → p1) → (True ∨ ((True ∧ True) ∨ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42141886170426727952102149130 : ((((p5 ∨ True) → (p1 ∨ ((p3 ∧ ((p5 ∨ False) ∧ p3)) ∧ ((((p1 → p4) → (p3 → False)) → (p1 ∨ p5)) ∨ (p1 ∧ True))))) ∨ True) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_729370796709281786253528520956 : (((((p3 ∧ True) ∨ p5) → ((((p1 → (((((p1 ∨ p3) → p5) ∧ p4) ∨ True) → (p1 → True))) → p2) → (p3 → p1)) ∨ (p1 ∧ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315769536554858990122313147836 : (p3 ∨ ((p1 ∧ p3) → ((((False → p2) ∧ (False ∨ ((True ∧ ((p5 → p2) → (True ∧ p4))) ∧ (True ∧ False)))) ∨ p1) ∧ ((p5 ∧ True) → True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215256943374258889966531899861 : ((False ∧ (p3 ∧ (p2 ∨ p2))) ∨ (((p3 ∨ ((p2 ∨ True) ∨ p5)) ∨ p2) ∨ ((((p2 ∧ (p3 → p2)) ∨ True) → p4) ∨ (p3 → (False ∧ False))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41128822002189788095896826250 : (((((((p2 ∧ (p4 ∧ ((False ∨ ((False ∨ p1) ∧ (p3 ∨ False))) ∨ False))) ∨ p4) ∨ (False ∨ True)) ∨ False) ∨ (True → (p1 ∧ p3))) ∨ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159183514563509180822015624497 : ((p1 → (p2 ∨ ((False ∧ (False ∨ (True ∧ ((p4 ∨ p4) ∧ ((p5 ∧ (False ∨ p4)) ∨ p2))))) ∧ p3))) ∨ ((True ∨ False) → ((p2 ∨ p1) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167969352830714602762834737211 : (((p5 ∨ ((p4 ∧ (p3 ∧ True)) ∨ (p2 → p3))) → ((False ∧ p2) ∧ ((p4 → p3) ∨ True))) → ((p2 ∨ ((p3 ∧ (False → False)) → p4)) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h5 : (p5 ∨ ((p4 ∧ (p3 ∧ True)) ∨ (p2 → p3))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h7 := h1 h5
  -- We need to get the left conjuct of h7 based on <expert-advice>.
  let h8 := h7.left
  -- We need to get the left conjuct of h8 based on <expert-advice>.
  let h9 := h8.left
  -- False on the left can always be used.
  apply False.elim h9
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_750867386384554970214954916261 : (((True ∧ (((True → p4) → (((p2 ∧ p4) ∧ (p2 ∨ False)) → p4)) → (p2 ∨ (p4 ∨ (p2 → (p4 → ((True → p1) ∨ (p2 ∧ p4)))))))) ∨ p3) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h2
  -- One of the premise coincides with the conclusion.
  exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60420598047086849982492372416 : (((p4 → p2) → (((((p4 ∧ p4) ∧ (p1 ∧ (False ∧ (p3 → (True ∧ p3))))) ∨ p2) ∨ True) ∧ ((p1 → ((p3 ∨ p3) → p5)) → False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_237866375934061559518224139602 : ((True ∨ True) ∧ ((((((((p1 → p3) ∨ (p3 → p5)) ∧ p3) ∧ p3) → p1) → (p4 ∧ ((False ∧ p1) ∧ ((True → p3) ∧ p4)))) ∨ True) ∧ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111294261810887570592941425424 : (((True ∧ ((((p2 ∨ ((False ∨ p4) → p5)) → False) ∧ (p2 ∨ (True ∨ (p4 ∨ ((p5 ∨ p1) ∨ p3))))) ∧ (p1 ∨ p4))) ∧ p3) ∨ (True ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_763394064587221881349892783966 : (((p3 ∧ (True ∧ ((True ∧ (((p3 → p3) ∧ ((p3 ∧ True) ∧ (p5 ∧ p3))) ∨ p3)) ∧ (((p2 ∧ p5) ∧ (True ∨ (p4 ∧ True))) → p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217002009490497060925283504370 : (((p5 → (p5 → p2)) ∧ p4) → (p2 ∨ ((p4 → (False ∧ True)) → (((p3 ∧ p4) ∨ (((False → ((False ∧ False) ∨ p5)) ∧ p3) → p2)) ∨ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_807394244331971710589650074502 : (((p4 → (((p2 ∧ (p3 ∨ ((False → p1) → (False → True)))) ∧ p1) → (p5 ∨ ((((p4 → p3) ∧ (True → p3)) ∧ True) ∨ (p4 ∨ p2))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50178984370680438326096182847 : (((((((p4 ∨ (False ∨ True)) ∧ ((p1 ∨ p2) → p5)) ∨ ((p2 ∨ p1) ∨ p3)) ∨ (p1 ∨ p3)) ∧ p5) ∨ (((p3 ∧ p3) → True) ∨ False)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249531851012256004025577087463 : ((p5 ∨ p2) ∨ ((((((((p4 → (p4 ∧ ((p2 → False) ∨ (True ∧ p3)))) → p5) ∧ p3) ∨ ((False → p1) ∨ p5)) → p5) ∧ False) ∨ p5) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60190605203265431704162198748 : (((p5 ∨ p3) → (((p1 ∨ (p2 ∨ (False ∨ p3))) ∧ False) ∧ ((((p4 ∨ (p4 ∧ p1)) → ((False ∧ p2) → True)) ∧ True) ∨ (p5 ∨ True)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118358758592777155640147990547 : ((p2 ∨ (((((False ∨ p1) ∧ p3) ∧ ((p2 ∧ p4) ∧ p3)) ∧ ((p1 ∧ (p1 ∨ True)) ∧ ((True → p5) ∧ p3))) ∧ (False ∧ p2))) ∨ (p2 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60051481506926095088134883735 : (((p2 ∨ True) → (p4 ∧ ((p1 → p5) ∧ (p3 ∨ ((p1 ∨ (p2 ∨ ((False ∨ (p2 → ((p1 ∨ True) ∧ p5))) ∧ (p5 ∧ p4)))) ∧ p4))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_253069719273390238681768655865 : ((True ∧ p4) → (((((((True ∨ p4) ∨ p5) → p3) → ((True ∧ (False → (p5 → False))) → p5)) ∨ (p5 ∨ True)) ∨ True) ∧ ((p5 ∧ p5) → p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h1.left
  let h8 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_210710212006586328185299513489 : ((((p1 ∨ p1) → False) → True) ∧ (p4 → (p1 → (((p1 → (p5 ∨ (p1 ∧ ((((False ∨ p1) ∧ p3) ∧ False) → False)))) → (False ∨ p3)) ∨ True)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_746492135771927005207128986786 : ((((p2 ∨ p4) → ((p1 ∧ (p4 → (p5 ∨ ((p1 → (False ∨ False)) → ((((p1 → True) ∨ (p1 → p1)) ∨ False) → (p4 ∧ False)))))) ∧ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171681588508272864470028088463 : (((p2 ∨ (p2 ∧ (p4 → (p3 ∨ (p4 → (((True → p5) ∨ p1) ∧ p3)))))) ∨ p2) ∨ ((p3 → (p2 → True)) ∧ (p1 ∨ ((True ∨ p2) ∨ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_226740019390254926853097607835 : (((p1 ∧ p5) → p3) ∨ (((p1 ∧ p1) ∧ p1) ∨ ((p1 ∧ ((p5 ∧ ((p3 ∨ True) ∧ p2)) ∧ True)) ∨ ((False ∨ (False ∧ (False ∧ False))) → True)))) := by
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
theorem thm_5_vars_41092656863838459815481213920 : ((((((p2 ∧ ((True → (True → p1)) ∧ ((p3 ∨ p2) ∧ False))) ∧ ((p4 → p2) ∧ p5)) ∧ (p1 ∧ False)) ∧ (p4 → (p2 ∧ p4))) ∨ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197944721082039961993745964903 : (((p1 ∧ p1) ∧ ((p2 ∧ (False ∨ p4)) ∨ p4)) ∨ ((p4 → ((False → p4) ∨ ((p5 ∧ False) → ((p2 ∨ p4) ∨ True)))) ∨ ((True → p2) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40893866971321995394181889807 : ((((((False ∨ p3) ∧ False) ∧ ((True ∨ (p4 ∧ (False ∧ (p5 → (p2 ∧ (p1 ∨ ((p5 ∧ p4) → p5))))))) ∧ p3)) ∧ (p3 ∨ p5)) ∨ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66207374815799129475282321602 : ((p5 ∨ (((p1 → ((((p4 ∧ (p5 → p3)) → (p5 ∨ p5)) ∨ p5) → p2)) ∨ p5) → (((p3 ∧ p4) ∧ (p5 ∨ (True ∧ p5))) ∧ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45833663140383807262508002012 : (((p2 → ((((p2 ∧ (((p3 ∨ p5) → p3) ∧ (p3 → p5))) → (False ∨ False)) ∧ p4) → ((p1 → ((p3 ∨ p5) ∧ False)) ∨ p3))) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46836896928615665244549829305 : (((((p4 ∨ ((((True → p5) ∨ False) ∧ (p3 → True)) → p5)) ∧ ((p4 → False) ∨ ((p2 ∧ p3) ∧ (p5 ∨ p4)))) ∧ p2) ∨ (True ∨ p1)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54724485968614122710136431400 : (((((p3 → False) → p3) ∧ (p4 ∨ (p1 ∧ p5))) → (((((p3 ∨ ((p4 → p4) ∧ p4)) ∨ (p4 ∧ p3)) ∨ p1) ∧ (True → p2)) → p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173160300162879464978140637606 : ((p3 ∨ (p3 ∨ (((p4 ∨ (((True → p3) ∨ p2) ∨ p2)) → (p1 → p2)) ∨ p2))) ∨ (p2 → (p2 ∧ ((p3 ∨ p3) ∨ ((p1 ∧ p1) ∨ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230113848251077443159338857026 : (((p3 ∧ p3) ∧ p3) → ((((p2 ∧ False) ∨ p5) → (p5 ∨ p1)) → (((p3 ∨ p4) ∧ ((p4 → (False ∨ False)) ∧ p2)) ∨ (p3 ∨ (p1 → False))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113461300494922491851882561776 : ((((((((p3 ∨ (p1 ∨ p4)) ∧ p1) → p5) ∨ p1) ∧ (p2 ∧ (True ∨ ((p5 → (p4 → p5)) ∧ True)))) → p3) ∨ (p2 → p5)) ∨ (p4 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_806582594737841728032533579678 : (((p4 → ((((False → p3) ∧ True) ∨ (((p2 → ((((False → (True → (p4 → False))) ∧ p2) ∧ False) → p3)) ∨ p1) ∨ (p4 ∧ p1))) → p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336446259868422342322232513099 : (p1 → ((p5 ∨ (((((p1 ∨ p1) ∨ (((((p2 ∨ p2) ∨ p5) → p3) ∧ p5) ∧ False)) ∧ (p2 ∨ ((p4 ∨ p4) ∧ True))) → p5) ∨ p2)) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_737676401506914891975765915523 : ((((p5 → p4) ∧ ((((((p1 ∨ ((p3 ∧ p2) ∨ (((p1 ∨ False) ∨ p4) ∨ p5))) ∨ p2) → (p3 → (p5 → p1))) → p4) ∨ False) ∨ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116023366353951351389623200922 : (((p1 ∧ ((p4 ∧ True) → p5)) → ((((p5 ∧ (False ∧ p3)) ∧ (p5 ∧ p5)) ∨ ((p1 ∧ (True ∨ p3)) → p1)) ∧ (p4 ∨ p1))) ∨ (p4 → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115638020630971251972145589674 : (((((p1 ∧ p3) ∨ (p5 → p1)) ∨ p1) ∨ ((p4 ∧ ((False ∧ p3) ∧ p5)) ∨ ((True ∧ (False → (p1 → p1))) → (False ∧ p4)))) ∨ (p3 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65499055807605150924790203383 : ((p3 ∨ (p5 ∧ (((p3 → (p1 → (((((p3 → False) ∨ p5) → p3) ∧ (p2 ∧ p3)) ∨ (p3 ∧ p4)))) ∨ p3) ∨ ((p4 ∧ False) → p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_88209072719217688953151830747 : (((p2 ∧ ((True ∨ p3) → p3)) ∧ ((p3 → (True → ((p3 ∧ False) ∨ ((((False ∨ (False → p1)) ∨ False) ∨ p2) → (True ∧ True))))) ∨ False)) → p3) := by
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
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h7 : (True ∨ p3) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h8 := h5 h7
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- False on the left can always be used.
    apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204474603511697098473690856560 : (((((p5 ∧ p5) ∧ p1) ∨ p3) ∨ p3) ∨ (((p2 ∨ p2) ∧ p1) → (((p5 ∧ p5) ∧ p4) → (p3 ∨ (((p3 ∧ (False ∧ p5)) ∧ p2) → p3))))) := by
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
  let h5 := h3.left
  let h6 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h1.left
  let h8 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h10
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- Conjunctions on the left can always be decomposed.
    let h13 := h11.left
    let h14 := h11.right
    -- Conjunctions on the left can always be decomposed.
    let h15 := h14.left
    let h16 := h14.right
    -- False on the left can always be used.
    apply False.elim h15
  case inr h17 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h18
    -- Conjunctions on the left can always be decomposed.
    let h19 := h18.left
    let h20 := h18.right
    -- Conjunctions on the left can always be decomposed.
    let h21 := h19.left
    let h22 := h19.right
    -- Conjunctions on the left can always be decomposed.
    let h23 := h22.left
    let h24 := h22.right
    -- False on the left can always be used.
    apply False.elim h23



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147801891241876808456227260785 : (((p1 ∧ (p5 → (p5 ∧ (((False ∧ (p4 ∨ ((p4 ∧ p1) ∨ ((p5 ∧ p4) ∨ p2)))) → False) ∨ p3)))) → p2) ∨ (False → ((p4 → p4) → False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197092305093918472231082487916 : (((p2 ∧ (p3 → ((p2 ∨ False) ∧ False))) ∨ p5) ∨ (((p1 ∨ p4) ∨ (((((p4 → True) ∧ p2) ∧ (p4 ∧ p4)) ∨ (False → False)) ∧ p4)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_727404515843412029677749902018 : ((((p2 ∧ (p3 → p3)) ∨ (p2 ∧ (p2 ∨ ((p5 ∧ (p3 ∧ ((p3 ∨ p3) → (p2 ∨ p2)))) ∧ (True → ((p1 → True) → (p1 → True))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217391313955193114460208750036 : (((True → (p5 ∧ p1)) ∨ p1) → ((((((p4 → False) → (p5 → p5)) → p5) ∧ ((True ∧ (p2 → p3)) ∧ (p5 → (p4 ∧ False)))) ∧ p3) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h3 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h4 := h2 h3
    -- We need to get the right conjuct of h4 based on <expert-advice>.
    let h5 := h4.right
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_873071466603805207829164889479 : ((((p1 → (((False ∨ (p5 ∧ (p4 → p1))) ∧ (False ∨ p3)) ∨ (p2 → (p4 → (((p3 ∧ False) ∧ (p2 → True)) ∨ (True ∧ p2)))))) → p5) → p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p1 → (((False ∨ (p5 ∧ (p4 → p1))) ∧ (False ∨ p3)) ∨ (p2 → (p4 → (((p3 ∧ False) ∧ (p2 → True)) ∨ (True ∧ p2)))))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46279264319943465569955376460 : ((((p1 ∧ ((((False ∨ True) ∧ p2) ∨ (p4 ∨ ((((False → p2) ∨ p5) ∧ p5) → p5))) ∨ p2)) ∧ (p4 ∧ (True → False))) ∧ (p5 ∨ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303828409077645060709025785601 : (p1 ∨ ((((((True ∧ True) → p5) → p5) ∧ ((((False → p3) ∧ (p4 → p3)) → (((p3 → p2) ∧ p1) ∨ p4)) ∨ p2)) ∧ (p2 ∨ p5)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52571055154440032963680327949 : (((((p1 ∧ (p5 → (True ∨ (True ∨ p5)))) ∧ (p5 ∨ p3)) ∨ (p5 ∨ p2)) ∨ ((True → (p3 → True)) ∨ (((True ∧ p1) ∨ p5) ∨ p1))) ∨ p2) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179491491933904784362652031437 : ((True → (False ∨ (((p2 → p5) ∨ p1) → (p4 ∨ (False ∧ (p3 ∧ p2)))))) ∨ (p1 → ((False → ((((p4 ∧ True) ∧ p5) → p4) → p5)) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258915823577153396681290921570 : ((True → p2) → (((False → True) → p3) ∨ (False ∨ (p2 → (p2 → ((((p2 ∨ (True → (p2 → p1))) ∧ True) ∧ p1) ∨ (p1 ∨ (True ∧ p2)))))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113407754859255829588153030395 : (((((((p3 ∨ (p3 ∨ (p4 → (p5 ∧ (p5 → (p1 → (False ∧ p5))))))) ∧ p3) ∨ (p1 → p3)) ∧ p2) ∧ True) ∨ (False ∧ True)) ∨ (p5 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53341621328594736059632167735 : (((((False → p3) ∧ (True ∧ ((p3 ∧ p5) ∨ (True ∧ p3)))) ∧ p2) → (((((p3 ∧ p1) ∧ (p1 → p4)) ∨ p1) ∧ (True ∧ p5)) ∨ p3)) ∨ p3) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h9
  case inr h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199638475039369720298710387936 : ((((p3 ∨ (p3 ∨ False)) ∨ (False → p5)) → False) → (p5 → ((((p2 → p3) ∧ (p5 ∧ p1)) → (p1 ∨ False)) ∧ (((p2 ∨ True) → p1) ∧ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h7
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h8
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h9 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h10 : ((p3 ∨ (p3 ∨ False)) ∨ (False → p5)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h11
      -- False on the left can always be used.
      apply False.elim h11
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h12 := h1 h10
    -- False on the left can always be used.
    apply False.elim h12
  case inr h13 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h14 : ((p3 ∨ (p3 ∨ False)) ∨ (False → p5)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h15
      -- False on the left can always be used.
      apply False.elim h15
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h16 := h1 h14
    -- False on the left can always be used.
    apply False.elim h16
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231473050267212329326213513407 : (((p3 → False) ∨ p1) → ((((p1 ∧ p1) ∧ p2) ∨ False) ∨ (False ∨ (((p4 ∨ p1) → (((p2 ∨ p5) ∨ p5) ∧ False)) → (p3 → (p3 ∨ True)))))) := by
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
    -- Implications on the right can always be decomposed.
    intro h4
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
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
theorem thm_5_vars_205518049786836115629123209692 : (((p5 ∧ p5) ∧ ((p3 ∧ p4) ∨ p5)) ∨ ((False ∨ p1) → (True ∨ (True → (((p4 → (p1 ∨ (p2 ∧ (p4 ∧ False)))) ∧ (p5 → p4)) ∧ p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- False on the left can always be used.
    apply False.elim h2
  case inr h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304720726352988461637833738971 : (p1 ∨ ((((((p5 ∧ ((p4 ∧ (True → p2)) ∧ True)) ∧ p3) ∧ p1) ∨ ((p4 → True) ∧ True)) ∧ ((p5 → p3) → (True ∧ p3))) ∨ (p4 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_357441778401443610899562603179 : (p5 → ((True → False) → (((((p3 ∨ (p1 ∨ p3)) ∨ p4) ∨ True) ∧ ((p1 ∧ p2) ∧ ((p2 ∧ p3) ∧ (p2 ∨ ((p2 ∨ p4) ∨ p4))))) ∧ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
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
  -- False on the left can always be used.
  apply False.elim h4
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h5 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h5
  -- False on the left can always be used.
  apply False.elim h6
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h7 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h8 := h2 h7
  -- False on the left can always be used.
  apply False.elim h8
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h9 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h10 := h2 h9
  -- False on the left can always be used.
  apply False.elim h10
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h11 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h12 := h2 h11
  -- False on the left can always be used.
  apply False.elim h12
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h13 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h14 := h2 h13
  -- False on the left can always be used.
  apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259918206197438776970458202178 : ((p1 → p5) → (((((p1 ∨ ((False → p4) → ((False ∨ p2) ∧ (p5 ∨ (True ∨ p2))))) ∨ (p3 → True)) ∨ p3) ∨ (False → (p4 → p2))) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_344731033627705647917135055334 : (p2 → (p3 → (((((True ∨ p5) → (((p4 → (True ∧ (p5 ∧ p1))) → False) ∨ True)) ∨ p3) ∨ p1) ∨ (((p4 → False) ∨ (p2 → False)) ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38591588085154932215134892943 : ((((p3 ∧ ((p5 ∧ p3) ∨ ((p1 ∧ (p4 → p3)) → True))) → ((p1 ∧ (p2 → (((p3 → (p2 ∨ True)) → False) ∨ p1))) ∧ p3)) ∧ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_620102713180058994701725818692 : (((((True ∧ p5) ∨ ((((((p3 ∨ p1) → (p1 ∨ p2)) ∧ (p3 ∧ ((False → p1) ∨ p1))) ∧ p3) ∧ p5) → (p1 ∧ (p4 ∧ p4)))) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



