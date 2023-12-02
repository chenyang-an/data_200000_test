variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_715195554671292760709388311196 : ((((False → ((False ∧ (p4 ∧ p3)) ∨ p1)) → (((p2 → False) ∨ ((p3 ∨ p5) ∨ ((True ∧ False) ∨ (p2 ∧ p5)))) ∨ ((p5 ∧ p2) → True))) ∨ p1) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_82296572872388730897246076504 : ((((((((p3 → p1) ∨ (p4 → p2)) → ((True ∨ p1) → (False ∨ p2))) ∨ p4) ∧ p2) ∧ (p3 → p2)) ∧ (((p3 → True) ∨ p5) ∨ p5)) → p2) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- One of the premise coincides with the conclusion.
        exact h7
      case inr h11 =>
        -- One of the premise coincides with the conclusion.
        exact h7
    case inr h12 =>
      -- One of the premise coincides with the conclusion.
      exact h7
  case inr h13 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h14 =>
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h15 =>
        -- One of the premise coincides with the conclusion.
        exact h7
      case inr h16 =>
        -- One of the premise coincides with the conclusion.
        exact h7
    case inr h17 =>
      -- One of the premise coincides with the conclusion.
      exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_320420332943857043193271378365 : (p4 ∨ ((True ∨ p2) → (p5 ∨ (p5 ∨ ((p4 ∧ (p5 ∨ p2)) → ((((True → (p3 ∨ p4)) → (True → p5)) ∨ (p5 ∨ p4)) ∧ (True ∨ p3))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
    -- Conjunctions on the left can always be decomposed.
    let h8 := h3.left
    let h9 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h11 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h12 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h13
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the left can always be decomposed.
    let h14 := h13.left
    let h15 := h13.right
    -- Disjunctions on the left can always be decomposed.
    cases h15
    case inl h16 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h16
    case inr h17 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h14
    -- Conjunctions on the left can always be decomposed.
    let h18 := h13.left
    let h19 := h13.right
    -- Disjunctions on the left can always be decomposed.
    cases h19
    case inl h20 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h21 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112324036787234987944411473879 : (((p3 → (False ∧ (((((p5 ∨ p2) ∧ p2) ∧ (True → (p2 ∧ (p3 ∨ ((p5 ∧ p4) ∧ (p2 ∧ p3)))))) ∨ p4) ∧ p4))) ∨ True) ∨ (p1 ∧ True)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51779925719840008724374124931 : (((p2 ∧ (False ∧ (((True ∨ ((p5 ∨ p1) ∧ (p3 ∨ (p2 → p4)))) ∨ p4) → p3))) ∧ (((((p1 ∨ p1) ∧ True) ∨ p1) → True) ∧ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_457736047271043016260469142871 : (((((p5 ∧ (p2 ∨ (False ∨ ((False ∨ (False ∨ p1)) ∧ (False ∧ p4))))) ∧ ((p2 → p2) → True)) ∨ (p4 ∨ ((p5 ∨ (p4 ∧ p5)) → True))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_47422203237276075836359669394 : (((p1 ∧ (((p4 ∨ (((False ∨ (p5 ∨ p4)) ∨ p2) ∨ p3)) ∧ p4) ∧ ((p3 ∨ p1) → (False ∨ (False ∨ (True → p5)))))) ∨ (p2 → p2)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350179439444381508499194389101 : (p4 → (((p1 ∧ (False ∧ (p4 ∧ False))) ∧ (False ∧ (p3 ∧ ((p4 → (p2 ∧ ((((p1 ∨ False) ∧ p1) → False) → True))) ∨ (True ∨ True))))) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227857422797496199871083172139 : ((p2 ∧ (p1 ∨ p1)) ∨ ((p4 ∨ (p2 ∧ p5)) ∨ (True ∨ ((p5 → (p4 ∧ (p5 ∨ ((p3 → p3) ∨ ((p3 ∧ (p3 ∨ True)) → p2))))) ∨ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64558822170842624554109818093 : ((p1 ∨ (((p3 → p3) ∧ (p5 ∧ p3)) → (p5 → ((p4 ∧ ((False ∧ (p3 ∧ (False ∧ p3))) ∨ p4)) ∨ (((p3 → p4) ∧ p5) → p5))))) ∨ False) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h7
  -- Conjunctions on the left can always be decomposed.
  let h8 := h7.left
  let h9 := h7.right
  -- One of the premise coincides with the conclusion.
  exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_678322719457222976697759436609 : (((((p3 → (p1 → (True ∨ ((p2 → True) → p1)))) → (((p3 ∨ (True ∧ True)) ∧ (True → p1)) ∧ False)) ∨ ((False ∧ p2) → (p3 ∨ p3))) ∨ p2) ∧ True) := by
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
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_196811213716988760944907643639 : ((((p2 → p4) → (False ∧ (p1 ∨ p4))) ∧ p5) ∨ (((((p3 ∧ p5) → ((p5 ∧ ((p5 ∨ (p4 ∧ False)) → p4)) → p3)) ∨ p2) ∨ p3) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  let h5 := h1.left
  let h6 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_25242809166419602628528857521 : ((((p3 → False) ∧ p1) → (((((p1 ∧ True) → p2) → (p3 ∨ p2)) → p3) → (False ∨ ((p4 ∧ p1) ∧ ((True → (False ∨ p5)) ∧ p5))))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h5 : (((p1 ∧ True) → p2) → (p3 ∨ p2)) := by
    -- Implications on the right can always be decomposed.
    intro h6
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h7 : (p1 ∧ True) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h4
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h8 := h6 h7
    -- One of the premise coincides with the conclusion.
    exact h8
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h9 := h2 h5
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h10 : p3 := by
    -- One of the premise coincides with the conclusion.
    exact h9
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h11 := h3 h10
  -- False on the left can always be used.
  apply False.elim h11
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310018352670975339165294127581 : (p2 ∨ (((((((False ∧ ((p5 ∨ True) ∨ (p1 ∧ True))) ∨ p4) ∨ p3) ∨ p4) ∨ p1) ∨ True) ∨ (((False ∧ ((p3 ∧ p5) ∧ p1)) ∧ False) ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199189947717975904954409469655 : (((p3 ∧ (p4 → ((True → p3) ∨ p4))) ∧ p1) → ((p5 → p4) ∨ ((p1 ∨ p5) → (p3 → (p2 → (p3 ∧ ((False ∨ (True ∧ p3)) ∧ p1))))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h6
  -- Implications on the right can always be decomposed.
  intro h7
  -- Implications on the right can always be decomposed.
  intro h8
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h9 =>
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h10 =>
    -- One of the premise coincides with the conclusion.
    exact h7
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h11 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h12 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- One of the premise coincides with the conclusion.
    exact h7
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h13 =>
    -- One of the premise coincides with the conclusion.
    exact h13
  case inr h14 =>
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263639361900265094516361942108 : (True ∧ ((p5 → (((p4 → ((p2 → p4) → (p3 ∨ True))) ∨ (True ∨ (True ∨ True))) ∧ (p3 ∨ (p3 → False)))) → (((p1 → p2) ∧ p3) ∨ True))) := by
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
theorem thm_5_vars_137637353088011444249541979684 : ((False ∨ (((p1 → ((p4 ∨ (p2 ∨ (True → True))) ∧ True)) → (p3 ∧ (True ∨ False))) ∧ (True ∧ (p2 → (p4 ∧ p2))))) ∨ ((True ∧ True) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204966453590566405686580810055 : (((p1 ∧ ((True ∧ p4) → p3)) → p3) ∨ (((True → (((p5 → (p3 ∧ (True ∧ (p4 ∧ (p3 ∧ p1))))) ∧ p3) ∧ (p1 ∧ False))) ∧ p3) → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258668555361859536818024111669 : ((p5 ∨ p5) → ((True ∨ ((p2 ∨ p2) ∧ (p3 ∨ p5))) ∧ ((((p3 ∧ False) ∨ (p1 → p5)) ∧ p4) ∨ (((False → p5) ∧ False) → (True ∨ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- False on the left can always be used.
    apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187073982851475729171452494267 : (((p4 ∨ p5) ∧ ((p2 ∨ (p1 → p1)) → (False ∨ (False → p2)))) → (((((p4 ∨ p3) ∧ True) → (p3 → ((p4 ∨ True) ∧ p1))) ∧ False) ∨ True)) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_596782179528566894310147888909 : (((((p4 → (p5 ∨ ((p3 ∨ p1) ∧ False))) ∧ ((((p4 ∨ p2) → ((p1 ∨ (p4 ∧ True)) → (p1 → True))) ∨ True) → (p4 ∧ p1))) ∧ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_242843815316671295280554292897 : ((p3 → p3) ∧ (p3 → (p5 → (((False ∧ True) ∨ (True ∧ p1)) ∨ ((((p3 ∨ ((p2 → p3) ∨ p3)) → p2) ∧ p3) → (False ∨ (False ∨ p2))))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h7 : (p3 ∨ ((p2 → p3) ∨ p3)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h6
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h8 := h5 h7
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119746720472377149406982567096 : (((((p4 ∨ (p3 ∧ p2)) ∧ ((p5 ∧ p5) → ((p5 ∧ (((True ∨ p3) ∨ True) → p1)) → (True → (p1 ∧ p3))))) ∨ p2) ∧ p3) → (p1 ∨ p3)) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
  case inr h11 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187183086287641031622000739678 : (((p4 ∧ False) → ((True ∨ (False ∧ p4)) → (False ∨ (p5 ∨ p3)))) → (p3 → ((p2 ∨ (p3 ∧ False)) ∨ (p2 → (((False ∨ p5) ∧ False) ∨ p2))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263623410430168173034668680007 : (True ∧ (((True → False) ∧ (((((p5 → True) → False) ∧ True) → (((p2 ∨ p2) → (p2 ∧ p1)) → True)) ∨ p2)) → (((p5 ∧ p3) ∧ p3) ∧ p2))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h8 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h9 := h2 h8
    -- False on the left can always be used.
    apply False.elim h9
  -- Conjunctions on the left can always be decomposed.
  let h10 := h1.left
  let h11 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h11
  case inl h12 =>
    -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
    have h13 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h10, we can now drive its conclusion.
    let h14 := h10 h13
    -- False on the left can always be used.
    apply False.elim h14
  case inr h15 =>
    -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
    have h16 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h10, we can now drive its conclusion.
    let h17 := h10 h16
    -- False on the left can always be used.
    apply False.elim h17
  -- Conjunctions on the left can always be decomposed.
  let h18 := h1.left
  let h19 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h19
  case inl h20 =>
    -- We want to use the implication h18 based on <expert-advice>. So we show its premise.
    have h21 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h18, we can now drive its conclusion.
    let h22 := h18 h21
    -- False on the left can always be used.
    apply False.elim h22
  case inr h23 =>
    -- We want to use the implication h18 based on <expert-advice>. So we show its premise.
    have h24 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h18, we can now drive its conclusion.
    let h25 := h18 h24
    -- False on the left can always be used.
    apply False.elim h25
  -- Conjunctions on the left can always be decomposed.
  let h26 := h1.left
  let h27 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h27
  case inl h28 =>
    -- We want to use the implication h26 based on <expert-advice>. So we show its premise.
    have h29 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h26, we can now drive its conclusion.
    let h30 := h26 h29
    -- False on the left can always be used.
    apply False.elim h30
  case inr h31 =>
    -- One of the premise coincides with the conclusion.
    exact h31



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114381069192330210814505311126 : ((((p5 ∧ (((True → False) ∨ (p2 ∧ ((p4 ∧ True) → (True ∧ (p2 ∨ p1))))) → p3)) → p2) ∨ ((p1 ∨ p2) ∨ (False ∨ p1))) ∨ (False → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_656936225594081006511639494975 : (((((p5 ∨ ((p2 ∧ True) → p5)) ∨ ((((False ∧ ((((False → p2) ∧ (p1 ∨ p3)) ∧ True) ∧ p3)) ∧ p4) ∨ p4) ∨ p4)) ∨ (p2 ∧ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49430554209621735569431416799 : (((((p3 → (p2 ∧ (((((((p3 ∨ p2) → p5) ∨ p2) → (p2 ∧ p2)) ∧ p2) → p2) ∧ p1))) ∨ p1) ∨ True) → (p1 → (p4 → p1))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h6 =>
      -- One of the premise coincides with the conclusion.
      exact h6
  case inr h7 =>
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_748305921638124450802447815527 : ((((p2 → p1) → ((((p1 → p1) → p1) ∨ (p5 ∧ (p2 ∧ (p5 ∧ ((False → (p5 ∧ ((p2 ∨ p5) ∧ False))) ∨ (False ∨ p5)))))) ∨ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_582736166779984928740181462597 : (((p5 → ((((p2 ∨ p4) ∧ ((False ∧ p3) ∨ p2)) ∨ (((p4 ∧ (True ∧ (p2 ∧ False))) → (False ∨ p4)) → ((p5 ∨ p3) ∨ p5))) ∨ p1)) ∧ True) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114374177745281871791969695282 : ((((((p5 → ((True ∧ (((p5 → (p1 ∨ p5)) ∧ p4) ∨ p4)) ∨ p4)) → p1) ∧ p3) → False) ∨ (True ∨ ((p5 ∨ p4) ∧ p4))) ∨ (True ∧ True)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_588431609048987753674071181259 : (((((((p4 ∧ p2) → False) → ((p2 → (p3 ∧ p3)) → ((((p3 → p5) → (p1 ∧ (p3 ∨ p5))) ∨ (p3 → p4)) ∨ p3))) ∨ p5) ∧ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_903228911847659355492706662770 : ((((p5 ∧ (True ∧ (((p4 ∨ (p2 ∨ p1)) ∨ (False ∨ p5)) ∧ ((p1 ∨ p2) ∧ ((True ∨ True) → False))))) ∧ (p2 ∨ (p3 → (p5 → p3)))) → False) ∧ True) := by
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
  let h8 := h7.left
  let h9 := h7.right
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h9.left
      let h13 := h9.right
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h14 =>
        -- Disjunctions on the left can always be decomposed.
        cases h3
        case inl h15 =>
          -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
          have h16 : (True ∨ True) := by
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h13, we can now drive its conclusion.
          let h17 := h13 h16
          -- False on the left can always be used.
          apply False.elim h17
        case inr h18 =>
          -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
          have h19 : (True ∨ True) := by
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h13, we can now drive its conclusion.
          let h20 := h13 h19
          -- False on the left can always be used.
          apply False.elim h20
      case inr h21 =>
        -- Disjunctions on the left can always be decomposed.
        cases h3
        case inl h22 =>
          -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
          have h23 : (True ∨ True) := by
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h13, we can now drive its conclusion.
          let h24 := h13 h23
          -- False on the left can always be used.
          apply False.elim h24
        case inr h25 =>
          -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
          have h26 : (True ∨ True) := by
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h13, we can now drive its conclusion.
          let h27 := h13 h26
          -- False on the left can always be used.
          apply False.elim h27
    case inr h28 =>
      -- Disjunctions on the left can always be decomposed.
      cases h28
      case inl h29 =>
        -- Conjunctions on the left can always be decomposed.
        let h30 := h9.left
        let h31 := h9.right
        -- Disjunctions on the left can always be decomposed.
        cases h30
        case inl h32 =>
          -- Disjunctions on the left can always be decomposed.
          cases h3
          case inl h33 =>
            -- We want to use the implication h31 based on <expert-advice>. So we show its premise.
            have h34 : (True ∨ True) := by
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h31, we can now drive its conclusion.
            let h35 := h31 h34
            -- False on the left can always be used.
            apply False.elim h35
          case inr h36 =>
            -- We want to use the implication h31 based on <expert-advice>. So we show its premise.
            have h37 : (True ∨ True) := by
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h31, we can now drive its conclusion.
            let h38 := h31 h37
            -- False on the left can always be used.
            apply False.elim h38
        case inr h39 =>
          -- Disjunctions on the left can always be decomposed.
          cases h3
          case inl h40 =>
            -- We want to use the implication h31 based on <expert-advice>. So we show its premise.
            have h41 : (True ∨ True) := by
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h31, we can now drive its conclusion.
            let h42 := h31 h41
            -- False on the left can always be used.
            apply False.elim h42
          case inr h43 =>
            -- We want to use the implication h31 based on <expert-advice>. So we show its premise.
            have h44 : (True ∨ True) := by
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h31, we can now drive its conclusion.
            let h45 := h31 h44
            -- False on the left can always be used.
            apply False.elim h45
      case inr h46 =>
        -- Conjunctions on the left can always be decomposed.
        let h47 := h9.left
        let h48 := h9.right
        -- Disjunctions on the left can always be decomposed.
        cases h47
        case inl h49 =>
          -- Disjunctions on the left can always be decomposed.
          cases h3
          case inl h50 =>
            -- We want to use the implication h48 based on <expert-advice>. So we show its premise.
            have h51 : (True ∨ True) := by
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h48, we can now drive its conclusion.
            let h52 := h48 h51
            -- False on the left can always be used.
            apply False.elim h52
          case inr h53 =>
            -- We want to use the implication h48 based on <expert-advice>. So we show its premise.
            have h54 : (True ∨ True) := by
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h48, we can now drive its conclusion.
            let h55 := h48 h54
            -- False on the left can always be used.
            apply False.elim h55
        case inr h56 =>
          -- Disjunctions on the left can always be decomposed.
          cases h3
          case inl h57 =>
            -- We want to use the implication h48 based on <expert-advice>. So we show its premise.
            have h58 : (True ∨ True) := by
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h48, we can now drive its conclusion.
            let h59 := h48 h58
            -- False on the left can always be used.
            apply False.elim h59
          case inr h60 =>
            -- We want to use the implication h48 based on <expert-advice>. So we show its premise.
            have h61 : (True ∨ True) := by
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h48, we can now drive its conclusion.
            let h62 := h48 h61
            -- False on the left can always be used.
            apply False.elim h62
  case inr h63 =>
    -- Disjunctions on the left can always be decomposed.
    cases h63
    case inl h64 =>
      -- False on the left can always be used.
      apply False.elim h64
    case inr h65 =>
      -- Conjunctions on the left can always be decomposed.
      let h66 := h9.left
      let h67 := h9.right
      -- Disjunctions on the left can always be decomposed.
      cases h66
      case inl h68 =>
        -- Disjunctions on the left can always be decomposed.
        cases h3
        case inl h69 =>
          -- We want to use the implication h67 based on <expert-advice>. So we show its premise.
          have h70 : (True ∨ True) := by
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h67, we can now drive its conclusion.
          let h71 := h67 h70
          -- False on the left can always be used.
          apply False.elim h71
        case inr h72 =>
          -- We want to use the implication h67 based on <expert-advice>. So we show its premise.
          have h73 : (True ∨ True) := by
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h67, we can now drive its conclusion.
          let h74 := h67 h73
          -- False on the left can always be used.
          apply False.elim h74
      case inr h75 =>
        -- Disjunctions on the left can always be decomposed.
        cases h3
        case inl h76 =>
          -- We want to use the implication h67 based on <expert-advice>. So we show its premise.
          have h77 : (True ∨ True) := by
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h67, we can now drive its conclusion.
          let h78 := h67 h77
          -- False on the left can always be used.
          apply False.elim h78
        case inr h79 =>
          -- We want to use the implication h67 based on <expert-advice>. So we show its premise.
          have h80 : (True ∨ True) := by
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h67, we can now drive its conclusion.
          let h81 := h67 h80
          -- False on the left can always be used.
          apply False.elim h81
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193209064394774897179145073013 : (((p3 ∨ ((p1 → p4) ∨ p1)) → ((p5 ∨ True) ∧ p2)) → (((True → p3) ∧ p4) ∨ ((p3 ∧ ((p4 ∧ p1) ∨ p1)) → ((p1 → False) ∨ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40895363172325096832192772089 : ((((((p3 → p1) ∨ p5) ∨ ((((p2 ∧ p1) → (p5 ∨ ((False ∨ (p2 ∨ (True → p5))) → p3))) → p4) ∨ p2)) ∧ (p2 → p3)) ∨ True) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37765286039416972581433873642 : ((((((True ∧ p4) ∧ True) ∨ ((p1 ∨ (p5 → p1)) ∨ (((True ∨ p4) ∧ (False ∨ p4)) → (((True ∧ p3) ∨ p5) → p5)))) → p1) ∧ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54053455429141122352654025900 : ((((p5 → ((p3 ∨ p1) → p5)) ∨ (p4 → (True → True))) → (p4 ∨ (((p3 ∨ (True → (((p1 → p5) ∧ False) ∨ p1))) ∨ p1) ∨ True))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62858510624480387326074719483 : ((p4 ∧ (((p5 ∧ True) ∨ (p4 ∨ p2)) → (p1 → ((((((p3 ∧ (p1 ∨ p5)) ∨ p3) → True) ∨ p3) ∧ (True ∧ p1)) → (p4 → p2))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_344494126574867901773992714578 : (p2 → (True → ((((p2 ∨ p3) ∧ (p4 ∨ p3)) → (p3 ∨ p5)) → ((((p5 → (p4 ∨ p3)) ∧ p5) ∧ p5) ∨ ((False ∧ p4) ∨ (p2 ∨ False)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197618478966258087813708898996 : (((((p2 → p4) ∧ p5) ∧ True) → (p3 ∧ p3)) ∨ (((False ∨ True) ∨ ((p2 ∨ (p4 ∧ p4)) ∧ ((p2 ∧ ((p2 → p4) ∧ p5)) → p4))) ∨ p2)) := by
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
theorem thm_5_vars_39019055492954290264289367274 : ((((False → True) ∧ (((True → False) ∧ p4) ∨ (((p1 ∧ ((((True → p2) → (p1 → False)) → p2) → p1)) ∧ (p1 ∧ p4)) ∨ p5))) ∧ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45234210058142869319237526421 : (((p1 ∧ ((((p4 ∧ (((p3 ∧ ((p1 ∧ p5) → p4)) ∨ True) ∨ (p2 ∧ p5))) ∧ p2) ∨ (((False ∧ False) → p3) ∧ p1)) → p4)) → p4) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : (((p4 ∧ (((p3 ∧ ((p1 ∧ p5) → p4)) ∨ True) ∨ (p2 ∧ p5))) ∧ p2) ∨ (((False ∧ False) → p3) ∧ p1)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- False on the left can always be used.
    apply False.elim h6
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h8 := h3 h4
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173710290549590567307919556958 : (((((p1 ∨ (True ∨ ((False → True) ∧ p3))) → (p1 ∧ p5)) ∧ (False ∨ p5)) ∨ True) → ((((p1 ∨ p4) ∨ (p2 ∨ False)) ∧ p4) ∨ (False → p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
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
      -- False on the left can always be used.
      apply False.elim h7
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- False on the left can always be used.
    apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64577284975520494096128583701 : ((p1 ∨ ((p2 ∧ (p4 ∧ p1)) → (((((p2 ∧ ((p1 ∨ False) ∨ p4)) → (p3 → p3)) → False) ∨ ((p2 ∧ p3) ∧ (p1 → True))) ∨ p1))) ∨ p4) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173200333114531455744801480418 : ((p5 ∨ ((p1 → (((True → p2) ∧ p4) → ((p3 ∨ p3) ∨ (p1 ∧ False)))) ∨ p5)) ∨ (((p5 ∧ ((p2 ∨ True) ∧ (p5 ∧ False))) ∧ p1) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_344845016520751285965263889089 : (p2 → (p5 → ((((p3 → p5) ∧ (p1 ∨ ((p3 → False) ∨ p2))) → ((p1 ∧ (p1 ∨ (p2 ∧ (p3 ∧ False)))) ∨ (p2 ∨ p3))) ∨ (p4 → p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168313004442783069644972965817 : (((True → False) ∧ ((((False → p2) ∨ ((True ∨ (p1 → p1)) ∧ (p1 ∨ False))) ∧ True) → p5)) → (((p5 → p4) ∧ (True → p4)) ∧ (False ∧ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- False on the left can always be used.
  apply False.elim h6
  -- Implications on the right can always be decomposed.
  intro h7
  -- Conjunctions on the left can always be decomposed.
  let h8 := h1.left
  let h9 := h1.right
  -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
  have h10 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h8, we can now drive its conclusion.
  let h11 := h8 h10
  -- False on the left can always be used.
  apply False.elim h11
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h12 := h1.left
  let h13 := h1.right
  -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
  have h14 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h12, we can now drive its conclusion.
  let h15 := h12 h14
  -- False on the left can always be used.
  apply False.elim h15
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_318620660793962779655775493483 : (p4 ∨ (((False ∧ p4) ∨ (((p5 ∧ p5) ∧ (False ∨ ((p5 ∧ p5) ∨ (False ∨ p2)))) ∨ (p4 ∧ ((p3 ∧ p1) ∨ (True → p4))))) ∨ (True ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_355586087824389655172784320567 : (p5 → ((((p1 ∧ p4) → ((p5 ∧ (False → p2)) ∨ (p2 ∨ True))) → (((False ∨ (False ∧ (p1 ∧ True))) → p4) ∧ (p3 ∧ True))) ∨ (p5 ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197226669043381550222976133801 : ((((True → (p1 ∧ (p2 ∨ p2))) ∨ p1) → p2) ∨ (p5 → ((((True ∧ True) ∧ ((p3 ∨ False) ∨ (False ∨ True))) ∨ p5) ∧ (p4 → (True ∧ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303971483807579233225116531855 : (p1 ∨ (((p3 → (p4 ∧ p1)) ∨ (p2 ∨ ((p4 ∨ ((p5 ∧ p4) → p2)) → ((p2 → p1) ∧ ((p5 ∧ (p3 → p3)) ∨ (p2 ∨ p3)))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322569553953572125459257821249 : (p5 ∨ ((p3 ∨ (p2 ∧ ((True → p3) → (((p3 ∨ p5) ∨ True) ∧ ((False ∧ (False ∨ (p1 ∧ (((p5 ∧ p5) → p1) ∨ p4)))) ∨ p5))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157766268699421408827383853340 : (((p4 ∨ (((False ∨ ((p1 ∨ p2) ∧ p1)) ∧ (True ∧ True)) ∧ True)) ∧ (p4 ∧ ((p2 → False) → p1))) ∨ ((((p4 → False) ∧ p3) ∧ p2) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_677672091656581416855648439832 : (((((((p1 ∧ p2) → ((False ∨ ((p1 → p1) → (p3 → p2))) ∨ p5)) → ((p4 ∨ p4) ∨ p1)) → p4) ∨ (p3 → (True → (False ∨ p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_355633651103781222401772695799 : (p5 → ((True → ((((((False ∨ False) → (((p2 ∨ p5) → p3) → p5)) ∧ p1) ∧ False) ∨ (p2 ∨ False)) ∨ (p2 ∨ (p5 → True)))) ∨ (p2 → p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_797245234900801410542490410557 : (((p1 → ((((p4 ∧ (p2 → (((p4 ∧ ((((True → p2) ∨ (p3 ∧ p1)) ∧ p5) ∨ p3)) → False) ∨ p2))) ∨ (p3 ∨ p5)) ∨ True) ∨ p2)) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_727329129471439663367756634098 : ((((p1 ∧ (p4 → False)) ∨ (((True ∧ ((p5 → p4) ∨ ((((p3 → p4) → (p4 ∨ p2)) → p3) ∧ (p2 ∧ p5)))) → (False ∧ p5)) ∨ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_93705759415921493548248503582 : ((p1 ∧ (((((True ∧ (p1 ∨ (p3 ∨ p4))) ∨ ((p1 → p2) ∨ (((p3 ∨ True) → p2) → p1))) ∨ p1) ∧ (p5 ∧ (p2 → False))) ∧ p2)) → p3) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- Conjunctions on the left can always be decomposed.
        let h13 := h7.left
        let h14 := h7.right
        -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
        have h15 : p2 := by
          -- One of the premise coincides with the conclusion.
          exact h5
        -- We have shown the premise of h14, we can now drive its conclusion.
        let h16 := h14 h15
        -- False on the left can always be used.
        apply False.elim h16
      case inr h17 =>
        -- Disjunctions on the left can always be decomposed.
        cases h17
        case inl h18 =>
          -- Conjunctions on the left can always be decomposed.
          let h19 := h7.left
          let h20 := h7.right
          -- One of the premise coincides with the conclusion.
          exact h18
        case inr h21 =>
          -- Conjunctions on the left can always be decomposed.
          let h22 := h7.left
          let h23 := h7.right
          -- We want to use the implication h23 based on <expert-advice>. So we show its premise.
          have h24 : p2 := by
            -- One of the premise coincides with the conclusion.
            exact h5
          -- We have shown the premise of h23, we can now drive its conclusion.
          let h25 := h23 h24
          -- False on the left can always be used.
          apply False.elim h25
    case inr h26 =>
      -- Disjunctions on the left can always be decomposed.
      cases h26
      case inl h27 =>
        -- Conjunctions on the left can always be decomposed.
        let h28 := h7.left
        let h29 := h7.right
        -- We want to use the implication h29 based on <expert-advice>. So we show its premise.
        have h30 : p2 := by
          -- One of the premise coincides with the conclusion.
          exact h5
        -- We have shown the premise of h29, we can now drive its conclusion.
        let h31 := h29 h30
        -- False on the left can always be used.
        apply False.elim h31
      case inr h32 =>
        -- Conjunctions on the left can always be decomposed.
        let h33 := h7.left
        let h34 := h7.right
        -- We want to use the implication h34 based on <expert-advice>. So we show its premise.
        have h35 : p2 := by
          -- One of the premise coincides with the conclusion.
          exact h5
        -- We have shown the premise of h34, we can now drive its conclusion.
        let h36 := h34 h35
        -- False on the left can always be used.
        apply False.elim h36
  case inr h37 =>
    -- Conjunctions on the left can always be decomposed.
    let h38 := h7.left
    let h39 := h7.right
    -- We want to use the implication h39 based on <expert-advice>. So we show its premise.
    have h40 : p2 := by
      -- One of the premise coincides with the conclusion.
      exact h5
    -- We have shown the premise of h39, we can now drive its conclusion.
    let h41 := h39 h40
    -- False on the left can always be used.
    apply False.elim h41



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173657690346452502339180893630 : (((((p4 → True) ∧ ((False ∧ (((p1 ∨ p3) → p1) → p2)) → p4)) ∧ p3) ∨ p5) → (p2 ∨ (True ∨ (True ∧ ((p5 ∧ (p1 ∧ p1)) → p5))))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_974199811564240307502290941204 : ((((False → True) → (((False ∨ (p1 → (((((p4 ∨ p3) ∧ p3) → ((p3 ∧ False) → (p1 ∧ (p2 → p1)))) → p5) → p1))) ∧ p2) ∧ True)) → p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (False → True) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- One of the premise coincides with the conclusion.
  exact h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179337116416110739238497143745 : ((p1 ∨ ((False ∧ (False ∧ p4)) ∧ (((p4 → (p4 ∨ False)) → p5) ∧ p5))) ∨ ((p3 → (p4 → (p4 ∨ (True ∨ p5)))) → (True ∨ (True ∨ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39403656734025264314975502672 : (((p4 ∧ ((True ∧ ((p2 ∧ ((((p3 ∨ False) ∨ p4) ∧ p1) ∨ p2)) ∨ ((p3 → p4) ∧ (False ∧ (p1 ∨ True))))) ∧ (False → p3))) ∧ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_262347207978549809399470167743 : (True ∧ (((p1 → (p1 → (False ∧ p1))) ∨ ((p4 → ((p1 ∨ p4) ∧ p1)) → (((p4 ∧ (True → p4)) ∧ ((p3 ∧ p1) ∨ False)) ∨ True))) ∨ p5)) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50267444105664139302388448680 : ((((((p1 → False) ∨ p4) ∨ (False ∨ (((p4 → p4) ∧ p3) → ((p5 ∧ True) ∨ p4)))) ∧ (p3 → p5)) ∨ ((True → (p2 ∧ p5)) ∧ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57886106375422551024148228545 : (((p2 ∨ (p5 ∨ p3)) → ((False ∨ ((((p2 → (p1 → False)) → p3) → ((False → p3) → False)) → (p5 ∨ (p4 → p4)))) ∨ (True → False))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h7
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h8 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h9
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- One of the premise coincides with the conclusion.
      exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185695224305511423925083921941 : ((p1 → (p5 → (((p1 ∨ (p5 ∨ False)) ∧ (False ∧ p4)) ∨ p3))) ∨ ((p3 ∨ ((((False ∧ (p4 → p5)) ∨ p4) → (False → p3)) ∨ p2)) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119037551591825442411951609865 : ((p1 → (((p3 ∧ ((p2 ∧ ((p1 ∨ False) ∧ ((p5 ∧ p1) ∨ p3))) → (p1 ∨ p4))) → (((p3 ∧ p4) ∨ False) ∧ p2)) ∧ p4)) ∨ (p1 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66183576648281407883682585697 : ((p5 ∨ (((p4 → p1) ∧ ((True ∨ False) ∧ (((((p2 → p3) → (False ∧ p5)) → False) → p3) ∧ p3))) ∨ (p1 ∨ (p5 → (False → False))))) ∨ p1) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_16757854682833543897923525192 : ((((((p1 ∨ p5) ∨ (False ∨ False)) → ((((p5 ∧ False) ∧ p3) ∧ p2) ∧ p2)) → ((p4 ∨ p3) ∨ (True ∨ False))) ∨ ((p3 → p3) → False)) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56406588409056386544904948409 : ((((p4 ∨ (p5 ∨ False)) → p1) → ((True → ((p2 ∨ False) ∧ (p4 ∨ (p5 ∧ (p1 → ((p3 → (p1 → p1)) ∨ (p1 → p2))))))) ∨ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_151994557079564436332205550870 : (((((p5 ∧ p3) → ((p4 → p5) ∨ (p3 ∨ p3))) ∨ (p2 → True)) → ((((True ∨ p1) ∧ p5) → p4) ∧ p2)) → (p3 → ((False → p5) → p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h4 : (((p5 ∧ p3) → ((p4 → p5) ∨ (p3 ∨ p3))) ∨ (p2 → True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h4
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_610939039771780359356528974204 : (((((((p4 ∨ p3) ∨ (p4 → (p2 ∧ ((p5 ∨ p4) → True)))) ∨ (((p1 ∨ (p3 → (p2 ∨ p4))) → False) ∨ (p2 ∧ True))) → p1) ∨ True) ∨ False) ∧ True) := by
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
theorem thm_5_vars_736360479365265600150499910212 : ((((False → p5) ∧ ((p3 ∧ p1) ∨ ((((p3 ∧ False) ∧ ((False → p3) ∧ True)) → p5) → (((False ∨ True) ∧ False) ∨ (p3 → (p2 → False)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137326376372421987375849508301 : ((p2 ∧ ((p2 → False) → (p5 ∧ (p2 ∨ (False ∧ ((False ∨ False) ∨ ((False ∨ ((p1 ∨ p2) ∧ p4)) ∨ (p1 ∧ p5)))))))) ∨ (p4 ∨ (True ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_655009930336710022485546313962 : ((((((p5 ∨ p4) ∨ ((p4 ∧ (False ∧ ((p4 → (p1 ∧ ((((p3 ∧ True) ∧ True) ∨ p4) ∧ p1))) ∧ p4))) → True)) → False) ∨ (p2 ∧ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40303977388022207333334380280 : ((((((p4 ∧ (p1 ∨ (p4 → ((p3 → ((False ∧ ((False ∨ p1) ∨ (p5 → (True ∨ True)))) → p3)) ∨ True)))) → p5) ∧ True) ∨ True) ∨ p3) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_801141840253295000574021553219 : (((p2 → (((p5 ∧ ((True ∧ (((False ∨ p1) → ((p4 ∨ False) ∧ p2)) ∧ True)) ∨ p5)) ∨ (False ∨ p1)) ∨ ((p1 → (p1 ∧ False)) ∨ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_608702871213341073762640564860 : (((((((p2 ∨ ((p1 → ((((p5 ∨ False) ∧ True) → False) ∧ p4)) ∧ (False ∨ (p2 → p5)))) ∨ (p5 ∨ p5)) → (False ∧ p2)) ∨ True) ∨ False) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_68328310293997752518973879398 : ((p3 → ((p2 ∧ ((((p5 ∨ False) ∧ ((p5 ∨ p2) ∨ p3)) → (p3 ∨ p4)) → p4)) ∧ ((True ∨ p3) ∧ (((p5 ∨ True) ∨ p4) → p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_264297834203274874159247846805 : (True ∧ (((p3 → ((p1 ∧ p2) ∨ p1)) ∨ p3) → (p2 → ((p4 ∧ ((((p1 ∨ (p2 ∨ p1)) ∧ False) ∧ (p1 → (True ∧ p4))) ∨ True)) ∨ True)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
theorem thm_5_vars_674784445726931224255997568219 : ((((p4 → (((False → True) ∧ (((p2 ∧ True) ∨ ((p3 → p4) → (p4 ∧ False))) → True)) ∧ (p1 → (p2 ∧ False)))) → (p3 ∧ (p4 → False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158953450218409442571686876588 : ((p2 ∨ ((False ∨ p4) → ((p5 → p2) ∨ (p5 ∨ ((True ∧ p2) ∨ ((p3 → (p1 ∧ p4)) ∨ p3)))))) ∨ (False → ((p1 → p5) ∧ (False ∧ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351424344209966056252069383299 : (p4 → ((p2 ∨ ((False ∨ p4) ∧ (p3 ∨ ((((True → ((p3 → True) → True)) ∨ p3) ∧ False) ∧ (True → p1))))) ∨ ((p1 → (False ∨ p1)) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_673936716985907079590852440390 : (((((p5 → p1) → (((p1 → ((p2 ∨ (p5 ∧ p5)) → p5)) → (p4 → True)) ∨ ((p4 → (p1 → False)) ∧ p3))) → ((p2 ∧ p1) ∨ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48508746112618520169138312244 : (((((False → (p3 ∧ (((p2 ∨ (p1 → (p2 ∨ p2))) ∨ (False ∧ ((p4 ∧ p2) ∨ p4))) → p1))) → p2) ∨ True) ∧ ((p1 ∧ p1) → p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53281078722075880992391474763 : (((p4 ∧ (((((p2 ∧ False) ∨ p3) → p2) ∧ (p5 → p5)) ∧ p2)) ∨ (((((False → p1) ∧ True) ∧ p5) ∨ (p5 ∧ False)) → (p5 → p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345587563363513396587405025258 : (p3 → (((p2 ∧ p4) ∧ (True → (p2 → ((p3 ∧ (((p1 → ((p4 ∧ (p4 ∧ p4)) ∧ (p4 → p2))) ∧ p2) ∨ (p1 ∨ p2))) ∧ p4)))) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337341747153838128632111750130 : (p1 → (((True → (((p2 → (((p3 → True) ∧ p4) ∨ (p3 ∧ ((p5 → (p4 ∨ p1)) → p5)))) → p1) → p2)) ∧ p1) ∨ ((True ∧ p2) ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217235482331674907041939026666 : (((True ∧ (p2 ∧ p1)) ∨ p4) → (p2 → ((p5 ∧ (((p4 ∧ True) → ((((p4 → p3) ∨ p2) ∨ ((p5 ∨ p3) ∧ p2)) ∧ True)) → p5)) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_712578176729271327217593120319 : ((((((p2 ∨ p4) → True) → (False ∧ p4)) ∨ ((True → p1) → ((True → ((((p3 ∨ p5) ∧ p1) ∧ True) → (False → p4))) ∨ (p1 ∧ True)))) ∨ p3) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- False on the left can always be used.
  apply False.elim h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_122874005659534698241713721935 : (((((False ∨ p3) ∨ p3) ∧ (p1 ∨ ((p3 → True) ∧ (((True ∧ ((p4 ∧ True) → p4)) → p3) → p5)))) ∧ ((True ∨ p1) → p1)) → (p4 ∨ p1)) := by
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
      -- False on the left can always be used.
      apply False.elim h7
    case inr h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h9
      case inr h10 =>
        -- Conjunctions on the left can always be decomposed.
        let h11 := h10.left
        let h12 := h10.right
        -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
        have h13 : (True ∨ p1) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h3, we can now drive its conclusion.
        let h14 := h3 h13
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h14
  case inr h15 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h16 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h16
    case inr h17 =>
      -- Conjunctions on the left can always be decomposed.
      let h18 := h17.left
      let h19 := h17.right
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h20 : (True ∨ p1) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h21 := h3 h20
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h21



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52818270015576561171829967561 : (((((p3 → (p1 → p5)) ∧ False) ∨ (p3 ∨ (p4 ∨ ((p2 ∧ p5) ∨ False)))) → (((p5 ∧ p2) ∨ (p2 ∨ (p1 ∨ (False ∨ True)))) ∨ p4)) ∨ p5) := by
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
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
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
    case inr h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h8
      case inr h9 =>
        -- Disjunctions on the left can always be decomposed.
        cases h9
        case inl h10 =>
          -- Conjunctions on the left can always be decomposed.
          let h11 := h10.left
          let h12 := h10.right
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h11
        case inr h13 =>
          -- False on the left can always be used.
          apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57013115549627127973131985418 : (((False → (p1 ∨ False)) ∧ (((p4 ∧ False) ∧ (p5 ∨ p4)) ∧ (((p3 ∨ True) → p4) ∨ (True → (p2 ∨ (((p1 ∨ p5) ∧ p2) → False)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_221684220629879370928185158433 : (((True ∧ p2) → p2) ∧ (p1 ∨ ((((((p2 ∨ (False → p1)) ∨ ((True ∧ p3) ∧ p5)) ∨ True) → False) ∧ p2) ∨ (p1 ∨ ((p5 ∨ False) ∨ True))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h3
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
theorem thm_5_vars_337716724214561118370599368750 : (p1 → ((p5 ∨ ((p1 → (((p4 ∧ p2) → p4) ∨ ((p5 ∧ p5) → True))) ∧ (False ∨ (p2 ∧ p4)))) → (((p1 → (False ∨ p4)) ∧ False) ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- False on the left can always be used.
      apply False.elim h7
    case inr h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_183931770686951278165780917514 : (((p5 ∧ ((False ∨ (p4 → p3)) ∨ ((p3 ∨ p1) ∨ p5))) ∧ False) ∨ (((p4 ∨ (p1 ∨ (p2 → p4))) ∧ p4) → (p1 ∨ (p3 ∨ (p4 ∨ True))))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_320001063039018055603258778004 : (p4 ∨ ((False → (True → p3)) ∧ (p2 → (((False ∨ p3) ∧ ((p3 ∨ ((p4 → False) ∨ p4)) → p5)) ∨ ((p5 ∧ p4) → (p1 ∨ (False ∨ p2))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118530088811054049551232332737 : ((p3 ∨ (False ∧ (p4 ∧ ((p3 → (p4 ∨ ((p1 ∧ (((p2 ∨ ((p1 → p2) ∧ p1)) ∧ p4) ∨ (p1 ∧ True))) ∨ True))) ∧ p5)))) ∨ (p4 → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_760847593454798096306358206901 : (((p2 ∧ (p3 ∨ (((((((p2 ∧ (p3 ∧ p2)) ∧ (p4 → p2)) ∨ p5) → ((p4 → p4) → False)) ∧ p4) ∨ False) ∨ ((False ∧ p4) → p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351864573966981997438636055158 : (p4 → ((p5 → (((True ∧ p1) ∨ (((True ∧ p2) ∧ False) ∨ True)) ∨ p1)) → ((((p4 → p5) ∨ ((True ∨ (False ∧ p4)) ∨ p3)) ∨ p5) ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



