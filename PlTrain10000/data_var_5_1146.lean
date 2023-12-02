variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38729751023213372835472880169 : (((((p2 ∨ p2) → ((p2 ∨ False) ∨ True)) → ((((True ∧ ((p1 ∨ p3) ∨ p1)) ∧ p1) ∨ (p3 ∨ (p2 ∧ (p2 ∧ False)))) ∧ p1)) ∧ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_550920749151846356157839736016 : (((p1 ∨ (((p5 ∨ ((False ∧ p3) → ((p1 → True) ∨ p1))) → (True ∧ (False ∧ (p1 ∨ p1)))) → (((p4 ∧ (p2 ∧ p2)) ∨ p3) ∨ p4))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p5 ∨ ((False ∧ p3) → ((p1 → True) ∨ p1))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- False on the left can always be used.
    apply False.elim h4
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h2
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- We need to get the left conjuct of h7 based on <expert-advice>.
  let h8 := h7.left
  -- False on the left can always be used.
  apply False.elim h8
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149211670840823059948544732646 : (((False ∧ p3) ∨ (((((p5 → True) ∧ (p1 ∧ ((p2 → (False ∧ p1)) ∨ (False ∨ p5)))) → p5) ∧ p5) → p2)) ∨ (p5 → (False ∨ (True → True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309350162631950468172923046030 : (p2 ∨ (((p3 ∨ ((p2 ∨ True) → (p4 ∧ ((p4 ∧ (p5 ∧ (p1 ∧ p1))) → False)))) → (p3 ∧ (((p3 → False) → True) ∧ p5))) ∨ (p5 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_312454024138465768814175119010 : (p2 ∨ (p4 → (False ∨ (((True ∨ False) ∧ ((((False ∨ (p2 ∨ ((False ∨ p3) ∧ True))) → (p3 ∨ (p5 ∨ p2))) → (False ∧ False)) → p2)) ∧ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : ((False ∨ (p2 ∨ ((False ∨ p3) ∧ True))) → (p3 ∨ (p5 ∨ p2))) := by
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
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h7
      case inr h8 =>
        -- Conjunctions on the left can always be decomposed.
        let h9 := h8.left
        let h10 := h8.right
        -- Disjunctions on the left can always be decomposed.
        cases h9
        case inl h11 =>
          -- False on the left can always be used.
          apply False.elim h11
        case inr h12 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h12
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h13 := h2 h3
  -- We need to get the left conjuct of h13 based on <expert-advice>.
  let h14 := h13.left
  -- False on the left can always be used.
  apply False.elim h14
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181328520506582052701013062209 : ((True ∨ ((p4 ∨ p3) ∧ (p4 → ((p1 ∧ (p1 → p5)) ∨ (True → p1))))) → ((True → ((False → (p2 ∧ (False ∨ p1))) → (p2 ∧ p5))) ∨ True)) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159370037176537676151608688630 : ((((((p2 ∨ ((False ∨ (p5 → True)) ∧ p5)) ∨ ((p1 ∧ (True → p1)) → p3)) → True) ∨ p3) ∧ p2) → (((p4 ∨ p3) ∨ p2) ∨ (p4 ∧ p5))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149264957221718891707550633796 : (((p5 ∨ p3) ∨ (((((p2 ∧ p4) ∧ p2) ∨ ((p5 ∨ ((p4 ∧ (p4 ∧ p3)) ∨ p3)) ∨ p3)) → p5) ∧ p2)) ∨ ((False ∨ (False ∨ True)) ∨ p5)) := by
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
theorem thm_5_vars_147030010088705828737168519936 : (((((p2 → True) ∧ ((True ∨ (p1 ∧ (p1 ∧ p4))) ∧ ((False ∧ p5) ∨ p2))) ∨ ((p3 ∨ p4) ∧ p4)) ∧ p1) ∨ (((p4 ∨ True) ∨ p3) ∨ p1)) := by
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
theorem thm_5_vars_619761041887491797262073439426 : (((((False ∨ p3) ∧ ((False ∨ (((((((p3 ∧ p1) ∨ p4) → p4) ∨ p3) ∨ p1) ∨ (p4 ∧ p3)) ∨ p5)) ∨ ((p3 ∧ p3) → p1))) ∨ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_211723460697009643063916092100 : ((True ∧ (True ∨ (p4 ∧ p3))) ∧ ((True → (False ∧ ((p4 ∨ True) ∨ ((p2 → p3) ∨ False)))) → ((p4 ∧ p2) ∧ (((p3 → p4) ∧ p3) ∨ p3)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the left conjuct of h3 based on <expert-advice>.
  let h4 := h3.left
  -- False on the left can always be used.
  apply False.elim h4
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h5 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h5
  -- We need to get the left conjuct of h6 based on <expert-advice>.
  let h7 := h6.left
  -- False on the left can always be used.
  apply False.elim h7
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h8 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h9 := h1 h8
  -- We need to get the left conjuct of h9 based on <expert-advice>.
  let h10 := h9.left
  -- False on the left can always be used.
  apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313166567803079815840803696330 : (p3 ∨ (((((((True ∧ p3) → p2) ∨ False) ∨ (p3 → True)) → p4) ∨ (p2 → ((p2 → p3) ∨ (p5 ∨ ((p4 ∨ p5) → (p4 ∨ p5)))))) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347226537646220124941595686276 : (p3 → ((((p3 ∨ (p1 ∧ p2)) ∨ p1) ∧ (((p5 → p2) → False) ∨ p4)) → ((p1 ∨ p1) ∨ ((False → p5) ∧ ((p1 → p2) ∨ (p1 ∨ p3)))))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h7 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Implications on the right can always be decomposed.
        intro h8
        -- False on the left can always be used.
        apply False.elim h8
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h1
      case inr h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Implications on the right can always be decomposed.
        intro h10
        -- False on the left can always be used.
        apply False.elim h10
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h1
    case inr h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h14 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h12
      case inr h15 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h12
  case inr h16 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h17 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h16
    case inr h18 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314401928612883906860689309747 : (p3 ∨ ((((((p5 ∨ p1) ∧ p2) → ((False ∨ p2) ∧ p3)) ∧ (p1 ∧ ((p5 ∨ (p2 → False)) → p3))) ∧ p1) ∨ ((False ∧ p5) → (False ∧ p4)))) := by
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
  -- False on the left can always be used.
  apply False.elim h2
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47136584770769300742000898047 : (((((True → (((p1 ∨ p3) → ((p3 ∧ p4) ∧ (p3 ∧ p4))) ∧ (p5 ∧ True))) → False) ∧ ((p3 → (False ∧ True)) → p1)) ∨ (p4 → p4)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_740410915480135349437626564814 : ((((p1 ∨ p3) ∨ ((((p4 ∧ False) ∧ p1) ∨ False) ∨ (((p1 → p2) ∧ (p2 ∨ True)) ∨ (((True ∨ False) ∧ (p4 → (p2 → p3))) ∨ True)))) ∨ p5) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171588761704945825990543475600 : ((((p5 → ((p5 ∧ (p2 → (p5 ∧ p2))) ∧ p2)) ∧ ((p3 ∨ p4) ∧ True)) ∨ p2) ∨ (True ∧ (p2 → (p5 ∨ (p1 → (p3 → (False ∨ p1))))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44065504044176271711790114078 : (((((((p5 → (((p5 → p4) → p1) → (p1 ∧ False))) ∧ (p4 ∧ p4)) → ((p5 ∨ p4) ∧ p4)) → p3) ∧ ((p5 → False) ∧ p2)) → p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_343449951374017643047472009102 : (p2 → ((p5 ∨ p1) ∨ (((p2 ∧ p2) ∧ ((((p4 ∧ ((p1 ∧ p2) → p1)) ∨ ((p2 ∧ p2) ∧ False)) → p5) ∨ (True ∨ p2))) ∨ (p1 ∨ False)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227741111158364979959943655289 : ((p1 ∧ (p1 ∨ p3)) ∨ (False ∨ (((((((p5 → (p2 → (False → True))) ∨ p2) → p4) ∧ p3) ∨ ((p4 → p1) → True)) ∨ False) ∨ (p5 ∨ p2)))) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190938262869906587761642619285 : ((((p4 ∨ p1) ∧ (False → p2)) ∧ ((p1 ∧ True) ∧ p4)) ∨ (((p2 → ((p4 → p3) → p5)) ∨ (False → (((p5 → p2) → p4) → p3))) ∨ p1)) := by
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
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37966744001993175300132395656 : ((((((((False ∨ ((False ∧ p1) ∧ p1)) → ((p1 → True) ∧ (p2 ∨ p3))) ∧ (p2 ∧ p1)) → (p1 → p2)) → p1) ∨ (True → p4)) ∧ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166748644650920311337922476241 : ((p4 → ((p4 → (p3 ∧ (p2 ∧ True))) → (((p2 ∨ True) ∧ (p3 → p5)) ∧ (p2 ∧ p4)))) ∨ (True → ((p1 ∧ (True → (True ∨ False))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51843116491031900962290088234 : ((((((p1 → (p2 ∨ (((p5 → p3) → True) ∧ p4))) ∨ True) → (p5 ∨ p5)) ∧ p2) ∨ ((True ∧ True) ∧ ((p5 ∧ p3) → (p1 → True)))) ∨ p4) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158041218470785851485549699722 : ((((p2 ∨ ((p4 ∨ p2) ∨ p2)) ∨ p3) ∨ (p1 ∨ (False → ((True ∨ p5) → ((p4 ∨ p5) ∨ p3))))) ∨ (((p2 ∨ p3) → (False ∨ p5)) ∨ False)) := by
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
  cases h2
  case inl h3 =>
    -- False on the left can always be used.
    apply False.elim h1
  case inr h4 =>
    -- False on the left can always be used.
    apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_221001098803251682218763196554 : (((p3 ∧ False) ∨ True) ∧ ((p5 ∨ ((p4 ∧ (p4 ∧ False)) ∨ (p2 ∧ ((p3 ∨ p3) ∧ (p3 ∨ p5))))) ∨ (((p4 ∨ True) ∧ (p1 ∨ True)) ∨ p5))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113677274432318369108557502232 : ((((p3 ∧ ((False ∨ (True → p1)) ∧ (((p2 → ((p3 ∧ (False ∧ True)) ∨ p1)) → (p2 ∧ p3)) ∨ p3))) ∨ p1) → (False ∨ p4)) ∨ (p3 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307426129704753875363963909956 : (p1 ∨ (p5 ∨ ((p1 ∧ (((False → False) ∧ p2) ∧ ((False → (((False → p3) → p4) ∧ (p3 ∧ (p4 ∨ ((p4 ∨ p5) ∧ True))))) ∧ p2))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114366519004337285882893962594 : (((((p1 ∨ ((False ∧ (((p5 → p2) ∧ p1) ∨ p4)) ∧ ((p2 ∧ p1) ∨ p1))) ∨ p5) ∨ False) ∨ ((p4 ∧ (p5 ∧ p3)) ∧ p2)) ∨ (False ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_671298649565016335775011855735 : ((((p5 ∨ (p1 ∧ ((((p4 → p3) ∨ ((p2 ∨ p3) ∨ p4)) ∧ False) ∨ ((p2 → p2) ∧ ((p1 → True) → p4))))) ∨ (p3 ∧ (p1 ∧ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_727738254876259414345834586884 : ((((False ∨ (p3 ∧ p2)) ∨ ((p1 ∨ False) ∨ (((((p3 → p5) ∧ (True → (p4 ∧ ((p2 → False) ∧ p5)))) ∨ p3) → p1) → (p3 → True)))) ∨ p2) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_600564462246512098453135946698 : ((((True ∧ (p2 ∨ ((p5 ∨ (p5 → (p2 ∨ ((((False ∨ (p5 ∨ (p3 → p5))) ∧ True) ∧ ((p2 ∧ False) ∨ p5)) ∧ p3)))) ∧ p5))) ∧ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_19042774865094534888420650319 : (((((((p2 ∧ ((p4 ∧ p1) → p2)) → ((p1 ∧ p1) ∨ True)) ∨ True) ∧ (p4 ∨ True)) → p3) → (((p3 → False) ∧ (p1 ∨ False)) → False)) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h6 : p3 := by
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h7 : ((((p2 ∧ ((p4 ∧ p1) → p2)) → ((p1 ∧ p1) ∨ True)) ∨ True) ∧ (p4 ∨ True)) := by
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h8 := h1 h7
      -- One of the premise coincides with the conclusion.
      exact h8
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h9 := h3 h6
    -- False on the left can always be used.
    apply False.elim h9
  case inr h10 =>
    -- False on the left can always be used.
    apply False.elim h10
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_482260181873608428914028446300 : (((((p2 ∨ ((False → (p3 → p2)) → p1)) → p5) → ((True → ((p1 ∨ (p2 ∨ (p5 → ((True → p4) ∨ p5)))) ∨ (p4 → True))) ∨ True)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60702645469940354744462853982 : ((True ∧ (((((p4 ∨ False) → False) → p5) ∧ (p1 ∨ p1)) ∧ ((((p4 ∧ p3) ∨ (p2 ∨ (True ∧ p2))) ∧ p1) ∧ (p1 ∧ (True ∧ p2))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304041056480535294561424851060 : (p1 ∨ ((p4 ∧ (((((p4 ∨ ((p5 ∨ p1) ∨ p2)) ∨ ((False ∨ True) ∨ (True ∧ p1))) → (p1 ∨ (p2 ∧ p5))) → p5) ∨ (False ∨ True))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136930897951102996030761698469 : (((p2 → p5) ∨ (((True ∨ ((p2 ∨ ((p5 → p5) ∧ False)) → p3)) ∨ p3) → (p4 ∨ ((p3 ∧ (p4 ∧ p4)) ∨ True)))) ∨ (False → (p4 → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116722264019806591639101704753 : (((p2 ∧ p4) ∨ ((p4 ∨ (p4 → (p3 ∧ p5))) ∨ ((True ∧ p5) ∨ (p2 ∨ ((p4 ∨ p3) → (False ∨ ((p2 ∧ p3) ∨ p4))))))) ∨ (p4 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49145906173224580503828421965 : (((((p4 ∧ False) → (False → ((p1 → (p3 → True)) ∧ p3))) → (p1 ∧ (((p1 ∧ p3) ∨ (True ∨ p4)) ∧ p4))) ∨ ((p5 ∧ p4) → True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307314566561223998478746581687 : (p1 ∨ (p3 ∨ ((False ∨ (True → (p5 → (((((p1 ∧ p3) ∧ (False ∨ p4)) ∨ p5) ∧ (p4 ∨ p4)) ∨ ((p2 ∧ p5) ∨ p5))))) ∨ (p2 ∧ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341742216001026418088281630720 : (p2 → ((True ∧ ((((((True ∧ p5) → (p3 ∨ False)) ∧ (p1 → (p4 ∨ (p1 ∧ p5)))) ∧ True) ∨ ((True → True) ∧ p2)) → p5)) ∨ (p3 → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136108859852650828018172776304 : (((((False → p3) ∧ p1) → (p1 → (p3 → p2))) ∨ ((True ∧ p4) → ((False → ((False → False) ∨ (p2 ∨ False))) → p2))) ∨ ((True ∨ p2) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193572453950975704409253160068 : (((p2 ∨ p5) → (False → (p1 → ((p4 ∨ p2) ∧ p3)))) → (((((p2 → (p4 → (p5 → ((p5 ∧ p1) → p5)))) → p4) ∨ p5) ∧ p3) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_636921186081585187465608386062 : ((((((((((p4 → (False ∧ p2)) ∧ p4) ∧ True) ∧ p2) ∨ False) ∧ p4) ∧ (True ∨ (((p5 ∨ (p5 ∨ True)) → (p4 → p4)) → True))) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41992767643754932590997888359 : ((((True → p2) ∧ ((p4 → p3) → (((p2 → p2) ∧ p4) ∨ ((True → (p2 → (((True ∨ False) ∨ True) ∧ (p4 ∧ p4)))) ∨ p2)))) ∨ True) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64504356718248068356023134755 : ((p1 ∨ ((((False → p5) ∧ (((p4 ∧ False) ∨ p4) ∧ (True ∨ True))) → (True → False)) ∨ (True ∧ ((p5 ∧ False) ∧ (p3 ∧ (p2 ∨ p1)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50935872574416031431398186080 : (((((False ∨ ((p1 ∧ p1) ∧ p5)) → ((True → p3) → p5)) ∧ ((p3 → (p2 ∨ True)) → False)) ∧ (((True ∧ p1) ∨ (p2 ∧ p3)) → p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215308129024214221128913027769 : ((p1 ∧ ((p5 ∧ True) → False)) ∨ ((((False ∨ (((p4 ∨ (p4 ∧ p5)) → True) → p5)) ∧ p2) ∧ p5) → ((p3 ∧ (p5 → p4)) ∨ (p4 → p2)))) := by
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
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_784417315162653092120839967804 : (((p3 ∨ (p4 ∧ ((p2 ∨ (False ∧ (p1 → (p4 ∨ (True ∨ (p2 ∨ (p2 ∧ (p1 → (False ∧ (False → p3)))))))))) ∧ ((p1 → p2) → True)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_329150467911924387269028158226 : (True → ((((p3 ∨ True) ∨ p2) ∨ p1) → (((p5 → (p3 → p2)) ∨ p4) ∨ (((p2 ∧ ((p3 → p3) → (True ∨ (False ∨ True)))) ∨ True) ∨ p2)))) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h5 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h6 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h7
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_588293929227119987625921447805 : ((((((p1 ∧ ((p5 ∧ p5) ∧ (p4 ∨ p1))) → ((True ∧ (False ∧ ((False → p3) ∨ False))) ∨ ((False ∨ (p4 → True)) ∧ p3))) ∨ p2) ∧ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_306047877353887263853844969947 : (p1 ∨ (((p3 ∨ p5) ∧ (p5 ∨ p2)) → ((((((p5 → False) ∨ ((True ∨ (p5 ∧ p4)) ∧ False)) ∨ (False → p1)) → False) ∧ (p3 → p1)) → p3))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h9 =>
      -- One of the premise coincides with the conclusion.
      exact h7
  case inr h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h11 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h12 : (((p5 → False) ∨ ((True ∨ (p5 ∧ p4)) ∧ False)) ∨ (False → p1)) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h13
        -- False on the left can always be used.
        apply False.elim h13
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h14 := h3 h12
      -- False on the left can always be used.
      apply False.elim h14
    case inr h15 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h16 : (((p5 → False) ∨ ((True ∨ (p5 ∧ p4)) ∧ False)) ∨ (False → p1)) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h17
        -- False on the left can always be used.
        apply False.elim h17
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h18 := h3 h16
      -- False on the left can always be used.
      apply False.elim h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_787736278582824236597772469657 : (((p4 ∨ (True → ((p4 → ((False ∨ (((((True ∨ p1) ∧ False) → p5) → p2) ∧ p3)) ∧ ((True → (p5 ∨ (p3 ∨ p4))) ∧ False))) ∧ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_69325311358001163182611088234 : ((p5 → (p5 ∧ (((((p1 ∨ p5) → True) ∧ ((p2 ∧ ((p1 → (p2 ∧ p3)) ∨ p1)) → p5)) ∨ True) → ((p4 ∨ p1) ∨ (p1 ∨ True))))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
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
theorem thm_5_vars_687991616238434447024570602558 : ((((((p4 ∧ p5) ∧ ((p2 → p1) ∧ p5)) ∧ (p2 ∧ ((p4 ∧ p1) → (p2 → p1)))) ∧ ((p4 ∧ p4) ∨ (p4 → (True ∨ (False → True))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58776245016477938563469517039 : (((p4 → p4) ∧ ((((((((False ∧ p5) ∨ False) → p5) ∨ p3) ∨ ((((True ∧ (p3 ∧ False)) ∧ p5) → False) → p2)) → p4) ∨ p1) ∧ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148047450859817360634980620227 : (((p3 ∧ ((((((p3 ∨ True) → (p3 ∨ p3)) ∧ p4) ∨ p2) ∨ (p1 → p4)) → (True → p4))) ∨ (p2 ∨ p2)) ∨ (((p4 ∧ p1) ∧ False) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44088122232880891638149118161 : ((((p1 ∧ ((((False ∧ (p4 ∧ p2)) → p3) ∨ True) → (p1 ∧ ((p5 → (False → p1)) ∧ (False ∨ p5))))) ∧ ((False → p3) ∨ p2)) → p5) ∨ p5) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h6 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h7 : (((False ∧ (p4 ∧ p2)) → p3) ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h8 := h5 h7
    -- We need to get the right conjuct of h8 based on <expert-advice>.
    let h9 := h8.right
    -- We need to get the right conjuct of h9 based on <expert-advice>.
    let h10 := h9.right
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- False on the left can always be used.
      apply False.elim h11
    case inr h12 =>
      -- One of the premise coincides with the conclusion.
      exact h12
  case inr h13 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h14 : (((False ∧ (p4 ∧ p2)) → p3) ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h15 := h5 h14
    -- We need to get the right conjuct of h15 based on <expert-advice>.
    let h16 := h15.right
    -- We need to get the right conjuct of h16 based on <expert-advice>.
    let h17 := h16.right
    -- Disjunctions on the left can always be decomposed.
    cases h17
    case inl h18 =>
      -- False on the left can always be used.
      apply False.elim h18
    case inr h19 =>
      -- One of the premise coincides with the conclusion.
      exact h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_357125978110000355716041717120 : (p5 → ((p5 → (p5 → False)) → (((p3 → ((False ∧ ((p3 ∨ False) → p2)) ∧ p3)) → ((((p1 ∧ (p3 ∨ p1)) → p2) → p4) ∨ p1)) ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342508712124483013605126547784 : (p2 → ((((p4 ∨ (p4 → False)) ∧ (False ∧ (p2 ∧ ((p1 ∧ p4) ∧ p1)))) → p1) → ((((p2 ∧ (p3 ∨ (p3 → p4))) ∨ p5) ∧ p1) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137779463859172676740137889382 : ((p2 ∨ ((False ∨ (p4 ∧ (True ∧ p5))) ∧ (((p5 ∧ (p1 → ((p4 ∨ (False → p5)) ∨ (p4 → True)))) ∨ True) → p1))) ∨ ((p4 ∧ True) → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116798193139530226215157405072 : (((p2 ∨ p3) ∨ (p5 ∧ ((p1 ∨ (((p5 ∨ (p1 ∧ True)) → (True ∨ (p5 → False))) ∨ (p5 ∨ ((p4 → p2) → p2)))) → False))) ∨ (False → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310253027886534804665562423269 : (p2 ∨ ((p2 ∨ (((p2 → p5) ∧ p3) → ((p4 ∨ True) ∨ (p3 → p5)))) → ((p5 ∧ p1) ∨ (((((p4 ∧ False) ∨ p2) ∧ p3) → True) ∨ p2)))) := by
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
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h4
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_614451267101353051741083584942 : (((((((p5 ∨ False) ∨ (((((p5 ∧ p3) ∨ ((p4 → p1) → p3)) ∧ p2) ∨ False) ∧ p5)) ∧ p3) ∧ (((True → False) ∧ p1) ∨ p4)) ∨ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_175875618102060644359573666514 : ((((((p3 → p4) ∧ False) → (p2 ∧ False)) → (p2 ∧ (p1 ∨ p1))) ∨ True) ∧ (True ∨ (p5 ∧ (((True ∧ (p4 → p5)) ∨ p2) → (p5 ∧ p3))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48935970557851904141320591974 : (((((True ∧ (p2 ∧ (False → ((False ∨ p5) → (p5 → p2))))) ∧ (((True ∨ p4) → p5) → (p2 ∧ False))) ∧ p3) ∨ (True ∨ (False ∨ p1))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_607013869108451262328844016638 : ((((((((p4 ∨ (((False ∧ (False ∨ p5)) → p2) → p1)) → False) → p4) ∧ (True ∧ (((False ∧ (False → p5)) ∨ p4) ∧ p5))) ∧ p1) ∨ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_784999026788218071827337208484 : (((p3 ∨ (p5 → (((False ∧ (p5 → p2)) ∨ (((p4 ∨ (((p1 ∨ True) → False) → p2)) ∧ ((True ∧ p3) ∨ p3)) ∨ (True ∨ p5))) ∨ True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187451413913020508122467453431 : ((True ∨ (((p3 ∨ (p3 ∨ False)) → ((p2 ∧ p3) ∧ p5)) → p1)) → (((((p1 → (True ∧ p2)) ∧ (True ∨ False)) ∧ p2) ∨ False) ∨ (True ∨ True))) := by
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
theorem thm_5_vars_48318160491243839559374826850 : (((False ∨ (p2 ∧ ((p2 → True) → ((((p1 ∨ (p2 ∨ p5)) → (p1 → True)) ∧ (p3 → p1)) ∨ ((p2 ∨ p5) ∨ p1))))) → (p4 ∨ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_306496151725363158355887442879 : (p1 ∨ ((p3 → p4) ∨ ((p3 → (p1 ∨ ((((p4 ∨ ((False ∨ ((p5 → False) → True)) ∨ p5)) ∨ True) ∧ p5) ∧ p2))) ∨ (p5 ∨ (True ∨ p1))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171697567077964572863629164705 : (((p1 → ((p3 ∧ ((((p3 ∨ True) → (False ∨ p3)) ∨ True) ∧ True)) ∧ p1)) ∨ p2) ∨ (p3 → ((((p3 → p5) ∧ (False ∨ p1)) ∨ p3) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178773261174524083381943532694 : (((p3 ∧ (False → True)) ∧ (False ∨ ((((p3 ∧ p5) → True) ∧ p3) → False))) ∨ (p3 ∨ (p5 ∨ (((p4 ∨ p5) ∨ (True → p2)) ∨ (True ∧ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167856180916693028609494428143 : (((True → (((p2 → (True ∧ p1)) → (p1 → p2)) ∨ True)) ∨ (p1 ∧ (p1 ∨ (p2 ∧ True)))) → (p3 → (((p1 ∨ p4) → p5) ∨ (True ∨ p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204934434488130203059541630243 : ((((p3 ∧ False) → (False ∨ False)) → p2) ∨ (((p5 → ((p3 → False) ∧ ((p3 → False) → ((p2 ∧ (False ∧ (p5 ∧ p2))) ∧ p4)))) → p4) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256032348097253831981600095338 : ((True ∨ p4) → (((p4 ∧ (((p4 ∧ False) → (p1 ∧ p2)) ∧ False)) ∨ (p5 ∨ (p1 ∧ (((((p3 → p3) ∨ p3) ∨ p1) → p4) ∨ p4)))) ∨ True)) := by
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
theorem thm_5_vars_114542537402166686250639639331 : (((p5 → (False ∨ ((p5 ∨ (((p3 ∨ False) ∧ p1) ∨ (p5 ∨ False))) ∨ ((False ∨ p2) ∧ False)))) → (((p1 → True) ∧ p1) ∧ p3)) ∨ (True ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46246267495358092372714197176 : ((((True → ((((p5 ∧ p5) → ((p2 → p4) → ((p5 → (True → p1)) ∨ p1))) → p1) → (p4 ∨ p4))) ∨ (p3 → p5)) ∧ (p1 → True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48620909411166872134710591705 : ((((p4 → ((False → (((True ∧ False) → (p2 → p4)) ∨ True)) ∧ (p3 ∧ ((p5 ∨ p2) → p2)))) → (False ∧ True)) ∧ ((False → p2) ∨ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134459872693319612340336813245 : ((((((p2 ∧ p5) → (p5 ∧ True)) ∧ (p1 ∨ ((((p1 ∧ p1) ∧ (p1 ∨ False)) → (p1 ∨ p5)) ∨ False))) ∧ True) → p5) ∨ ((p2 → p1) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_727774101422518173156933315873 : ((((False ∨ (True → False)) ∨ (p4 → (((((p3 → (False ∧ p3)) ∧ p4) → (((p4 → p1) ∧ p3) ∧ (p2 ∧ p4))) ∧ p5) ∨ (p4 ∨ p3)))) ∨ False) ∧ True) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_682727787616077964788371205386 : (((((((p4 ∨ p3) ∨ True) ∧ p4) ∨ (p2 ∧ ((p1 ∨ p1) ∨ ((p1 → p5) → (p5 → p1))))) ∧ ((True ∧ p1) → ((p4 ∧ p2) ∨ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_809822419096486415339739477115 : (((p5 → ((((p3 → ((((p3 ∧ (p5 → False)) ∨ p3) ∧ (p4 ∨ p4)) → (p5 → p2))) → ((p1 ∧ p2) ∨ p3)) ∧ p4) → (False ∨ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149118852987183001187538593334 : (((False ∧ p4) ∧ ((False ∨ (p1 → ((False ∧ ((p1 ∨ p4) ∧ p5)) ∧ (False ∧ (True ∨ (p5 ∨ True)))))) ∨ p5)) ∨ (((p1 ∧ p4) → False) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158241413416938198192902790076 : ((((p3 ∨ False) ∧ p5) ∨ (((((True ∧ False) ∧ p2) ∧ p3) ∧ (True ∧ ((p5 ∧ False) ∨ p4))) ∧ p3)) ∨ (p4 → (False ∨ ((p2 ∨ p4) ∧ True)))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42320482938369440298213227151 : (((p2 ∧ (p5 ∧ ((((p2 ∨ (p5 → p1)) ∧ (True → p1)) ∨ ((p1 ∨ (p4 ∨ (p1 → (p5 ∨ p4)))) ∧ (p4 ∧ True))) ∨ p1))) ∨ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_656574461627393718515935927987 : ((((((p1 → ((p5 ∧ (p2 ∨ p2)) ∧ True)) ∧ p4) ∨ (False ∨ ((True ∧ p2) ∧ ((False ∨ p5) ∧ ((True ∧ p2) ∨ p3))))) ∨ (True ∨ True)) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213555390925238092131926354174 : ((((p5 ∧ p4) ∧ p1) ∨ p2) ∨ (p1 ∨ (p4 ∨ ((p3 → p4) → (p1 → (((False ∧ p2) ∧ ((p3 ∨ False) ∧ (True → True))) → (False ∨ p1))))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207045198771976926016758480765 : (((True ∧ ((p3 ∧ p3) ∧ p2)) ∧ p1) → ((((p5 → p4) → ((p4 ∨ p5) ∧ (False ∨ (p3 → (False → p3))))) ∧ (p4 ∧ p3)) ∨ (p1 ∨ p1))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158190972948046976069233812804 : (((p3 → ((True ∧ p3) ∧ p4)) → (p2 ∧ (p1 ∨ (p1 ∨ (((p1 ∨ p1) → (p4 → p4)) ∨ p2))))) ∨ (((p1 → p1) ∧ (False → p5)) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218039341325802679915610693008 : (((p2 ∨ True) ∧ (True → p2)) → (p4 ∨ ((p2 ∨ (p1 → ((False ∨ p2) ∨ p3))) ∨ ((p5 ∨ p3) → (p3 ∨ (p4 ∨ ((p4 ∨ p4) ∧ False))))))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h6 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h7 := h3 h6
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186609881505101842290366977416 : (((((p2 → p2) ∧ True) ∧ (False ∨ (p4 → p3))) → (p1 ∧ p1)) → (((p2 → p1) ∨ True) → (((True ∨ (p1 ∨ False)) ∧ p3) → (p4 → p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h8 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h9 : (((p2 → p2) ∧ True) ∧ (False ∨ (p4 → p3))) := by
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Implications on the right can always be decomposed.
        intro h10
        -- One of the premise coincides with the conclusion.
        exact h10
        -- True on the right can always be proven directly.
        apply True.intro
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h11
        -- One of the premise coincides with the conclusion.
        exact h6
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h12 := h1 h9
      -- We need to get the left conjuct of h12 based on <expert-advice>.
      let h13 := h12.left
      -- One of the premise coincides with the conclusion.
      exact h13
    case inr h14 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h15 : (((p2 → p2) ∧ True) ∧ (False ∨ (p4 → p3))) := by
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Implications on the right can always be decomposed.
        intro h16
        -- One of the premise coincides with the conclusion.
        exact h16
        -- True on the right can always be proven directly.
        apply True.intro
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h17
        -- One of the premise coincides with the conclusion.
        exact h6
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h18 := h1 h15
      -- We need to get the left conjuct of h18 based on <expert-advice>.
      let h19 := h18.left
      -- One of the premise coincides with the conclusion.
      exact h19
  case inr h20 =>
    -- Disjunctions on the left can always be decomposed.
    cases h20
    case inl h21 =>
      -- Disjunctions on the left can always be decomposed.
      cases h2
      case inl h22 =>
        -- One of the premise coincides with the conclusion.
        exact h21
      case inr h23 =>
        -- One of the premise coincides with the conclusion.
        exact h21
    case inr h24 =>
      -- False on the left can always be used.
      apply False.elim h24



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192054759914895766718979008184 : ((p3 → ((((p1 ∧ p4) ∧ (p5 ∧ p2)) ∨ False) ∨ p3)) ∨ (((p4 → (p4 → (False ∨ ((p5 → ((p4 ∧ p2) → p1)) → p1)))) ∧ p4) ∧ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_619322716383935742012417261021 : ((((((False → p3) ∨ p2) → (p2 ∧ ((((False → p5) ∨ p5) → (p5 ∧ (p2 ∨ ((p2 → (p2 ∧ True)) ∧ (False → p1))))) → p4))) ∨ True) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_734498219570779705725960499727 : ((((p1 ∨ False) ∧ (((((p3 → True) ∨ p4) ∧ ((p2 ∧ p3) ∧ (p5 ∧ (((p1 ∧ p3) → p5) ∧ p5)))) ∨ p4) ∧ (p3 → (p1 ∨ p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180252883634312435603556707041 : (((p1 ∨ (p2 ∧ (False ∧ ((p2 → p3) ∨ (False ∧ (p5 ∧ p3)))))) → p5) → (p2 ∨ ((p2 → p3) ∨ ((((False ∨ False) ∧ p3) → p4) ∨ p2)))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- False on the left can always be used.
    apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324535173805145655244192649199 : (p5 ∨ ((((p5 → p5) → False) → p2) → (((p5 ∧ ((p4 ∨ (p1 → p5)) ∨ p3)) ∧ True) ∨ (p3 → (False ∨ (((p5 ∧ p4) ∨ p4) → p3)))))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h7 =>
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354587359581219865456680493301 : (p5 → (((p1 ∧ (((p5 ∧ (p3 ∨ (p3 → p2))) → p1) → ((((p3 → (p5 → False)) → (p5 ∧ False)) ∨ (p4 ∧ p1)) ∨ True))) ∧ p5) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56940453592251571769411100928 : (((False ∨ (p2 → p4)) ∧ (((((((True ∧ False) ∧ p3) ∧ ((p4 ∨ p5) ∧ True)) ∧ p3) ∧ p5) ∧ p1) ∧ ((False → p5) → (p2 ∧ True)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198315448630249200755367912341 : ((p1 ∧ (p2 ∧ (((True ∨ p4) ∨ False) ∧ False))) ∨ (p1 ∨ ((p5 → p4) ∨ (((False ∨ (p2 ∨ True)) ∨ p2) ∨ (p4 → ((True ∧ p4) ∧ p4)))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



