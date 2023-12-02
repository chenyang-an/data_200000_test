variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52943530465118874537800374272 : (((((((p2 → p1) ∨ (True ∧ p2)) ∨ (p2 ∨ p2)) ∨ p3) ∨ True) ∧ (((False ∧ (p4 → (((p5 ∨ p5) ∧ p1) → False))) ∨ p1) → p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52645078266096454448606418353 : ((((p1 → p4) → ((False ∨ ((p1 ∧ False) ∧ (p4 ∨ (True → False)))) ∨ p4)) ∨ ((((p5 ∨ ((p2 ∨ p5) ∧ p4)) ∧ p2) ∧ p1) ∨ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165900603654255808549072593610 : (((True ∨ (p2 → p1)) → (p5 ∨ (p4 ∨ ((p1 → ((p5 → (p2 ∨ p1)) ∨ p2)) ∧ False)))) ∨ (True ∨ ((False ∨ ((p5 ∨ p1) ∨ p1)) ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174495324963387062975329716877 : ((((((p2 → p4) ∨ p4) ∨ p3) ∨ p5) ∨ (p5 ∨ (p3 → ((p2 → p4) ∨ p4)))) → (p3 ∨ (p2 ∨ (((p2 ∧ (False → True)) ∨ True) ∨ p2)))) := by
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
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h7 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h7
    case inr h8 =>
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
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
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
    case inr h11 =>
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
theorem thm_5_vars_227937918065834993513937395781 : ((p3 ∧ (p1 ∧ p3)) ∨ (False ∨ (((p1 → ((True → (((p1 ∧ False) → (False ∧ (True ∨ p4))) ∧ ((p3 ∨ p5) ∨ p1))) ∨ p2)) ∧ False) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46844563804590973685749885811 : (((((((p2 → p1) ∨ True) ∨ p4) → (((True ∧ (False → p2)) → (((p1 ∨ p4) ∧ (p4 ∧ True)) → p1)) ∧ True)) ∧ p3) ∨ (True ∨ False)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_595501157244511632378807510198 : ((((((p4 ∨ p4) ∨ (p1 ∨ (p5 ∨ (((p2 ∧ p5) ∧ True) ∨ True)))) ∨ ((((False ∨ p1) → (p2 ∨ p4)) → (False ∨ p4)) ∧ p3)) ∧ True) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_175180812951105511104249306305 : ((True ∨ (True ∨ ((p4 ∧ (p4 → (((p1 ∧ p4) ∧ p1) → (False ∧ False)))) ∧ True))) → (p3 → (((p5 ∧ (p2 ∧ p3)) ∨ (False → p5)) ∨ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
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
      -- Implications on the right can always be decomposed.
      intro h7
      -- False on the left can always be used.
      apply False.elim h7
    case inr h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Conjunctions on the left can always be decomposed.
      let h11 := h9.left
      let h12 := h9.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h13
      -- False on the left can always be used.
      apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_348981654215042695923792224034 : (p3 → (p4 ∨ ((((p4 ∧ p4) → (False ∧ (((True → True) → (p4 ∧ (p5 ∨ ((p3 ∧ p1) ∨ (True → p2))))) ∨ False))) ∨ p1) ∨ (True ∨ False)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152292772094242346717956797994 : (((p5 ∧ (((p4 ∨ p3) ∨ p1) ∨ p4)) → (((p3 ∧ (p2 ∨ p4)) → ((p5 ∧ p2) ∨ (True ∧ True))) → p5)) → ((p4 → False) → (p4 → p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : p4 := by
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_705423156881935094476467740181 : (((((True ∨ ((p1 ∨ p5) ∨ (p4 ∧ p5))) ∨ p5) ∧ (((p5 ∨ p3) → p5) ∧ (p2 → (((p2 → (p2 → p4)) ∨ p1) ∧ (p3 ∧ False))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115386103136931729601174425428 : ((((True ∨ p5) ∧ (p5 ∧ ((True → p4) ∨ p2))) ∧ (((True → p5) → (True → ((p1 ∧ (p4 ∧ True)) → p4))) → (p4 → False))) ∨ (p4 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_705565848842842446836610751616 : ((((((p5 ∨ p1) ∨ ((p2 ∨ True) ∨ p4)) → p2) ∧ ((p5 → ((((p2 ∨ p3) ∨ p4) ∧ ((p1 → p4) ∧ (p5 ∨ p2))) → p2)) ∧ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_201008977879451420118938756981 : ((p3 ∨ (p5 ∧ (p3 ∨ (p5 ∨ (p4 ∧ p3))))) → ((True ∧ ((p2 → ((p1 ∧ p4) → False)) ∨ (p5 ∨ (((True ∧ p2) ∨ True) ∨ p1)))) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
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
  case inr h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
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
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
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
        -- One of the premise coincides with the conclusion.
        exact h8
      case inr h9 =>
        -- Conjunctions on the left can always be decomposed.
        let h10 := h9.left
        let h11 := h9.right
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
        -- One of the premise coincides with the conclusion.
        exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112143199823037011945176402752 : (((p1 ∧ (((((p2 ∨ p1) ∧ p2) ∨ (True → False)) ∧ (p3 → ((False ∧ p5) ∨ ((True ∧ p4) ∧ p1)))) ∨ (p5 ∨ p1))) ∨ p1) ∨ (p2 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340229809310597707271250442533 : (p1 → (p5 → ((False ∨ (((p1 ∧ (p1 ∧ (p2 ∨ p5))) → ((p1 ∨ (p2 → True)) → p2)) ∨ p2)) ∨ (((True → p3) → p1) ∨ (True ∨ p3))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_809747036751605456387214710596 : (((p5 → ((((True ∧ p1) ∨ ((True → ((p2 → (p4 → ((True → False) ∨ ((p1 ∧ p5) ∧ False)))) ∨ p1)) → p1)) ∧ p5) ∨ (True → True))) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_801024583585029295944659694004 : (((p2 → (((True ∨ (p1 ∧ (((((p1 ∨ (p1 → False)) → p5) → (p5 → (p1 ∧ True))) ∧ p4) → p4))) → p4) ∨ (p2 ∨ (p5 → p1)))) ∨ p1) ∧ True) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_786788295360653552889241848844 : (((p4 ∨ ((((p1 ∧ p4) ∧ p4) ∧ p2) → (((False ∨ (p5 ∨ ((p5 ∨ True) → ((False → ((p5 ∨ p1) ∨ False)) ∧ False)))) ∨ p1) ∨ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_699887175017258121229786164281 : (((((((p2 ∨ (p5 ∧ p2)) ∨ p4) → True) ∨ ((p4 ∨ p2) ∨ p5)) → (((p4 → p1) ∨ ((((p2 → p4) ∨ p5) ∨ p3) ∧ False)) ∨ True)) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_394532043996611155867763928425 : (((((p2 → False) → (((((p3 ∧ ((p1 ∨ p5) ∨ p3)) → p3) → ((((True ∨ p4) → p3) → p1) ∧ p2)) ∧ p1) → (p2 ∧ p3))) ∨ p2) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h5 : ((p3 ∧ ((p1 ∨ p5) ∨ p3)) → p3) := by
    -- Implications on the right can always be decomposed.
    intro h6
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h8
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
      exact h12
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h13 := h3 h5
  -- We need to get the right conjuct of h13 based on <expert-advice>.
  let h14 := h13.right
  -- One of the premise coincides with the conclusion.
  exact h14
  -- Conjunctions on the left can always be decomposed.
  let h15 := h2.left
  let h16 := h2.right
  -- We want to use the implication h15 based on <expert-advice>. So we show its premise.
  have h17 : ((p3 ∧ ((p1 ∨ p5) ∨ p3)) → p3) := by
    -- Implications on the right can always be decomposed.
    intro h18
    -- Conjunctions on the left can always be decomposed.
    let h19 := h18.left
    let h20 := h18.right
    -- Disjunctions on the left can always be decomposed.
    cases h20
    case inl h21 =>
      -- Disjunctions on the left can always be decomposed.
      cases h21
      case inl h22 =>
        -- One of the premise coincides with the conclusion.
        exact h19
      case inr h23 =>
        -- One of the premise coincides with the conclusion.
        exact h19
    case inr h24 =>
      -- One of the premise coincides with the conclusion.
      exact h24
  -- We have shown the premise of h15, we can now drive its conclusion.
  let h25 := h15 h17
  -- We need to get the right conjuct of h25 based on <expert-advice>.
  let h26 := h25.right
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h27 : p2 := by
    -- One of the premise coincides with the conclusion.
    exact h26
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h28 := h1 h27
  -- False on the left can always be used.
  apply False.elim h28
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204560663946837245953506545993 : ((((False ∧ False) ∧ (True ∨ p3)) ∨ False) ∨ (((p1 → (p4 → (p2 → (False → p5)))) → p3) ∨ ((False ∨ (p3 → True)) ∧ (True ∨ (p4 → p5))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_124105235811042129079241633312 : ((((p5 ∧ ((p1 → ((p5 ∧ p3) → p4)) → True)) → True) ∧ ((((p2 → ((p2 ∨ p4) → p2)) → p1) ∧ (p1 → p2)) ∧ p4)) → (p4 ∧ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- One of the premise coincides with the conclusion.
  exact h5
  -- Conjunctions on the left can always be decomposed.
  let h8 := h1.left
  let h9 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h10 := h9.left
  let h11 := h9.right
  -- Conjunctions on the left can always be decomposed.
  let h12 := h10.left
  let h13 := h10.right
  -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
  have h14 : (p2 → ((p2 ∨ p4) → p2)) := by
    -- Implications on the right can always be decomposed.
    intro h15
    -- Implications on the right can always be decomposed.
    intro h16
    -- Disjunctions on the left can always be decomposed.
    cases h16
    case inl h17 =>
      -- One of the premise coincides with the conclusion.
      exact h15
    case inr h18 =>
      -- One of the premise coincides with the conclusion.
      exact h15
  -- We have shown the premise of h12, we can now drive its conclusion.
  let h19 := h12 h14
  -- One of the premise coincides with the conclusion.
  exact h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197673308305055770121047688089 : (((True ∧ ((p1 → p1) ∨ p4)) → (p1 ∧ True)) ∨ ((p3 ∨ (((p3 ∧ p5) → (p4 ∨ p1)) → (p1 ∨ True))) ∨ ((p1 ∨ (p2 → p2)) ∧ p3))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_32021369410415370962035103653 : ((p1 ∨ ((p2 → (((p4 ∧ ((((p3 ∨ p2) ∨ False) ∧ p5) → ((p1 ∧ p1) ∧ ((True ∧ True) → p1)))) → (True ∧ p3)) → p4)) ∨ True)) ∧ True) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59295888072989641475711940558 : (((p3 ∨ p5) ∨ (((p2 ∨ True) → (((p4 ∧ True) → False) ∨ ((False ∨ True) ∨ ((p5 ∧ p5) ∨ p1)))) ∨ (p2 ∧ (p4 → (True ∨ p2))))) ∨ p3) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164562255371310590024200443180 : (((((False ∧ (p3 → p4)) ∧ p1) ∨ (p4 ∧ (((p3 ∧ (False ∧ p4)) ∧ p4) ∧ p3))) ∧ p4) ∨ ((((p3 ∧ p5) → True) ∧ p4) ∨ (False ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42424694216485583362437278201 : (((p5 ∧ (((((p4 ∧ p5) → True) ∧ (p1 ∨ ((p1 ∨ p1) ∨ p1))) → (p2 ∨ False)) ∨ (p1 ∨ (p1 → ((p2 ∨ False) ∧ False))))) ∨ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45639490444406633991893953878 : (((p4 ∨ (((p4 ∨ (((False ∧ p1) ∧ False) → p3)) → p2) ∨ ((p4 ∨ (p2 ∧ (((p3 ∨ False) ∧ p1) ∧ p4))) ∨ (p2 ∧ False)))) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_78879310577992263028500168634 : ((((True → p2) ∧ (((p5 ∨ (((p1 ∨ False) ∧ True) ∨ p2)) → p4) ∧ (((p2 ∧ (p5 → p3)) ∧ (p1 ∨ p5)) → True))) ∧ (p2 → p3)) → p2) := by
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
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h8 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h9 := h4 h8
  -- One of the premise coincides with the conclusion.
  exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134883171484601930902377531650 : (((p3 → (((((False ∨ p4) ∨ p3) ∨ p1) ∧ p3) ∧ ((p5 ∨ ((((p4 ∨ p2) ∨ p1) ∨ p3) ∨ p4)) ∧ False))) → p1) ∨ (True ∨ (p2 → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354672076728670195205886054565 : (p5 → (((p5 ∨ (p3 → ((True ∨ p3) → ((((p3 ∧ (p2 → p3)) ∨ p5) → p3) ∨ ((p3 ∨ ((False ∧ p2) ∨ p1)) ∨ p5))))) → p2) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187589523187107922290962966572 : ((p3 ∨ (p4 ∨ ((p4 → p5) ∧ (((True ∧ True) ∧ p4) → p2)))) → ((((p4 → False) ∧ (p4 ∧ (p3 → (p1 ∧ p5)))) ∧ p2) → (p2 → p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h7.left
  let h9 := h7.right
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h10 =>
    -- One of the premise coincides with the conclusion.
    exact h10
  case inr h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h13 : p4 := by
        -- One of the premise coincides with the conclusion.
        exact h12
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h14 := h6 h13
      -- False on the left can always be used.
      apply False.elim h14
    case inr h15 =>
      -- Conjunctions on the left can always be decomposed.
      let h16 := h15.left
      let h17 := h15.right
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h18 : p4 := by
        -- One of the premise coincides with the conclusion.
        exact h8
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h19 := h6 h18
      -- False on the left can always be used.
      apply False.elim h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115676787449485746152259467561 : (((p1 ∧ (False ∧ ((True → False) ∨ p2))) ∨ (p1 ∨ (((False → (p1 → (True ∧ (((True ∧ p3) ∨ False) ∨ p1)))) → p2) ∨ False))) ∨ (True ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_123194878853497674699836861165 : (((((p2 ∧ (p2 → False)) ∧ ((True → (((p4 → p5) → False) ∧ p1)) ∧ (p1 ∧ p4))) ∧ p5) ∧ (((p1 ∧ p5) ∧ p1) ∧ p1)) → (p3 ∧ True)) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- Conjunctions on the left can always be decomposed.
  let h10 := h7.left
  let h11 := h7.right
  -- Conjunctions on the left can always be decomposed.
  let h12 := h11.left
  let h13 := h11.right
  -- Conjunctions on the left can always be decomposed.
  let h14 := h3.left
  let h15 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h16 := h14.left
  let h17 := h14.right
  -- Conjunctions on the left can always be decomposed.
  let h18 := h16.left
  let h19 := h16.right
  -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
  have h20 : p2 := by
    -- One of the premise coincides with the conclusion.
    exact h8
  -- We have shown the premise of h9, we can now drive its conclusion.
  let h21 := h9 h20
  -- False on the left can always be used.
  apply False.elim h21
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_624146653936856966153078105594 : ((((p2 ∨ (p1 ∨ (((False ∨ p1) ∧ (p1 → (p1 ∨ ((True ∨ (((True → p2) → p2) ∧ p1)) ∧ ((p4 ∧ p2) ∨ p3))))) ∨ p5))) ∨ True) ∨ False) ∧ True) := by
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
theorem thm_5_vars_218002690398416144576397193951 : (((p5 ∧ p4) ∧ (False ∨ p3)) → (p5 → (((((p1 ∨ p3) → p1) ∨ False) ∨ ((((p2 ∨ p4) ∨ (False ∨ False)) ∧ (False ∨ p1)) ∨ p5)) ∨ p1))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h7 =>
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198561051384323217972995959931 : ((p1 ∨ (((p1 ∨ (p5 ∧ p1)) ∨ False) → p3)) ∨ (((False ∧ p5) → (p4 ∨ p3)) → (((p2 ∧ ((p4 ∨ p4) → p5)) ∧ (p3 ∨ p3)) → p3))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h7 =>
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h8 =>
    -- One of the premise coincides with the conclusion.
    exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118678899350336609597640010194 : ((p5 ∨ (((((False ∨ (False → ((True ∧ False) ∨ (True ∨ p2)))) ∨ p3) ∧ (p2 → (True ∨ (False ∧ (p2 ∧ p2))))) ∧ p2) ∧ p2)) ∨ (False ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231881028824182624749985533720 : (((True ∨ p2) → p5) → (((False ∧ p1) ∨ ((((p5 → False) ∧ (p1 ∨ (p3 → True))) → p3) ∨ p4)) ∨ ((p5 → (p1 ∨ p2)) → (True ∨ False)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217602195639497032857484686189 : ((((p1 → p1) ∨ True) → p5) → (p4 → (((True ∧ (((((p5 → (False → p4)) ∨ (p3 → p3)) → (False ∧ False)) ∨ p5) → False)) → p2) ∧ p4))) := by
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
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h6 : ((((p5 → (False → p4)) ∨ (p3 → p3)) → (False ∧ False)) ∨ p5) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h7 : ((p1 → p1) ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h8 := h1 h7
    -- One of the premise coincides with the conclusion.
    exact h8
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h9 := h5 h6
  -- False on the left can always be used.
  apply False.elim h9
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_962105618906950568569765106105 : ((((p5 ∨ True) ∧ (p1 ∧ (((p4 ∨ ((p1 ∨ (((((p1 ∧ p4) → True) ∧ True) ∨ p3) ∨ (False → p2))) → p2)) ∨ p4) ∧ (True → p3)))) → p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
        have h11 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h8, we can now drive its conclusion.
        let h12 := h8 h11
        -- One of the premise coincides with the conclusion.
        exact h12
      case inr h13 =>
        -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
        have h14 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h8, we can now drive its conclusion.
        let h15 := h8 h14
        -- One of the premise coincides with the conclusion.
        exact h15
    case inr h16 =>
      -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
      have h17 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h8, we can now drive its conclusion.
      let h18 := h8 h17
      -- One of the premise coincides with the conclusion.
      exact h18
  case inr h19 =>
    -- Conjunctions on the left can always be decomposed.
    let h20 := h3.left
    let h21 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h22 := h21.left
    let h23 := h21.right
    -- Disjunctions on the left can always be decomposed.
    cases h22
    case inl h24 =>
      -- Disjunctions on the left can always be decomposed.
      cases h24
      case inl h25 =>
        -- We want to use the implication h23 based on <expert-advice>. So we show its premise.
        have h26 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h23, we can now drive its conclusion.
        let h27 := h23 h26
        -- One of the premise coincides with the conclusion.
        exact h27
      case inr h28 =>
        -- We want to use the implication h23 based on <expert-advice>. So we show its premise.
        have h29 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h23, we can now drive its conclusion.
        let h30 := h23 h29
        -- One of the premise coincides with the conclusion.
        exact h30
    case inr h31 =>
      -- We want to use the implication h23 based on <expert-advice>. So we show its premise.
      have h32 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h23, we can now drive its conclusion.
      let h33 := h23 h32
      -- One of the premise coincides with the conclusion.
      exact h33
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319787627500906551229049470055 : (p4 ∨ (((p1 → p4) ∨ ((p3 ∧ True) ∨ p4)) → ((p1 ∨ p4) ∨ (p2 → (p2 ∨ ((p3 ∧ (((p3 ∨ p4) ∧ p1) ∨ True)) → (p3 ∧ True))))))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h9 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308452753544599700767622816715 : (p2 ∨ ((((p2 ∨ p1) ∨ ((False ∨ (((p2 ∨ (p3 → p1)) ∧ ((p1 ∧ (p1 → (p4 ∧ p5))) ∧ False)) ∨ p3)) → p5)) ∧ (p2 ∧ p1)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57572233455549869718127765628 : ((((p1 ∨ p2) ∧ p2) → (p2 → (p5 → (((p5 ∨ (p1 → p2)) → p2) ∧ (p3 ∨ (((p5 ∨ p1) → ((p2 ∨ p5) ∧ p4)) → False)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_598516311422575212225502922538 : ((((((p3 ∧ p2) → p2) → ((p5 ∨ p3) → ((p2 ∧ (False → (True → (True → (p2 ∨ (p1 ∨ p1)))))) ∧ ((p1 ∨ True) → p1)))) ∧ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314403292110029593475448473438 : (p3 ∨ (((p3 ∧ (p2 ∨ (False ∨ ((True ∧ (((False ∨ (p5 → p3)) ∨ True) → (p2 ∨ p5))) ∧ p1)))) ∧ p4) ∨ (p2 → (p4 ∨ (p4 → p2))))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50423774038110192972435059149 : (((p3 ∧ (False ∨ (((p1 ∨ ((((p1 ∧ (True → True)) ∧ (p5 ∨ p4)) ∨ p4) ∧ p3)) → p4) ∨ True))) ∨ ((True ∧ (p4 ∨ p4)) → p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172027924229853390602785238612 : ((((p2 ∨ True) → (((True ∨ True) ∧ (p1 ∨ p1)) ∨ (p4 ∨ p2))) ∨ (p2 ∨ False)) ∨ (True ∨ (p1 → (p3 → ((p3 ∧ p4) ∧ (True ∨ p2)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_670106252148334595941035788855 : (((((p1 ∨ (True ∧ ((True ∨ p3) → False))) ∧ (p1 ∨ ((p3 → (False → (p4 ∨ p3))) ∨ (p3 ∧ (p5 ∧ False))))) ∨ (True → (p5 → p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135000993084740942101375572881 : (((p4 ∧ (((((p3 ∧ (((False ∨ p4) ∧ p1) ∧ ((p1 → p5) ∧ p2))) ∨ False) ∨ p4) ∧ p4) ∧ p3)) ∧ (p5 → p3)) ∨ (p1 ∨ (p4 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309913986363703063723583882024 : (p2 ∨ (((p3 ∧ ((p1 ∨ (p5 ∧ p3)) ∧ ((True ∧ (p2 ∨ ((False → p3) → p2))) ∧ p5))) ∨ True) ∨ (p2 ∨ (p3 → ((p4 ∧ p2) → p1))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249229451057749566968636298431 : ((p4 ∨ p4) ∨ ((((p3 → ((True ∨ (((p4 ∧ ((True ∧ False) ∨ True)) ∧ False) ∨ p4)) ∨ p1)) → (False ∧ (p4 ∧ True))) ∨ (True ∨ False)) ∨ p1)) := by
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
theorem thm_5_vars_650087978674742390075335613592 : ((((((p1 ∧ p1) → (p2 → (p4 ∧ ((((p2 → True) ∨ (p4 ∨ p2)) ∨ (True ∧ True)) ∨ False)))) → ((p1 → p3) ∨ p1)) ∧ (p4 ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137249888356209436575408155345 : ((p1 ∧ ((((p4 ∨ True) ∨ p3) ∧ p3) ∧ ((((True → p3) ∨ ((p4 → (True ∧ False)) → p2)) ∨ (True → False)) ∧ p2))) ∨ (False → (True → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_220933505906482562548024586342 : (((p1 ∧ p2) ∨ True) ∧ (((((True ∧ p4) ∨ p4) ∧ ((((True ∨ p5) → p3) → ((False ∨ (p1 ∨ False)) → p4)) → False)) ∨ p5) ∨ (True ∨ p5))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68628966561112300629041911317 : ((p4 → ((False ∨ (((p2 → (p2 → (p1 → p3))) → ((p5 ∧ (p4 → False)) ∧ ((True ∨ p3) ∨ (p5 → (p2 ∧ p4))))) ∧ p1)) ∨ True)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39242992379060798501795964601 : (((False ∧ ((((p3 ∧ p3) → (p2 ∨ (p3 ∨ ((((False ∧ p3) ∧ (True ∨ (p5 → False))) ∧ p4) → p3)))) ∨ (True ∨ p3)) → p1)) ∧ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354405036844328542771889123318 : (p5 → (((p2 ∨ (p4 → p1)) → (((((p3 ∨ p4) ∧ (((False ∨ p1) → False) ∨ (p5 ∧ (p1 ∧ p4)))) ∨ p3) ∨ True) ∨ (p1 → p2))) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310113182465023889842371827681 : (p2 ∨ (((((p2 → ((False → True) ∨ True)) ∧ ((p4 → p4) → False)) ∨ p1) ∨ p4) ∨ ((p1 ∨ (False → (((p1 ∨ p3) ∨ p5) → p2))) ∨ p5))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- False on the left can always be used.
      apply False.elim h1
    case inr h5 =>
      -- False on the left can always be used.
      apply False.elim h1
  case inr h6 =>
    -- False on the left can always be used.
    apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137309684897464813238145365907 : ((p2 ∧ (((p2 ∧ p1) ∨ ((True ∨ (p4 → ((p3 → p3) ∧ p3))) ∧ p4)) ∨ ((((p2 ∧ p5) → False) ∧ False) → p2))) ∨ ((p5 ∨ False) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_348129081208467090904643271268 : (p3 → ((p1 ∧ p1) → (((False ∨ (((p5 ∧ (p5 ∨ (False ∧ True))) → False) ∧ p1)) ∧ ((((True → p2) → (p3 ∨ p4)) ∨ p3) → p4)) ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157453356973910228272638989244 : ((((((True ∨ p4) → (((p3 → (True ∧ (p1 ∨ False))) → p4) ∨ p3)) ∨ p5) ∧ p1) ∨ (False → p5)) ∨ ((p4 → True) → ((p4 ∧ True) ∧ p5))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_677638909272172626642807740615 : ((((((p3 ∧ (p2 → (((p3 → True) ∧ ((True → False) → (False ∨ (p1 ∧ p4)))) ∧ False))) → False) → p2) ∨ (p3 ∨ ((False → True) ∨ p3))) ∨ p5) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_754902138504720150142604128065 : (((False ∧ (p3 ∨ (((p2 ∨ ((p3 → (True → p2)) ∧ p3)) ∨ p1) → ((p4 ∨ p4) ∨ (((p1 ∧ (p4 ∧ (p1 ∨ p3))) ∧ p5) ∧ p3))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55967786009565378583175970898 : (((((False ∨ p5) ∨ p4) ∧ True) ∨ (False ∨ ((p4 ∧ p4) ∨ (p3 ∨ (((p1 ∧ (p5 ∧ (p5 ∨ p3))) ∨ ((p2 ∧ p3) → p3)) ∨ p3))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152109730175422333540745821105 : ((((((p1 → False) → p5) ∧ (True ∧ p5)) ∧ p4) ∧ ((((p2 → False) ∧ True) ∧ p4) → ((p4 → True) ∧ p2))) → ((True → (p3 → p5)) → p5)) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- Conjunctions on the left can always be decomposed.
  let h9 := h8.left
  let h10 := h8.right
  -- One of the premise coincides with the conclusion.
  exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63206009521431625690699707584 : ((p5 ∧ ((((True ∨ (False ∨ (p5 → p5))) ∧ (p2 ∧ ((p4 ∨ (p5 ∧ p1)) ∧ (p3 → False)))) → p1) ∨ (p5 ∨ ((p5 → p4) ∨ True)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53679643311810693514873465048 : (((True ∧ (p3 ∨ (((p5 ∧ p2) → (p1 → p5)) → p4))) ∧ (p5 ∨ (p3 → (p1 → ((p2 ∧ ((True ∨ (p5 ∨ False)) ∧ p5)) ∨ p3))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165520020073858746651043782896 : ((((p2 → (p1 ∨ (p2 → p4))) → ((p2 → True) → True)) → ((p3 → False) → (p5 ∨ p3))) ∨ ((p4 ∨ (((True → False) ∧ False) ∧ p3)) → p4)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- False on the left can always be used.
    apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57174523876436828643852008162 : ((((p5 ∧ False) ∨ p4) ∨ ((p5 ∧ ((((((True → p5) → p4) → p2) → (False ∨ p4)) ∧ (True ∨ p1)) ∧ p4)) ∨ (p5 ∨ (p2 → p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_740422909325085458159628529568 : ((((p1 ∨ p3) ∨ (p4 ∨ ((((((p2 ∧ p5) ∧ (p3 ∨ (True ∨ p4))) ∧ True) → ((((False → p3) ∨ False) ∨ p5) ∨ p2)) ∧ p5) ∧ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116364028672516628652209762690 : ((((p1 ∧ False) → p1) → ((False ∧ (((((p2 ∨ (p1 ∧ p5)) ∨ (((p1 → False) ∨ True) ∨ True)) ∧ True) ∧ p2) ∨ p1)) ∧ p4)) ∨ (True ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_355546719736405393659841096201 : (p5 → (((p4 ∨ (((((True ∨ ((((False ∨ p3) → p5) ∨ (True → p3)) ∧ (p5 → p5))) ∨ p4) ∧ p4) ∨ p5) → False)) ∨ True) ∨ (False → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310118522637417221503157584229 : (p2 ∨ (((p1 → ((((((p1 → True) ∨ False) ∧ p4) ∨ p1) ∧ p3) ∨ p3)) → False) ∨ (((p2 → True) ∨ p5) ∨ (p5 ∧ ((True ∧ False) ∨ p5))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138008265588524326422786008567 : ((True → ((((p2 → True) → ((((False ∨ False) ∨ p4) ∨ p5) ∨ (((True ∨ (p1 ∨ p3)) ∨ True) ∧ p1))) → p2) ∧ p2)) ∨ (False → (p4 ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_642031835089862503122395378393 : ((((True ∧ (((p3 ∧ p3) ∧ (False → (False ∨ ((True ∧ ((p4 → (p5 ∨ p4)) ∧ False)) → ((p4 ∨ p2) ∧ (p1 → p4)))))) ∨ p1)) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_201329595635957814785510308950 : ((p5 → ((p4 ∨ ((p4 ∨ p1) ∧ p4)) → False)) → (p3 ∨ ((((p1 ∨ (p1 ∧ p5)) ∨ (p5 ∧ (False → p4))) → ((p4 ∨ p5) ∧ p4)) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59337555895092784206183005226 : (((p4 ∨ p5) ∨ (False ∨ ((((((((False ∧ p1) ∧ p3) ∨ p3) ∨ p5) → True) → p5) → p4) → (((p4 ∧ p2) ∧ True) ∨ (True ∨ p3))))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_759266811195517535502896641071 : (((p2 ∧ ((((True ∨ ((True ∨ (p1 ∧ (False ∨ p1))) ∧ (True ∨ False))) → True) ∨ (((p4 ∧ (p5 → p2)) ∨ p3) → p5)) → (p1 ∨ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217130148163623545046173889329 : ((((p5 ∨ p4) ∨ p3) ∨ p5) → ((p1 ∧ ((((p3 ∨ (p5 ∧ p4)) ∧ p4) ∧ (p3 ∨ p4)) → False)) → ((p1 → (p4 → (p2 ∨ p3))) ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h8
        -- Implications on the right can always be decomposed.
        intro h9
        -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
        have h10 : (((p3 ∨ (p5 ∧ p4)) ∧ p4) ∧ (p3 ∨ p4)) := by
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- One of the premise coincides with the conclusion.
          exact h7
          -- One of the premise coincides with the conclusion.
          exact h9
          -- One of the premise coincides with the conclusion.
          exact h9
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h9
        -- We have shown the premise of h4, we can now drive its conclusion.
        let h11 := h4 h10
        -- False on the left can always be used.
        apply False.elim h11
      case inr h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h12
    case inr h13 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h14
      -- Implications on the right can always be decomposed.
      intro h15
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h13
  case inr h16 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h17
    -- Implications on the right can always be decomposed.
    intro h18
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h19 : (((p3 ∨ (p5 ∧ p4)) ∧ p4) ∧ (p3 ∨ p4)) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h16
      -- One of the premise coincides with the conclusion.
      exact h18
      -- One of the premise coincides with the conclusion.
      exact h18
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h18
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h20 := h4 h19
    -- False on the left can always be used.
    apply False.elim h20



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356773327715810281808762840918 : (p5 → (((p3 ∨ p1) → ((p1 ∨ p4) → p4)) → (((p5 ∧ (p5 ∧ (p1 ∨ p4))) ∨ (p3 ∨ False)) → (True → ((p4 → (p1 ∨ False)) ∨ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
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
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h13 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h14 =>
      -- False on the left can always be used.
      apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_188664347643603885947452985616 : ((((p4 ∨ p1) ∨ ((p2 → p1) → False)) ∨ (False → p1)) ∧ (False ∨ (((False ∨ p1) → ((p2 → p5) ∨ ((p1 ∨ False) ∨ p2))) ∨ (False ∧ False)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136716546030828249037301794836 : (((p3 ∧ p2) ∧ ((p5 ∧ (p3 → p2)) ∨ (p3 ∨ (((((p1 → True) ∧ ((p2 ∨ False) → p4)) ∨ False) → p1) ∧ True)))) ∨ ((True ∨ p2) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_564825211960242413712249275901 : (((True → (((((p5 ∧ p2) ∧ (p3 → (p4 ∨ ((False ∧ True) → p1)))) ∧ (p1 ∧ ((p1 ∨ (False ∧ False)) → p2))) → (p1 → p3)) ∨ True)) ∧ True) ∧ True) := by
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
theorem thm_5_vars_47981262532303847692572270980 : (((((p3 → (((((p2 ∨ False) ∧ (False → p1)) → (p5 ∧ p3)) → p3) ∧ p1)) → p2) → ((True ∨ (p5 ∨ p3)) → p1)) → (False ∧ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_123714217315554119237461146046 : (((((False ∧ (False ∨ p3)) ∧ ((p4 ∧ p2) ∨ (False → (p4 ∧ False)))) → p2) ∧ (p5 → (((p3 ∨ p5) → (p1 ∧ p2)) ∧ p2))) → (p1 ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206273210727218436827011048122 : ((False ∨ (p3 ∧ ((p5 ∨ p5) ∨ p2))) ∨ ((False ∨ (p3 ∧ (p2 ∨ ((p1 → ((p2 ∨ p1) → (p3 → (p3 ∧ p2)))) ∨ (False ∨ p1))))) → p3)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- One of the premise coincides with the conclusion.
        exact h4
      case inr h9 =>
        -- Disjunctions on the left can always be decomposed.
        cases h9
        case inl h10 =>
          -- False on the left can always be used.
          apply False.elim h10
        case inr h11 =>
          -- One of the premise coincides with the conclusion.
          exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_358579851180542279627789211045 : (p5 → (p3 → ((((p3 → (p1 ∨ (p4 → ((p5 ∧ p1) ∧ p1)))) ∨ (p5 → ((((p5 ∧ (False ∧ False)) → False) → True) → False))) ∨ p2) ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51969149847020068245613969834 : ((((True ∧ (p4 ∨ p5)) ∨ (((p1 → p5) → (((p2 ∧ p5) → p4) ∧ p2)) ∨ p3)) ∨ (p4 → (((True ∧ (p2 ∨ p2)) → False) ∧ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52910286308173041754565383811 : (((p2 → (p2 → (False → (((p1 ∧ (True → (p4 → p1))) ∨ p3) ∨ True)))) → (p2 ∧ (((p1 ∨ (p5 ∨ p3)) → p1) → (p1 ∧ p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166767558724313067682216402043 : ((p5 → ((((((p2 ∨ False) ∧ p3) ∨ True) ∨ p2) → ((p5 ∧ p2) → (False ∧ p5))) ∨ p4)) ∨ (((False ∧ (p5 ∧ False)) ∨ (True ∨ p1)) ∨ p3)) := by
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
theorem thm_5_vars_180143629593107422389550347016 : ((((p1 → (p5 → (((False ∨ (p2 → False)) → p1) ∨ p3))) → p1) → False) → (p1 → ((p1 → (p4 ∧ ((p3 → p5) → p2))) ∨ (p4 → p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152153158489483672140875028865 : ((((p3 → ((p1 ∨ p3) ∧ True)) → (p2 → p3)) ∨ (p1 ∨ ((p5 ∧ ((p1 → (p3 ∧ p4)) → p5)) ∨ p3))) → ((p2 → (p5 ∧ p5)) ∨ True)) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Conjunctions on the left can always be decomposed.
        let h7 := h6.left
        let h8 := h6.right
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
theorem thm_5_vars_185771813785915746121928032297 : ((p4 → ((p2 ∧ (p4 ∧ p5)) ∨ (((p1 ∨ p2) → False) → False))) ∨ (((p5 → p3) → (p2 ∨ p2)) ∨ (True ∨ (p4 ∨ (p1 ∧ (p5 ∨ p4)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58720760020433765457887729976 : (((p3 → p1) ∧ ((((p5 → ((False → p1) ∧ False)) ∨ p4) ∨ (p5 ∨ ((True ∧ (True ∧ ((True ∧ p2) → (p1 ∨ p2)))) → p5))) ∨ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260178303930527215509051369188 : ((p2 → p2) → (((((True ∨ p1) ∧ (p3 → (True → (((True → p1) ∧ p5) ∧ p5)))) ∧ (p4 ∧ p3)) ∧ p3) ∨ ((p4 ∨ (False ∨ p1)) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338382833414469450677491023029 : (p1 → ((True → ((p1 ∧ p3) → p2)) ∨ (p5 → (p5 → (True ∧ ((((p4 → p5) ∧ (p5 → (((p5 ∨ p1) → p2) → p5))) → p3) ∨ True)))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_327174123035580113927743226551 : (True → ((False ∨ ((((False ∨ p2) ∧ ((p4 → (p5 → p4)) → False)) → (p5 ∨ True)) → ((p3 ∧ (p2 ∨ ((p5 ∧ p2) ∧ True))) ∨ True))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_621895529612579617458869081976 : ((((p1 ∧ ((p2 ∧ p4) ∨ ((((p3 ∧ ((p4 ∨ (p2 → True)) ∨ (p2 ∧ p5))) → p2) ∧ False) ∧ ((p4 ∧ p2) → (p5 ∧ True))))) ∨ True) ∨ p1) ∧ True) := by
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



