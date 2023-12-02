variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68997970208078783054869593012 : ((p5 → (((p1 ∨ (p3 → ((((p5 ∧ p2) → True) ∨ (p5 → (((p3 ∨ p3) ∧ True) ∨ True))) ∨ False))) → (p4 ∧ (p2 ∨ True))) ∧ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_689331328891364688019007515019 : ((((((p2 ∨ (((p5 ∨ (p4 ∧ p5)) ∧ p3) ∨ (p5 → p4))) ∨ True) ∨ (p1 → p5)) ∨ (p2 ∨ (p3 ∨ ((True → p1) ∧ (False → p5))))) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43951586035457460660251757813 : (((((p5 ∨ True) ∧ (((p5 ∨ ((False ∧ (p2 → (True ∧ (False → p1)))) ∧ p2)) → p4) ∧ ((p5 → p1) → True))) ∨ (p2 → True)) → p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184175826951483244690483666135 : (((p2 → ((p1 ∨ ((p2 ∧ p4) ∨ (p5 ∧ p1))) ∨ p3)) ∨ p3) ∨ ((p5 → (((p2 ∧ (True → False)) ∨ True) ∧ (p1 ∨ (p5 ∧ p5)))) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200747353571595631588702827205 : ((p3 ∧ (p5 ∧ (p4 ∨ (p5 ∨ (p2 ∧ p4))))) → (((p1 ∨ ((p4 ∨ ((p4 ∨ ((False ∧ p3) → p2)) ∧ False)) ∨ p2)) ∨ (p4 → p4)) ∧ p5)) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h9
      -- One of the premise coincides with the conclusion.
      exact h9
    case inr h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h11
  -- Conjunctions on the left can always be decomposed.
  let h13 := h1.left
  let h14 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h15 := h14.left
  let h16 := h14.right
  -- Disjunctions on the left can always be decomposed.
  cases h16
  case inl h17 =>
    -- One of the premise coincides with the conclusion.
    exact h15
  case inr h18 =>
    -- Disjunctions on the left can always be decomposed.
    cases h18
    case inl h19 =>
      -- One of the premise coincides with the conclusion.
      exact h19
    case inr h20 =>
      -- Conjunctions on the left can always be decomposed.
      let h21 := h20.left
      let h22 := h20.right
      -- One of the premise coincides with the conclusion.
      exact h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_697670737447156475126037550588 : ((((p5 ∨ (((True ∨ True) → (p2 ∧ (p1 → (p5 ∧ p4)))) → p2)) ∧ (((((True → p3) → (False ∨ p2)) ∧ p1) → p4) → (p2 ∨ True))) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- We need to get the left conjuct of h3 based on <expert-advice>.
  let h4 := h3.left
  -- One of the premise coincides with the conclusion.
  exact h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354895995566690897371677068724 : (p5 → ((p4 ∧ ((((False ∧ p1) → p1) ∨ p4) ∧ (False ∧ ((((p4 ∨ True) → (p5 → p4)) → (p2 → ((p4 ∧ p1) ∧ True))) ∧ False)))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_15241415407823585386582869476 : (((p3 → (p2 ∨ (((p5 → True) ∨ (p4 → (((p1 → (p2 ∧ (False → (p1 ∧ p5)))) ∨ (p3 ∨ p1)) → p1))) → p2))) ∨ (True ∨ True)) ∧ True) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114645146730093543450343296737 : ((((p3 → (((p4 → (False ∧ (False → p2))) ∨ p4) → (p5 ∧ p2))) ∨ (True ∧ p3)) ∨ (((p4 → p4) ∨ False) ∨ (p3 ∨ p1))) ∨ (p3 ∨ p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228068440035968567878905653777 : ((p4 ∧ (p3 ∧ p5)) ∨ (((((p1 ∨ ((p5 → ((p3 → p5) ∨ True)) → (p4 ∨ True))) ∧ (p3 ∧ p1)) ∨ (p3 ∨ True)) ∨ p4) ∨ (p4 ∨ p3))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47460962812291781692861608326 : (((p4 ∧ (p5 → (((p3 → (p1 ∧ (p4 ∧ (p1 ∨ True)))) ∧ ((((False → False) ∨ p2) ∨ p2) ∨ p1)) ∨ (False ∧ p3)))) ∨ (p5 ∨ True)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_3366388970468919406709431094 : ((p5 ∨ p1) → ((p2 ∨ (p4 ∧ p3)) ∨ (((False → ((True ∧ ((p5 ∧ ((True ∧ p4) ∨ p4)) ∧ p2)) ∧ p2)) ∨ True) ∨ (p2 ∧ p3)))) := by
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
theorem thm_5_vars_56563877393056875027431712872 : (((p5 ∨ ((p1 ∧ p3) → False)) → ((p4 ∨ ((((p2 ∧ ((p5 ∨ p1) ∨ (True ∨ p5))) ∧ True) ∨ p5) ∧ False)) ∨ ((p2 → p1) → True))) ∨ p5) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219659887155819513246856875198 : ((False → (True ∨ (p5 → True))) → ((((p2 ∧ p3) ∧ ((p1 → p1) ∧ p5)) ∨ (p5 ∧ ((p2 ∨ p2) → p4))) ∨ (((True → p1) → False) → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_685262262614330139426840345620 : ((((p1 → ((((((p3 → (p4 ∨ (p2 ∧ True))) ∨ (p2 ∧ p1)) ∨ False) ∧ True) ∧ p3) ∨ p5)) ∨ (p1 ∧ (((True ∧ p5) → False) ∨ True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157431715986020475722559982388 : (((False ∧ (p3 ∧ (p5 ∧ (((p3 → p5) → p2) → ((p3 ∨ (False → p1)) → p3))))) ∧ (p4 ∧ p3)) ∨ (p3 → (((True ∨ p4) ∨ p4) ∨ p4))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315768116648032747892222894844 : (p3 ∨ ((p1 ∧ p1) → ((p4 ∨ (False ∨ (p3 ∨ p3))) → (((False ∧ p5) ∨ (((p1 ∨ True) ∨ p2) ∨ p3)) ∧ (False → ((p2 ∨ False) ∨ True)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h1.left
    let h5 := h1.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- False on the left can always be used.
      apply False.elim h7
    case inr h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Conjunctions on the left can always be decomposed.
        let h10 := h1.left
        let h11 := h1.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h9
      case inr h12 =>
        -- Conjunctions on the left can always be decomposed.
        let h13 := h1.left
        let h14 := h1.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h12
  -- Implications on the right can always be decomposed.
  intro h15
  -- False on the left can always be used.
  apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167932562337656558981329208716 : ((((p4 ∨ (p4 ∧ p4)) → ((True → True) ∧ p4)) ∨ ((p1 ∨ False) ∧ ((p2 ∧ p2) ∧ p1))) → ((p5 → p1) ∨ ((True ∧ True) ∨ (p3 ∨ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h11 =>
      -- False on the left can always be used.
      apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147382921467132943871870133068 : ((((p2 → ((p4 → p2) → (((p1 ∨ True) → True) ∧ p1))) ∨ (((p4 ∨ p4) → p1) → (p3 → False))) ∨ p3) ∨ ((False ∧ (p4 ∨ p2)) → False)) := by
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
theorem thm_5_vars_116265701907800469415660281775 : (((p3 ∧ (p2 ∧ p1)) ∨ (((p1 ∧ p3) ∨ ((p2 ∧ p4) ∧ (p2 ∨ p4))) → (((True → True) → p5) ∧ (p5 → (True ∧ p1))))) ∨ (p3 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208448060781860776201427038578 : (((False → False) ∨ (p5 ∧ (p4 ∧ p4))) → (((p1 ∨ p1) ∨ p3) → (((p5 → ((p2 ∨ (p2 → p5)) ∨ p5)) ∨ (False ∨ p2)) ∨ (p3 → p4)))) := by
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
      cases h1
      case inl h5 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h6
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h6
      case inr h7 =>
        -- Conjunctions on the left can always be decomposed.
        let h8 := h7.left
        let h9 := h7.right
        -- Conjunctions on the left can always be decomposed.
        let h10 := h9.left
        let h11 := h9.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h12
        -- One of the premise coincides with the conclusion.
        exact h11
    case inr h13 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h14 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h15
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h15
      case inr h16 =>
        -- Conjunctions on the left can always be decomposed.
        let h17 := h16.left
        let h18 := h16.right
        -- Conjunctions on the left can always be decomposed.
        let h19 := h18.left
        let h20 := h18.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h21
        -- One of the premise coincides with the conclusion.
        exact h20
  case inr h22 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h23 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h24
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h24
    case inr h25 =>
      -- Conjunctions on the left can always be decomposed.
      let h26 := h25.left
      let h27 := h25.right
      -- Conjunctions on the left can always be decomposed.
      let h28 := h27.left
      let h29 := h27.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h30
      -- One of the premise coincides with the conclusion.
      exact h29



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165997230923493921079173527682 : (((p4 ∧ p1) ∨ (p5 ∨ ((p4 ∨ True) ∧ (p2 → ((p4 ∧ (p4 ∧ p5)) ∨ (True ∨ p3)))))) ∨ ((False ∨ (True ∧ p3)) ∧ (False ∧ (False ∧ p3)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303107639731118017648691684650 : (False ∨ (p3 → ((True → ((p3 → True) → (p1 → (False ∧ (((True ∨ p4) → (p5 ∨ (p3 ∨ p4))) ∨ ((p3 ∧ (p5 ∨ True)) ∨ p4)))))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57963571056119942604532876073 : (((p2 → (True → False)) → (((p5 → ((p3 → p2) ∨ p1)) → False) ∨ (((True ∧ (((False ∧ p3) ∧ p1) ∨ p4)) → p2) ∨ (True ∨ True)))) ∨ p2) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_7279190588076428192027974530 : (((p3 ∨ (((((True ∨ p4) ∧ (p1 → (((p5 ∨ True) ∧ p5) ∨ (p5 ∧ p4)))) → p4) ∨ ((True ∨ True) ∨ p2)) ∨ (p3 ∧ p3))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_320122074755380888736406081305 : (p4 ∨ ((False ∨ (p3 ∨ p4)) → (((p2 ∨ p2) ∨ ((((p2 ∧ False) ∨ (p3 ∨ False)) → p5) → (True ∨ (p1 ∧ (p4 ∧ (p2 ∨ p2)))))) ∨ p2))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h5
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h6 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h7
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2643010680552795885406176711 : (((((p1 ∧ p4) ∨ p4) → True) ∧ p3) ∨ (True → ((((False ∧ True) → p5) → (p2 ∨ ((True ∨ p4) ∧ (p3 ∨ (p1 → p3))))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207162732869187190226725423018 : (((p3 → (p1 → (p5 → p3))) ∧ p2) → ((p1 ∨ ((((p1 → p4) → (p4 ∧ False)) → p1) ∨ ((p4 ∨ ((False → p2) ∨ p1)) ∨ p3))) ∨ True)) := by
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
theorem thm_5_vars_305766054821868400692595702494 : (p1 ∨ ((((p5 ∨ p2) ∧ (p1 ∧ (False ∨ p1))) → p4) ∨ ((((p1 ∨ (p5 → p2)) → (p4 ∧ (p2 ∨ (p5 ∨ (p4 ∧ True))))) ∨ True) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314922686298915029113748142537 : (p3 ∨ ((((p5 ∧ (True ∧ p3)) ∨ (p3 → p4)) → (p5 ∨ p4)) ∨ (((p5 → (p4 → False)) ∧ (p2 → (False → p1))) ∨ (p2 → (True → True))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55886888098274298106763565314 : (((p1 ∨ (True ∨ (p2 ∨ True))) ∧ (p2 ∨ (((p3 ∨ p2) ∨ p2) ∨ ((p5 ∧ (p3 ∧ False)) → ((((False ∧ True) → p2) ∧ True) ∧ p3))))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h3
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h5 := h1.left
  let h6 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h6.left
  let h8 := h6.right
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_721438040619872870373970429049 : ((((p1 ∧ (True ∧ (True → p2))) → ((p5 ∧ (p3 → ((p3 → p1) ∨ ((False ∨ ((p2 → p4) ∨ ((p3 ∨ p3) ∧ False))) → p4)))) ∨ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117966092652869639282511749587 : ((p5 ∧ (p3 → (((p5 ∧ p3) → (p4 ∧ False)) ∨ (((p4 → False) ∨ p1) ∨ (p5 → (((p4 ∨ (p5 ∨ p3)) ∧ False) ∧ p5)))))) ∨ (p1 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217030278427871497988304459610 : ((((True ∨ p3) ∧ p1) ∨ p5) → ((p4 ∨ ((p3 ∨ (p2 → ((p5 ∨ ((p5 → ((p5 → True) ∧ (True ∧ False))) → p5)) ∨ p3))) → p3)) ∨ True)) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47524706996830206404042464984 : (((p3 ∨ (p3 ∧ (((True ∧ p5) → (p3 ∨ (p5 ∨ (((((p5 ∧ (True → True)) ∧ p2) → False) ∧ p4) ∨ True)))) → p2))) ∨ (p3 ∧ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156883856843506685618969540823 : ((((((((((p5 ∨ p5) ∨ (p1 ∨ True)) → False) ∨ (False ∨ p4)) → p2) → p3) → False) ∨ p4) ∨ p2) ∨ ((False → p3) ∨ ((p4 → True) → False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_668919118438060678552006252386 : (((((p4 ∧ ((((p4 ∨ p5) ∨ ((((p3 ∨ True) → p3) ∧ p2) ∧ (p1 → (p2 ∨ p2)))) ∨ p2) ∨ False)) ∨ p2) ∨ ((p2 ∧ p3) → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148028635039972444976154765848 : ((((True ∧ (p4 → (p1 ∨ True))) → (p2 ∨ (((p3 ∨ False) → (p2 ∧ (True ∧ p1))) → False))) ∨ (True ∨ False)) ∨ ((p4 ∨ (p4 ∨ p1)) ∧ p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_94350825413953673520376929449 : ((p2 ∧ ((p4 ∨ ((p1 ∨ p2) ∧ (p5 → False))) ∧ (True ∧ ((((p3 → p4) ∨ (p4 → p4)) ∨ (p4 → (p2 ∧ p5))) ∧ (p2 → p3))))) → p3) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
        have h13 : p2 := by
          -- One of the premise coincides with the conclusion.
          exact h2
        -- We have shown the premise of h10, we can now drive its conclusion.
        let h14 := h10 h13
        -- One of the premise coincides with the conclusion.
        exact h14
      case inr h15 =>
        -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
        have h16 : p2 := by
          -- One of the premise coincides with the conclusion.
          exact h2
        -- We have shown the premise of h10, we can now drive its conclusion.
        let h17 := h10 h16
        -- One of the premise coincides with the conclusion.
        exact h17
    case inr h18 =>
      -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
      have h19 : p2 := by
        -- One of the premise coincides with the conclusion.
        exact h2
      -- We have shown the premise of h10, we can now drive its conclusion.
      let h20 := h10 h19
      -- One of the premise coincides with the conclusion.
      exact h20
  case inr h21 =>
    -- Conjunctions on the left can always be decomposed.
    let h22 := h21.left
    let h23 := h21.right
    -- Disjunctions on the left can always be decomposed.
    cases h22
    case inl h24 =>
      -- Conjunctions on the left can always be decomposed.
      let h25 := h5.left
      let h26 := h5.right
      -- Conjunctions on the left can always be decomposed.
      let h27 := h26.left
      let h28 := h26.right
      -- Disjunctions on the left can always be decomposed.
      cases h27
      case inl h29 =>
        -- Disjunctions on the left can always be decomposed.
        cases h29
        case inl h30 =>
          -- We want to use the implication h28 based on <expert-advice>. So we show its premise.
          have h31 : p2 := by
            -- One of the premise coincides with the conclusion.
            exact h2
          -- We have shown the premise of h28, we can now drive its conclusion.
          let h32 := h28 h31
          -- One of the premise coincides with the conclusion.
          exact h32
        case inr h33 =>
          -- We want to use the implication h28 based on <expert-advice>. So we show its premise.
          have h34 : p2 := by
            -- One of the premise coincides with the conclusion.
            exact h2
          -- We have shown the premise of h28, we can now drive its conclusion.
          let h35 := h28 h34
          -- One of the premise coincides with the conclusion.
          exact h35
      case inr h36 =>
        -- We want to use the implication h28 based on <expert-advice>. So we show its premise.
        have h37 : p2 := by
          -- One of the premise coincides with the conclusion.
          exact h2
        -- We have shown the premise of h28, we can now drive its conclusion.
        let h38 := h28 h37
        -- One of the premise coincides with the conclusion.
        exact h38
    case inr h39 =>
      -- Conjunctions on the left can always be decomposed.
      let h40 := h5.left
      let h41 := h5.right
      -- Conjunctions on the left can always be decomposed.
      let h42 := h41.left
      let h43 := h41.right
      -- Disjunctions on the left can always be decomposed.
      cases h42
      case inl h44 =>
        -- Disjunctions on the left can always be decomposed.
        cases h44
        case inl h45 =>
          -- We want to use the implication h43 based on <expert-advice>. So we show its premise.
          have h46 : p2 := by
            -- One of the premise coincides with the conclusion.
            exact h39
          -- We have shown the premise of h43, we can now drive its conclusion.
          let h47 := h43 h46
          -- One of the premise coincides with the conclusion.
          exact h47
        case inr h48 =>
          -- We want to use the implication h43 based on <expert-advice>. So we show its premise.
          have h49 : p2 := by
            -- One of the premise coincides with the conclusion.
            exact h39
          -- We have shown the premise of h43, we can now drive its conclusion.
          let h50 := h43 h49
          -- One of the premise coincides with the conclusion.
          exact h50
      case inr h51 =>
        -- We want to use the implication h43 based on <expert-advice>. So we show its premise.
        have h52 : p2 := by
          -- One of the premise coincides with the conclusion.
          exact h39
        -- We have shown the premise of h43, we can now drive its conclusion.
        let h53 := h43 h52
        -- One of the premise coincides with the conclusion.
        exact h53



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_229530529937213343213415767452 : ((p2 → (p4 ∨ p5)) ∨ (((((p2 ∨ True) → ((p1 ∧ p4) → False)) → (p3 ∨ (True → p3))) ∨ (False → True)) ∧ (p5 ∨ (p3 → (p3 ∨ p4))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_261103334943948851939985576306 : ((p4 → p3) → ((True → (True → p1)) → ((((p5 ∨ (p3 → p5)) ∨ ((True ∨ True) → p1)) ∨ True) → ((True → p1) ∧ ((p5 ∧ p3) → p3))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h8 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h9 := h2 h8
        -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
        have h10 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h9, we can now drive its conclusion.
        let h11 := h9 h10
        -- One of the premise coincides with the conclusion.
        exact h11
      case inr h12 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h13 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h14 := h2 h13
        -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
        have h15 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h14, we can now drive its conclusion.
        let h16 := h14 h15
        -- One of the premise coincides with the conclusion.
        exact h16
    case inr h17 =>
      -- We want to use the implication h17 based on <expert-advice>. So we show its premise.
      have h18 : (True ∨ True) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h17, we can now drive its conclusion.
      let h19 := h17 h18
      -- One of the premise coincides with the conclusion.
      exact h19
  case inr h20 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h21 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h22 := h2 h21
    -- We want to use the implication h22 based on <expert-advice>. So we show its premise.
    have h23 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h22, we can now drive its conclusion.
    let h24 := h22 h23
    -- One of the premise coincides with the conclusion.
    exact h24
  -- Implications on the right can always be decomposed.
  intro h25
  -- Conjunctions on the left can always be decomposed.
  let h26 := h25.left
  let h27 := h25.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h28 =>
    -- Disjunctions on the left can always be decomposed.
    cases h28
    case inl h29 =>
      -- Disjunctions on the left can always be decomposed.
      cases h29
      case inl h30 =>
        -- One of the premise coincides with the conclusion.
        exact h27
      case inr h31 =>
        -- One of the premise coincides with the conclusion.
        exact h27
    case inr h32 =>
      -- One of the premise coincides with the conclusion.
      exact h27
  case inr h33 =>
    -- One of the premise coincides with the conclusion.
    exact h27



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_4449468015000019322438198305 : (p2 → (((p5 ∧ (p3 → (p3 → (True ∧ (((p4 ∧ p3) → p5) ∧ ((True ∨ p4) ∨ (True → p3))))))) ∨ (False ∨ (p5 ∧ p5))) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159912033827802591590309932421 : ((((p4 → (False → (((p3 ∨ (False ∨ ((p3 → False) ∧ p3))) ∨ True) → (p4 → p3)))) ∨ p4) → p4) → ((p3 ∨ (True ∧ (p4 ∨ p1))) ∧ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p4 → (False → (((p3 ∨ (False ∨ ((p3 → False) ∧ p3))) ∨ True) → (p4 → p3)))) ∨ p4) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- Implications on the right can always be decomposed.
    intro h6
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- False on the left can always be used.
        apply False.elim h4
      case inr h9 =>
        -- Disjunctions on the left can always be decomposed.
        cases h9
        case inl h10 =>
          -- False on the left can always be used.
          apply False.elim h10
        case inr h11 =>
          -- Conjunctions on the left can always be decomposed.
          let h12 := h11.left
          let h13 := h11.right
          -- False on the left can always be used.
          apply False.elim h4
    case inr h14 =>
      -- False on the left can always be used.
      apply False.elim h4
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h15 := h1 h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h15
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h16 : ((p4 → (False → (((p3 ∨ (False ∨ ((p3 → False) ∧ p3))) ∨ True) → (p4 → p3)))) ∨ p4) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h17
    -- Implications on the right can always be decomposed.
    intro h18
    -- Implications on the right can always be decomposed.
    intro h19
    -- Implications on the right can always be decomposed.
    intro h20
    -- Disjunctions on the left can always be decomposed.
    cases h19
    case inl h21 =>
      -- Disjunctions on the left can always be decomposed.
      cases h21
      case inl h22 =>
        -- False on the left can always be used.
        apply False.elim h18
      case inr h23 =>
        -- Disjunctions on the left can always be decomposed.
        cases h23
        case inl h24 =>
          -- False on the left can always be used.
          apply False.elim h24
        case inr h25 =>
          -- Conjunctions on the left can always be decomposed.
          let h26 := h25.left
          let h27 := h25.right
          -- False on the left can always be used.
          apply False.elim h18
    case inr h28 =>
      -- False on the left can always be used.
      apply False.elim h18
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h29 := h1 h16
  -- One of the premise coincides with the conclusion.
  exact h29



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61785790913632143240741302017 : ((p2 ∧ ((p3 ∧ ((p4 ∧ ((p3 ∨ (p1 ∨ ((p5 ∨ True) ∧ (((p3 → p4) ∧ False) ∧ p3)))) ∧ (p2 ∨ (p1 ∧ p1)))) ∧ p5)) ∧ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57452384147853208764596667293 : (((p5 ∨ (p5 ∧ False)) ∨ ((((((True → p2) ∧ (p3 → (False ∨ p1))) → (True ∨ p5)) ∧ p5) ∨ p2) → ((p2 → (True ∧ p2)) → p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165158131830235556099293178322 : ((((((p3 ∧ p3) → p5) → True) → (p3 ∨ (p2 ∧ (p5 ∨ (True ∨ p5))))) ∧ (p4 ∧ p4)) ∨ ((p5 → (((p3 ∧ p2) ∨ p1) → p4)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165560256891678598670449565564 : (((True → (False ∨ ((p2 → (p2 ∨ p2)) ∨ p1))) ∧ (p4 ∨ (p4 ∧ ((p2 ∨ p1) ∧ True)))) ∨ ((p5 ∨ (p1 ∨ (False → p4))) ∨ (p2 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_742808912333267593306629977008 : ((((p3 → p1) ∨ ((((((p2 ∨ p1) → p4) ∧ False) ∨ (p2 → p5)) ∨ p3) ∨ (p2 ∨ (((p5 → False) ∨ False) ∨ (p3 ∨ (False → p2)))))) ∨ p5) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115905830871493942914246528308 : ((((p2 → (True ∧ p2)) → False) ∨ ((p1 ∧ (((p5 ∧ ((p1 ∨ (((p3 → p4) ∧ False) → p3)) ∧ p4)) → p3) ∨ p5)) ∧ p4)) ∨ (True ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133969947210849918027617927630 : (((p5 → ((False ∧ ((p1 ∧ (p5 → p2)) ∧ p4)) ∨ (p3 ∨ ((((True ∨ (p4 → True)) → False) ∧ p3) → p4)))) ∧ False) ∨ (False → (p3 ∧ p5))) := by
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
theorem thm_5_vars_184510798036909363749405767205 : (((False ∧ ((p1 ∨ (p1 ∧ p3)) ∧ (p1 ∧ p3))) ∨ (p1 ∨ p3)) ∨ ((p1 ∧ (((p1 ∧ p2) ∧ False) ∨ True)) → ((False ∨ (p4 ∨ True)) ∧ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- False on the left can always be used.
    apply False.elim h6
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h10 := h1.left
  let h11 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h11
  case inl h12 =>
    -- Conjunctions on the left can always be decomposed.
    let h13 := h12.left
    let h14 := h12.right
    -- Conjunctions on the left can always be decomposed.
    let h15 := h13.left
    let h16 := h13.right
    -- False on the left can always be used.
    apply False.elim h14
  case inr h17 =>
    -- One of the premise coincides with the conclusion.
    exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_318658701502747078450079488528 : (p4 ∨ ((p5 → ((((p4 ∨ p2) ∨ False) ∧ (((p1 ∨ (p1 → p4)) → (False ∧ (False → p3))) ∨ True)) ∧ ((p4 ∧ p5) ∧ p5))) ∨ (True ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187195442958092994862087223489 : (((p1 ∨ True) → (p2 ∧ ((((p3 ∨ p2) ∧ True) ∨ p5) → p2))) → (((((p5 → p4) ∧ (((p4 ∧ p5) ∨ p4) ∨ p5)) → False) ∨ p1) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_646960790409928467853464657447 : ((((p3 → (((False ∧ (p5 ∧ (p2 ∧ (p3 ∨ (True ∧ (p4 ∧ (True ∧ p1))))))) ∧ (True → ((False → p1) ∨ (p3 ∧ p1)))) ∧ p5)) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_750507315025409685639481782868 : (((True ∧ ((p4 ∨ ((p3 → False) ∧ (True → (False ∨ (((((p4 → p1) ∨ p1) → p4) → (p4 ∧ p4)) ∧ p4))))) → (p4 ∧ (True → False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_201095420593157827730931114682 : ((True → ((True ∧ ((p5 ∨ p4) ∧ p4)) ∧ p4)) → (((((p3 → False) ∨ p4) ∧ ((p4 → p3) ∨ p5)) ∧ False) ∨ (False → (p3 ∧ (p2 → False))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119398725876955913102698627823 : ((p4 → (((False ∧ ((p5 ∨ p2) ∨ (((p5 → p1) ∧ (((p2 ∧ (p5 → True)) ∧ (True ∧ True)) ∨ p4)) → p1))) ∧ p3) ∨ p1)) ∨ (p3 → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184507816020916273081519337962 : ((((p1 ∨ True) → ((p4 ∨ p2) ∨ (False ∧ p3))) ∨ (p1 → True)) ∨ ((p2 ∧ ((p2 ∧ p5) ∨ (p2 → (((p4 ∨ p1) ∨ p1) → p1)))) ∨ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_491617256816980348354266309735 : (((((p2 ∧ (p3 ∧ p1)) ∨ p1) ∨ (p1 ∨ (False → (p1 ∨ ((p5 ∨ (True ∧ p2)) ∧ (((False → p5) → ((p2 ∨ p3) ∨ p2)) ∧ p2)))))) ∧ True) ∧ True) := by
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
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53016769218094283808103543751 : (((((p2 ∨ (p3 ∧ p4)) ∨ p1) ∧ (((p5 → p2) → False) ∨ p1)) ∧ (True ∧ (((p5 → p4) → (((False → True) ∧ p5) ∨ True)) ∨ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_790505606116253010156715603355 : (((p5 ∨ (False ∨ (p1 ∨ (((((False ∧ True) ∨ True) → False) → p1) ∧ ((((False ∨ (p5 → ((p3 ∧ p2) ∧ p5))) ∧ p3) → p1) ∧ True))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115586360599832453375525019903 : ((((False → (p5 ∧ True)) → (p4 → False)) ∧ ((((p1 ∨ False) ∨ (p1 ∨ (True ∧ p4))) → (((p5 ∨ p1) ∨ True) ∧ False)) ∨ True)) ∨ (p2 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351408241148295370186596291580 : (p4 → (((p1 → (p4 ∨ ((p3 ∨ p2) ∧ (p5 → p1)))) → ((p4 ∧ ((p5 → p1) → (p1 ∨ p5))) ∨ True)) ∨ ((p3 ∨ (p4 ∧ False)) ∧ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41548978309937028067639471426 : ((((p4 ∨ (True → ((p3 → ((p5 ∧ p1) ∨ p1)) ∧ p5))) ∨ (((True ∨ p4) ∨ (False ∨ (p1 → p1))) → (True ∨ (p4 ∨ p5)))) ∨ p3) ∨ p1) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h3 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h4 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- False on the left can always be used.
      apply False.elim h6
    case inr h7 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172157200293527988970613896928 : ((((p1 ∧ (True ∨ (False → ((p5 ∧ p5) ∨ p2)))) ∨ p2) ∨ (p5 ∧ (p5 ∧ False))) ∨ ((p2 ∧ ((p3 ∨ p2) ∨ (p3 ∨ False))) → (False → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_8568983789811243519216449842 : ((((((p2 ∨ p2) ∨ ((False ∨ ((p4 ∧ p2) ∨ (((p4 ∨ True) ∧ (False ∧ p4)) ∨ True))) → (p3 ∨ True))) ∧ p4) ∨ (True ∨ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_624062892347241471045091914352 : ((((p2 ∨ (((p3 → ((p3 → p1) ∨ True)) ∨ p1) ∧ ((p5 → (p3 → True)) → (p2 ∧ ((True ∧ (p1 ∧ p3)) ∧ (p2 → p5)))))) ∨ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133530391988285932777081322867 : ((((((True → (p3 → (p1 ∨ (p5 → p5)))) → (p4 ∧ False)) ∨ (((False → p3) → p2) ∧ (p3 ∧ False))) ∧ p3) ∧ p1) ∨ (p4 → (True ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39382782079424507324506266739 : (((p3 ∧ (p2 ∧ ((p3 ∨ p3) ∧ ((((p5 ∨ True) ∨ (p4 ∨ p4)) ∧ (p2 → ((p4 ∨ True) ∨ False))) ∨ ((p5 → p4) ∨ p1))))) ∧ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166008169194590620924844365506 : (((False ∨ p4) ∨ (p2 → (p5 ∨ (p4 ∧ ((p2 ∧ True) ∧ ((p1 ∧ p2) → (p4 ∨ p4))))))) ∨ ((True → (((p5 ∧ p5) ∨ p4) ∧ p2)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_105784860282519736768976602228 : (((((p3 ∨ (((p4 ∧ True) ∨ (p4 ∧ p4)) ∨ p1)) ∧ (p4 → (p3 ∨ True))) → False) → (((p2 → True) → p5) ∨ (p3 → True))) ∧ (True ∨ p4)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
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
theorem thm_5_vars_633363853305889787605138954682 : ((((((True ∨ ((p2 → (((False ∨ ((((p2 ∧ p4) ∨ p3) ∨ False) ∨ p5)) → True) ∧ (p1 → p2))) ∧ True)) ∨ False) ∨ (p3 ∧ p1)) → p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_8932329573815500592979348879 : (((((p2 ∨ p5) ∨ (p4 ∨ (True ∨ ((((False ∧ True) → p5) ∨ (False ∧ (p5 ∧ p4))) → False)))) → (p3 ∨ (p4 ∨ (p2 → p2)))) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h4
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- One of the premise coincides with the conclusion.
      exact h6
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h11
        -- One of the premise coincides with the conclusion.
        exact h11
      case inr h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h13
        -- One of the premise coincides with the conclusion.
        exact h13
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_790585730758047671335667580235 : (((p5 ∨ (p2 ∨ (p4 ∨ (((((((True → p3) ∨ p2) ∨ False) ∧ (((((False → p3) ∧ p3) → p2) → p1) → p4)) ∨ False) ∨ p2) → p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179333296223976278487610198933 : ((p1 ∨ (((p4 ∧ ((p5 ∧ p2) ∧ p5)) ∨ p4) ∧ (p2 ∧ (p1 ∧ True)))) ∨ (((False ∨ p4) ∧ p4) ∨ (False ∨ ((p4 ∨ (p1 ∨ True)) ∨ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_352275945763722485076791007052 : (p4 → (((p1 → (False → p2)) → p5) → ((p5 → (((((p4 ∨ p5) ∧ p3) → (p2 → p4)) ∨ (((True ∧ p3) ∨ p5) ∨ p2)) → p2)) ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55162312253333074974723223714 : ((((p1 ∨ ((False ∨ False) ∧ p1)) ∨ p3) ∨ (p2 ∨ (p4 ∨ ((((True ∨ p1) → p5) ∨ ((p3 ∧ False) ∧ False)) ∨ (True ∨ (p5 → p2)))))) ∨ False) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135825750902541208487328568397 : (((((p2 ∨ p1) ∨ ((p4 ∧ (p2 ∨ False)) ∨ False)) ∨ (False ∧ p2)) ∧ (p2 → (p1 → (p5 → (p2 ∧ (p5 ∧ p4)))))) ∨ ((False ∧ p1) → p3)) := by
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
theorem thm_5_vars_37990713860311277582631259096 : ((((((p3 ∧ False) ∨ ((p1 ∧ True) ∨ p3)) ∧ (p5 ∨ (((p2 → ((p4 → (False ∨ True)) ∨ p4)) → False) → p1))) ∨ (True ∧ False)) ∧ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135085768237408101688392163253 : (((((True → (p3 ∨ ((p2 ∧ (p4 ∧ p3)) ∨ (p1 ∧ p3)))) ∧ True) ∨ (((p1 → p3) ∨ p4) ∨ True)) ∨ (False → p3)) ∨ ((p1 ∧ p5) → p4)) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49685377849213763695593291898 : ((((p5 → True) ∧ ((((True ∧ False) → (p4 ∨ p4)) ∨ (False → p2)) ∨ (((p1 ∨ p5) → p1) → (p1 → p4)))) → (p3 ∧ (p1 → p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49128433280707587801098489159 : (((((p5 → (False → (p2 → p5))) → ((p3 ∨ (p2 ∧ p5)) ∨ p4)) ∨ (((False → p1) → (p4 ∨ p3)) → p5)) ∨ ((p1 ∧ True) → True)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_756512924422572694986740607112 : (((p1 ∧ ((((p4 ∧ p2) ∨ False) ∧ (((True ∧ p5) ∧ (((False ∨ p4) → (p1 → p3)) → p5)) ∨ False)) ∨ (((True ∨ False) ∨ False) → p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_707087781834381942589162410220 : (((((((p4 → p3) → (True → p3)) ∨ p1) → False) ∨ ((((p2 ∧ True) → True) ∧ (p1 ∧ ((True → False) → (p2 → (p2 ∧ p4))))) ∧ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_124100405428660623576710588477 : ((((((p2 → (p4 → False)) ∧ (p3 ∧ p5)) ∧ p3) → False) ∧ ((True ∨ ((p4 ∨ False) → p4)) ∧ ((p1 ∨ True) → (False ∧ True)))) → (p3 ∧ p5)) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h7 : (p1 ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h8 := h5 h7
    -- We need to get the left conjuct of h8 based on <expert-advice>.
    let h9 := h8.left
    -- False on the left can always be used.
    apply False.elim h9
  case inr h10 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h11 : (p1 ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h12 := h5 h11
    -- We need to get the left conjuct of h12 based on <expert-advice>.
    let h13 := h12.left
    -- False on the left can always be used.
    apply False.elim h13
  -- Conjunctions on the left can always be decomposed.
  let h14 := h1.left
  let h15 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h16 := h15.left
  let h17 := h15.right
  -- Disjunctions on the left can always be decomposed.
  cases h16
  case inl h18 =>
    -- We want to use the implication h17 based on <expert-advice>. So we show its premise.
    have h19 : (p1 ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h17, we can now drive its conclusion.
    let h20 := h17 h19
    -- We need to get the left conjuct of h20 based on <expert-advice>.
    let h21 := h20.left
    -- False on the left can always be used.
    apply False.elim h21
  case inr h22 =>
    -- We want to use the implication h17 based on <expert-advice>. So we show its premise.
    have h23 : (p1 ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h17, we can now drive its conclusion.
    let h24 := h17 h23
    -- We need to get the left conjuct of h24 based on <expert-advice>.
    let h25 := h24.left
    -- False on the left can always be used.
    apply False.elim h25



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60450657954024736926372977314 : (((p5 → False) → (p3 ∧ (p4 ∧ ((((p4 → (p1 ∨ p3)) → (p2 ∨ p1)) ∧ True) → ((((p3 ∨ p3) ∨ (p1 ∧ p4)) → p3) ∨ False))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184101145474970895780103688422 : ((((p5 ∧ p3) ∧ ((((p2 ∧ p3) ∨ p2) ∧ True) ∨ p2)) ∨ True) ∨ (p3 → (((p3 ∧ (p3 ∨ (p3 → ((True → True) ∨ p5)))) → p1) → p4))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62912717246219398464593154041 : ((p4 ∧ (True ∧ (((((p4 ∨ False) → (((p5 ∨ p4) ∧ p1) → ((True → p2) → (p5 ∧ p5)))) ∨ (p5 ∧ p2)) ∨ (False → True)) ∧ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52682745038284277767357830911 : (((p4 ∨ (((((False ∧ False) ∧ (True ∨ p5)) ∧ (p1 ∨ p4)) ∨ p3) ∨ p5)) ∨ (((p1 ∧ p5) ∧ (((p3 ∧ p4) ∨ p1) → p3)) ∨ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233499708463107462702488701981 : ((p1 ∨ (p3 ∧ p4)) → (((p1 ∨ (p3 → ((p2 ∨ (p2 → (p1 → True))) → p4))) → False) → ((p1 → (True → p5)) → ((False ∧ False) ∨ False)))) := by
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
    have h5 : (p1 ∨ (p3 → ((p2 ∨ (p2 → (p1 → True))) → p4))) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h6 := h2 h5
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h10 : (p1 ∨ (p3 → ((p2 ∨ (p2 → (p1 → True))) → p4))) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h11
      -- Implications on the right can always be decomposed.
      intro h12
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- One of the premise coincides with the conclusion.
        exact h9
      case inr h14 =>
        -- One of the premise coincides with the conclusion.
        exact h9
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h15 := h2 h10
    -- False on the left can always be used.
    apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_312312245850062052630628904054 : (p2 ∨ (p2 → (((p1 ∨ ((((p4 ∧ True) → False) ∨ (p5 ∧ p2)) ∨ p4)) ∨ True) → (p1 → (True ∧ (p1 ∧ (True ∧ (p5 ∨ (p2 → p1))))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Disjunctions on the left can always be decomposed.
        cases h7
        case inl h8 =>
          -- One of the premise coincides with the conclusion.
          exact h3
        case inr h9 =>
          -- Conjunctions on the left can always be decomposed.
          let h10 := h9.left
          let h11 := h9.right
          -- One of the premise coincides with the conclusion.
          exact h3
      case inr h12 =>
        -- One of the premise coincides with the conclusion.
        exact h3
  case inr h13 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h14 =>
    -- Disjunctions on the left can always be decomposed.
    cases h14
    case inl h15 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h16
      -- One of the premise coincides with the conclusion.
      exact h15
    case inr h17 =>
      -- Disjunctions on the left can always be decomposed.
      cases h17
      case inl h18 =>
        -- Disjunctions on the left can always be decomposed.
        cases h18
        case inl h19 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h20
          -- One of the premise coincides with the conclusion.
          exact h3
        case inr h21 =>
          -- Conjunctions on the left can always be decomposed.
          let h22 := h21.left
          let h23 := h21.right
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h22
      case inr h24 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h25
        -- One of the premise coincides with the conclusion.
        exact h3
  case inr h26 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h27
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_302029041007472197633988900632 : (False ∨ (True ∧ (((p2 → False) ∧ (((p2 ∨ p5) ∧ p3) → ((False ∨ p4) ∨ ((True ∨ (p2 → p1)) ∨ False)))) ∨ ((p2 → (False → p3)) ∨ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
theorem thm_5_vars_52518019850865358647649740377 : ((((p5 ∨ ((((p2 ∨ (False ∧ p4)) ∧ p3) ∧ p3) ∨ (True ∧ p2))) ∧ p3) ∨ ((True ∨ (p4 ∨ p1)) ∧ ((p3 → (p3 ∨ p2)) ∧ True))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_687510832556520600456469394201 : (((((p4 ∨ (True ∧ (((p4 ∨ p5) ∧ (p4 ∨ p2)) ∧ (p5 ∧ (p1 → True))))) ∨ True) ∧ (((True → p1) ∨ (p3 ∨ p5)) ∧ (p4 ∨ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156601816012516916259760168221 : ((((((False ∨ (p1 → p3)) ∧ (((p1 ∨ p1) → False) → True)) ∨ (False ∧ (p4 ∧ True))) ∧ p4) ∧ p5) ∨ ((True ∧ ((p1 ∧ False) ∨ p1)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_806360652415530640713427554489 : (((p4 → ((p5 ∧ (((p3 → (p3 ∨ p5)) → (False → p5)) ∧ (False ∨ (p2 ∨ (p5 ∧ (p2 ∧ (((p5 ∧ p4) → p5) ∧ p4))))))) ∨ True)) ∨ False) ∧ True) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350973619574650292084022192610 : (p4 → ((((p2 ∧ p2) ∨ p4) ∧ (((((p2 ∨ p4) → ((((p3 ∨ p1) ∧ p4) → p1) ∧ False)) ∨ p2) → (p2 ∨ p4)) → p3)) ∨ (p1 → p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_662428955116850088575055537225 : ((((((True ∨ p3) ∧ ((p2 ∧ (p5 ∨ p3)) ∨ p4)) → (False ∧ (((True ∧ (p3 ∧ (p2 ∨ False))) ∧ (p5 ∧ True)) → p2))) → (p3 → p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206018838964332923826568065018 : ((p2 ∧ ((p3 ∨ (p5 ∨ p2)) ∨ p2)) ∨ ((((p2 ∧ ((True ∧ p5) → (p3 → (False ∧ ((p1 → (p3 ∧ False)) ∧ p1))))) ∨ p2) ∨ p3) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_675837401656468093104111746130 : (((((p5 → ((((p1 ∧ p2) ∧ ((p5 ∨ p1) ∧ p2)) ∨ True) ∧ p5)) ∧ ((True → (p1 ∧ p3)) → p4)) ∧ (p1 → (False ∧ (False → p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



