variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_638880055692816938155030191043 : ((((((p3 ∨ (p2 ∧ p4)) → p3) ∧ ((((p1 ∨ p2) ∨ (p2 → ((p1 → (((p1 ∧ p5) ∧ p3) ∨ p1)) ∨ p5))) ∨ p3) ∧ p5)) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_690141765492024330656934007168 : ((((p1 ∨ ((p1 ∧ (((p5 ∨ p2) ∧ p4) ∨ p5)) ∨ (False → (False ∧ (True ∧ p3))))) ∨ ((True → p4) → (((True ∨ p3) ∨ False) ∧ p3))) ∨ p4) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164448456995507479992507208294 : (((((p4 ∧ (False ∨ (((p2 ∧ p5) ∧ p1) ∧ (p1 ∧ p5)))) ∨ (p4 ∨ p5)) ∧ True) ∧ p4) ∨ (p2 → (p5 → ((p4 → (p2 ∨ False)) ∨ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_216442186029373979462112964434 : ((p4 → (False ∧ (p5 ∧ True))) ∨ ((((p4 ∨ (p5 ∨ (((False ∧ p3) ∨ ((p2 → p2) → p2)) ∧ p2))) ∧ (True → (False ∧ p4))) ∧ p5) → p4)) := by
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
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h9 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h10 := h5 h9
      -- We need to get the left conjuct of h10 based on <expert-advice>.
      let h11 := h10.left
      -- False on the left can always be used.
      apply False.elim h11
    case inr h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h12.left
      let h14 := h12.right
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h15 =>
        -- Conjunctions on the left can always be decomposed.
        let h16 := h15.left
        let h17 := h15.right
        -- False on the left can always be used.
        apply False.elim h16
      case inr h18 =>
        -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
        have h19 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h5, we can now drive its conclusion.
        let h20 := h5 h19
        -- We need to get the left conjuct of h20 based on <expert-advice>.
        let h21 := h20.left
        -- False on the left can always be used.
        apply False.elim h21



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38061268751016933210641060740 : (((((((p4 ∨ ((False → (p2 ∧ p4)) → (True ∧ p3))) ∧ False) → p3) ∧ ((p3 → p4) → (p4 ∧ (p5 ∨ p4)))) → (p3 ∨ p3)) ∧ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_348177615908706156010061233273 : (p3 → ((p2 ∨ p5) → (((p4 → ((p5 ∧ p5) → False)) → p2) → ((p3 → False) → (((p2 ∨ (p4 → ((p5 ∧ True) ∧ False))) → p1) ∨ p5))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h5 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h6 : p3 := by
      -- One of the premise coincides with the conclusion.
      exact h1
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h7 := h4 h6
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190279342235548756251156946102 : ((((p3 ∨ (p1 ∧ (p3 ∨ (p4 ∨ p5)))) ∨ True) ∨ p4) ∨ (((((True → (p2 ∨ True)) ∧ ((False → (False ∧ True)) → p1)) ∨ False) ∨ p1) ∧ True)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309776430160549229137725405075 : (p2 ∨ ((p5 → (((p1 ∧ ((p2 ∨ (False ∨ p2)) → (p3 → False))) ∨ False) ∨ (p5 ∨ ((p1 ∧ p4) → p5)))) ∧ (True ∨ ((p5 → p3) ∨ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_778422904639021974725608898200 : (((p1 ∨ (p3 ∧ (((p2 ∨ ((p4 → ((False ∧ p4) ∨ ((p4 → p1) → (p1 → p1)))) ∧ (True → (p5 ∧ p2)))) ∧ True) ∧ (p4 → p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_357062574341649075817029387124 : (p5 → (((p4 ∧ True) ∧ p2) → ((((p1 ∨ p1) ∧ True) ∨ ((p1 ∧ False) → (p5 ∧ p5))) ∧ ((p2 ∧ ((p3 → p3) → p1)) ∨ (True ∧ p2))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h7
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h8 := h7.left
  let h9 := h7.right
  -- False on the left can always be used.
  apply False.elim h9
  -- Conjunctions on the left can always be decomposed.
  let h10 := h7.left
  let h11 := h7.right
  -- False on the left can always be used.
  apply False.elim h11
  -- Conjunctions on the left can always be decomposed.
  let h12 := h2.left
  let h13 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h14 := h12.left
  let h15 := h12.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_806140538519782633105051128925 : (((p4 → ((((p1 → (((((((p4 ∧ p2) → p2) ∧ ((p5 ∧ False) → (p1 ∨ p3))) ∨ p2) ∧ p5) → False) → p1)) ∧ p5) ∧ p1) ∨ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172046141751402622977631145946 : (((p3 → ((False → (False ∨ p2)) → ((p5 ∨ (p1 ∧ True)) ∧ p1))) ∨ (False ∨ p4)) ∨ (p3 ∨ (False → ((p2 → (p1 ∨ p3)) → (p3 ∧ p3))))) := by
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
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_329761870965570521711229413879 : (True → (True ∧ ((p5 ∨ ((((p5 ∧ (p5 → False)) ∨ (((p2 ∨ p4) ∨ False) ∨ p1)) ∧ (p4 ∧ p5)) ∨ (True ∧ (False ∨ p3)))) ∨ (p5 ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39120621830646645896306269612 : ((((True ∧ p4) → (((p5 ∧ ((False ∨ False) ∧ (p5 ∨ ((False → (p2 ∨ (p3 ∨ False))) ∧ p2)))) ∨ ((p3 → p4) ∨ p3)) ∨ True)) ∧ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301054133167175421980781447551 : (False ∨ (((p5 → ((p1 ∨ False) ∧ (p1 ∧ p3))) → (False ∧ True)) ∨ ((((p1 → True) ∨ p2) ∨ (True ∨ p5)) ∨ ((True ∨ p1) → (p2 ∧ False))))) := by
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
theorem thm_5_vars_257246098365854503545345887021 : ((p2 ∨ p3) → (((((((((False ∨ (p1 ∨ False)) ∨ p4) → p1) → p1) ∨ (False ∨ (False ∧ p4))) ∨ True) ∨ p1) ∨ ((p4 → p2) → p1)) ∨ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
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
  case inr h3 =>
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
theorem thm_5_vars_677340127780369689221773800312 : (((((p5 ∨ (((p2 → p3) → (p3 → p1)) → ((True ∨ (p5 ∧ (p2 ∧ (p4 → p2)))) ∧ p4))) ∧ True) ∨ (p4 ∧ (p4 ∧ (p1 → p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57523731866098693089006652582 : (((p4 → (p1 → False)) ∨ ((((False → False) ∨ p1) ∧ ((p5 ∨ (p4 ∧ ((p2 ∧ p5) ∨ ((p2 ∨ (True ∧ p3)) ∨ p5)))) → p2)) ∧ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_616639830852546351341680661066 : (((((p3 ∧ ((((p3 ∧ p4) → (p1 → p1)) → p1) ∨ p1)) ∧ (p2 ∧ ((p5 ∨ ((((False → p2) → p2) ∨ p5) ∨ True)) ∧ p5))) ∨ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_302558927725636949134034084966 : (False ∨ (p1 ∨ (((p3 ∨ (((False ∨ False) ∧ p3) ∨ (True ∧ p1))) → (((p2 ∧ (p1 ∧ p1)) ∨ p1) → ((p5 ∨ False) ∨ (p1 ∨ p5)))) ∨ False))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Conjunctions on the left can always be decomposed.
        let h11 := h10.left
        let h12 := h10.right
        -- Disjunctions on the left can always be decomposed.
        cases h11
        case inl h13 =>
          -- False on the left can always be used.
          apply False.elim h13
        case inr h14 =>
          -- False on the left can always be used.
          apply False.elim h14
      case inr h15 =>
        -- Conjunctions on the left can always be decomposed.
        let h16 := h15.left
        let h17 := h15.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h17
  case inr h18 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h19 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h18
    case inr h20 =>
      -- Disjunctions on the left can always be decomposed.
      cases h20
      case inl h21 =>
        -- Conjunctions on the left can always be decomposed.
        let h22 := h21.left
        let h23 := h21.right
        -- Disjunctions on the left can always be decomposed.
        cases h22
        case inl h24 =>
          -- False on the left can always be used.
          apply False.elim h24
        case inr h25 =>
          -- False on the left can always be used.
          apply False.elim h25
      case inr h26 =>
        -- Conjunctions on the left can always be decomposed.
        let h27 := h26.left
        let h28 := h26.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h28



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305488175235502859340113773083 : (p1 ∨ (((((p2 → (p3 ∧ p4)) ∨ p4) ∨ ((False ∨ (p4 → p3)) → p1)) ∧ p5) ∨ ((((p4 ∧ (p2 → p2)) ∧ False) ∨ (False → True)) ∨ p4))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_788542419139761798626865261140 : (((p5 ∨ ((p1 → ((((p5 ∧ ((p4 → p3) ∧ False)) ∧ ((p3 → p1) ∨ (p2 → p2))) ∧ True) ∧ ((p3 ∨ (p2 ∨ p5)) ∨ p4))) ∨ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_690033462181492156392651408030 : ((((p3 ∧ ((p4 ∧ p5) ∧ (p1 → ((((p5 ∧ p1) ∨ p2) ∧ False) ∧ (True ∨ True))))) ∨ (p4 ∧ ((((p5 ∧ True) ∧ p5) ∨ p3) ∨ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62380325402869580811728113468 : ((p3 ∧ ((p2 ∨ (p4 ∧ (((p5 ∧ (p3 ∨ True)) ∨ (p1 ∧ (False ∧ True))) → True))) ∨ ((p2 → p3) ∨ (p2 ∨ ((p5 ∨ p3) ∨ False))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337475729627994510566339649843 : (p1 → ((((p2 ∧ p4) ∨ (p4 ∧ ((True ∧ (((p2 ∧ False) ∧ False) ∨ (p1 ∧ (p5 ∨ p1)))) ∧ False))) ∨ True) ∧ ((p1 ∧ p3) ∨ (True ∧ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317632547802356363592092568263 : (p4 ∨ (((((((False ∨ p5) → p1) ∧ (True → (p2 ∨ p1))) ∨ p1) → (False ∧ (True ∨ (((p1 ∧ p3) ∨ (p4 → True)) ∨ p2)))) ∨ True) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167855882835676190506298777263 : (((p5 ∨ (((True ∨ p1) → p3) → ((False → p2) ∧ p3))) ∨ ((p1 ∨ (p5 ∧ p3)) → p2)) → (p3 → ((False → p1) → ((p2 ∧ p5) ∨ True)))) := by
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
theorem thm_5_vars_156995003825778286406849356651 : (((((False ∨ p2) → (False ∨ p5)) ∧ (((p2 → p2) ∧ p5) ∨ (((True ∨ p2) ∧ True) → p5))) ∨ True) ∨ (True ∨ (((False ∨ p4) ∨ p1) ∧ p2))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_355089896031642361481777339052 : (p5 → (((True ∧ ((p3 ∨ (((((True ∨ (p5 ∧ ((((p4 ∨ p3) ∨ p5) → p1) ∧ p5))) → p2) ∨ True) ∨ p2) ∨ p2)) ∧ p5)) → False) → p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (True ∧ ((p3 ∨ (((((True ∨ (p5 ∧ ((((p4 ∨ p3) ∨ p5) → p1) ∧ p5))) → p2) ∨ True) ∨ p2) ∨ p2)) ∧ p5)) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
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
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_416853476315817955973714822093 : ((((p4 ∧ (((p2 → (p5 ∧ False)) ∧ (((((p2 → p2) ∧ p5) ∨ (p2 ∧ (False → (p1 ∨ p5)))) → (p2 ∧ p2)) ∨ p2)) ∧ p2)) → False) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  cases h7
  case inl h8 =>
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h9 : p2 := by
      -- One of the premise coincides with the conclusion.
      exact h5
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h10 := h6 h9
    -- We need to get the right conjuct of h10 based on <expert-advice>.
    let h11 := h10.right
    -- False on the left can always be used.
    apply False.elim h11
  case inr h12 =>
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h13 : p2 := by
      -- One of the premise coincides with the conclusion.
      exact h5
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h14 := h6 h13
    -- We need to get the right conjuct of h14 based on <expert-advice>.
    let h15 := h14.right
    -- False on the left can always be used.
    apply False.elim h15
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39435804877538656033692379386 : (((p5 ∧ (((((True → (p4 ∧ p2)) ∨ p4) ∧ (p5 ∨ (True ∧ ((((True → (p1 → p3)) ∧ p5) → p1) → p5)))) → False) ∨ p3)) ∧ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301990335866104702582911845531 : (False ∨ ((p3 → p3) → ((True ∧ (p3 → (p1 ∨ (((False ∨ (p2 → ((p1 ∧ p4) ∧ p2))) → p5) ∧ (p2 → (p4 ∨ True)))))) ∨ (True ∨ p5)))) := by
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
theorem thm_5_vars_8130727144936953773883296133 : (((((p2 ∨ p4) → ((((p1 ∧ True) → p3) → ((p5 ∧ p3) → False)) ∨ ((False ∨ (p3 ∨ p3)) → ((p1 ∨ p1) ∧ p5)))) ∨ True) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_358187135372405538510529334064 : (p5 → (p3 ∨ ((p4 ∧ (p5 ∨ p2)) → (((((p3 → p4) ∧ p2) ∨ p4) → ((p1 ∧ p3) ∨ (p4 ∧ p4))) ∨ (((p4 ∨ False) ∨ p5) ∧ p3))))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h6
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h3
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h10
      -- One of the premise coincides with the conclusion.
      exact h10
  case inr h11 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h12
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h13 =>
      -- Conjunctions on the left can always be decomposed.
      let h14 := h13.left
      let h15 := h13.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h3
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h16 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h16
      -- One of the premise coincides with the conclusion.
      exact h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1766631271149545751752251210 : ((((((False → p3) → (p4 → (p1 ∨ p5))) ∧ p3) → (((p5 ∧ (p1 → False)) ∨ True) ∨ (p2 ∧ False))) ∨ p3) ∨ (p3 → (p3 ∧ p4))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115831382956569787120491127222 : ((((p3 → True) → (True ∨ p2)) ∧ ((((p4 ∧ p2) → False) ∧ (p1 ∧ ((p4 → ((p4 ∨ (False ∧ True)) ∨ p2)) ∨ p4))) → p5)) ∨ (p1 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157413045845879756448359711943 : (((((p3 ∧ ((True ∨ True) → True)) → p4) ∧ ((((p4 → p1) ∨ p4) ∨ False) ∨ p1)) ∧ (p5 ∧ p2)) ∨ ((True → (False → (p5 ∧ True))) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48131030229828915035008318550 : ((((p5 → (False ∨ p2)) ∧ ((p1 ∨ p1) → ((p2 ∧ p1) → (p2 ∨ (((p4 ∧ (p4 ∧ (p2 ∧ p2))) ∨ p5) → True))))) → (p5 ∨ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40947995649717139727990657598 : ((((((p2 ∨ ((((p3 ∧ ((True → p4) ∧ False)) ∧ p2) → (p1 ∧ p5)) ∧ p4)) → (p5 ∨ p4)) ∧ (p3 → p5)) ∨ (p3 ∨ p3)) ∨ True) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324728518652604878123708324019 : (p5 ∨ (((False → True) → False) → (p5 → (((p3 ∧ (True → p5)) ∧ p3) ∨ ((p2 ∨ (((False ∨ p5) → p2) → (p4 ∨ False))) → (p3 ∨ True)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : (False → True) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h3
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_139114514460716695617853491901 : ((((False → ((p2 → (p5 ∧ ((p1 → p4) ∨ p1))) ∨ ((p2 ∨ (False → True)) ∨ p1))) ∨ (True → (False → p2))) ∨ False) → ((True ∧ p5) ∨ True)) := by
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
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_607036779075862008646818512124 : ((((((True ∧ (True → (((False ∧ p4) ∨ False) ∨ (p4 ∧ (p2 ∨ p4))))) ∨ (p3 → ((p1 ∨ (p5 ∨ (p5 ∧ True))) ∨ p2))) ∧ p2) ∨ True) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_133655240963249134130303794128 : ((((((p3 ∨ False) ∨ (p2 ∨ ((p5 → ((p4 ∧ (p5 → (True ∧ p3))) ∧ False)) ∨ p2))) ∨ p4) ∨ (p5 ∨ p2)) ∧ True) ∨ (p4 ∨ (p2 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345444610450796037400776310823 : (p3 → (((((p1 → False) → (((p5 → p2) ∧ (p5 ∧ (p2 ∧ (True ∧ p2)))) ∨ ((p3 ∨ p1) ∧ p2))) → (p5 ∧ True)) ∨ (p3 ∨ p4)) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66847326250324442738256031135 : ((True → (p4 → (((p2 ∨ p2) ∧ ((p1 ∨ (p4 ∨ (((p5 ∧ True) → p2) → ((p1 → (True ∨ p3)) → False)))) → False)) → (p1 ∧ p5)))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h7 : (p1 ∨ (p4 ∨ (((p5 ∧ True) → p2) → ((p1 → (True ∨ p3)) → False)))) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h2
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h8 := h5 h7
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h10 : (p1 ∨ (p4 ∨ (((p5 ∧ True) → p2) → ((p1 → (True ∨ p3)) → False)))) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h2
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h11 := h5 h10
    -- False on the left can always be used.
    apply False.elim h11
  -- Conjunctions on the left can always be decomposed.
  let h12 := h3.left
  let h13 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h12
  case inl h14 =>
    -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
    have h15 : (p1 ∨ (p4 ∨ (((p5 ∧ True) → p2) → ((p1 → (True ∨ p3)) → False)))) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h2
    -- We have shown the premise of h13, we can now drive its conclusion.
    let h16 := h13 h15
    -- False on the left can always be used.
    apply False.elim h16
  case inr h17 =>
    -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
    have h18 : (p1 ∨ (p4 ∨ (((p5 ∧ True) → p2) → ((p1 → (True ∨ p3)) → False)))) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h2
    -- We have shown the premise of h13, we can now drive its conclusion.
    let h19 := h13 h18
    -- False on the left can always be used.
    apply False.elim h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116731634685968915247111734292 : (((p3 ∧ p3) ∨ ((((p5 ∨ p2) ∧ (p2 ∨ False)) ∨ p4) ∧ (p2 ∨ (True ∨ ((False ∨ p5) → ((p2 ∨ p2) ∨ (p3 ∨ p5))))))) ∨ (True → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_255186594595186764478686950035 : ((p4 ∧ p4) → ((((True ∨ ((p2 → ((False → p4) → False)) ∨ True)) ∧ ((p5 → p1) ∧ ((p4 → (p1 ∧ p5)) ∧ p2))) ∨ (p4 ∧ False)) → p5)) := by
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
    cases h4
    case inl h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h5.left
      let h8 := h5.right
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Conjunctions on the left can always be decomposed.
      let h11 := h1.left
      let h12 := h1.right
      -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
      have h13 : p4 := by
        -- One of the premise coincides with the conclusion.
        exact h12
      -- We have shown the premise of h9, we can now drive its conclusion.
      let h14 := h9 h13
      -- We need to get the right conjuct of h14 based on <expert-advice>.
      let h15 := h14.right
      -- One of the premise coincides with the conclusion.
      exact h15
    case inr h16 =>
      -- Disjunctions on the left can always be decomposed.
      cases h16
      case inl h17 =>
        -- Conjunctions on the left can always be decomposed.
        let h18 := h5.left
        let h19 := h5.right
        -- Conjunctions on the left can always be decomposed.
        let h20 := h19.left
        let h21 := h19.right
        -- Conjunctions on the left can always be decomposed.
        let h22 := h1.left
        let h23 := h1.right
        -- We want to use the implication h20 based on <expert-advice>. So we show its premise.
        have h24 : p4 := by
          -- One of the premise coincides with the conclusion.
          exact h23
        -- We have shown the premise of h20, we can now drive its conclusion.
        let h25 := h20 h24
        -- We need to get the right conjuct of h25 based on <expert-advice>.
        let h26 := h25.right
        -- One of the premise coincides with the conclusion.
        exact h26
      case inr h27 =>
        -- Conjunctions on the left can always be decomposed.
        let h28 := h5.left
        let h29 := h5.right
        -- Conjunctions on the left can always be decomposed.
        let h30 := h29.left
        let h31 := h29.right
        -- Conjunctions on the left can always be decomposed.
        let h32 := h1.left
        let h33 := h1.right
        -- We want to use the implication h30 based on <expert-advice>. So we show its premise.
        have h34 : p4 := by
          -- One of the premise coincides with the conclusion.
          exact h33
        -- We have shown the premise of h30, we can now drive its conclusion.
        let h35 := h30 h34
        -- We need to get the right conjuct of h35 based on <expert-advice>.
        let h36 := h35.right
        -- One of the premise coincides with the conclusion.
        exact h36
  case inr h37 =>
    -- Conjunctions on the left can always be decomposed.
    let h38 := h37.left
    let h39 := h37.right
    -- False on the left can always be used.
    apply False.elim h39



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42655632960489380367031328820 : (((p4 ∨ (((p4 → (p1 ∨ ((p2 ∧ p4) ∧ ((p1 → p4) → (True ∧ (False ∧ p2)))))) ∧ ((True ∨ p2) ∧ p5)) ∨ (p5 ∧ False))) ∨ True) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_595811002078316453665711895301 : (((((p3 ∧ (False ∨ ((p4 ∨ ((p3 → True) → True)) ∨ p1))) ∧ ((p3 → False) ∨ ((p4 ∨ p5) ∧ ((p2 ∨ p4) ∨ (False ∧ p3))))) ∧ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113146195714550056123902227965 : (((p3 → (((p1 ∨ p2) → ((((p3 → (p3 → (((False ∨ False) ∧ p2) ∧ False))) ∧ True) ∧ p4) ∧ p4)) ∨ (False ∧ p5))) → False) ∨ (False → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_644790771798727713896341161382 : ((((p2 ∨ ((p3 ∧ (p3 ∨ (p4 ∧ ((p3 ∧ (False → (True ∧ ((p3 ∧ True) ∧ ((p5 ∧ (p1 → p1)) ∨ p3))))) ∨ True)))) ∨ p1)) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52988476134390957227633203981 : ((((True → (p5 → (((p1 → p3) ∧ p1) → False))) ∧ (p2 ∧ False)) ∧ (((True ∨ p3) ∧ ((p5 → p2) ∨ (p3 → p1))) ∨ (p2 ∨ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_573931235568978298062749096273 : (((p2 → ((p5 → ((p3 ∧ (p3 → (((p1 → p4) → p4) ∨ p3))) → (((p5 ∧ False) ∧ (p4 ∧ (p4 ∨ p1))) ∧ (False → p3)))) ∨ p2)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_936920162314766253495416889456 : ((((((True ∧ (p3 ∨ p5)) → True) → p5) ∧ (((p2 → p3) → (((False → p4) ∧ ((p2 ∨ p4) ∧ ((p5 ∧ p2) → p2))) ∧ p2)) ∧ p1)) → p5) ∧ True) := by
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
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h6 : ((True ∧ (p3 ∨ p5)) → True) := by
    -- Implications on the right can always be decomposed.
    intro h7
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h8 := h2 h6
  -- One of the premise coincides with the conclusion.
  exact h8
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171776979406018769362889898757 : ((((((((p3 ∨ p1) ∨ p5) ∨ True) ∨ (True ∧ p5)) → p2) ∧ (True → True)) → p3) ∨ (((p3 → ((p5 ∨ p4) → False)) ∧ (False ∧ p1)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47450255784518121357103577415 : (((p4 ∧ ((((p2 ∧ ((p1 ∧ (((p2 ∨ (True ∧ (p5 → (p2 ∨ True)))) → True) ∨ False)) ∧ False)) ∨ True) → p1) ∧ p1)) ∨ (p1 ∨ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244597409958594583065789549364 : ((False ∧ p4) ∨ (p1 ∨ ((((p3 ∨ True) ∧ p5) ∨ p4) ∨ ((False ∧ (p3 → (((False ∧ p1) ∨ (((True → p5) ∧ p2) → p4)) ∨ p5))) → p1)))) := by
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
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64035349618998723382017312635 : ((False ∨ ((((((p2 → True) → p5) → p1) ∨ p5) → (p4 → (True ∧ ((True → (p1 → (p2 → False))) ∧ p1)))) ∧ (p3 → (p3 ∧ p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191152613524982791402050374169 : ((((False ∨ p3) → False) ∨ ((p5 → p5) → (p3 ∧ p1))) ∨ ((((False ∧ p1) → ((p1 ∨ (p3 ∨ ((p5 ∨ True) ∨ True))) ∨ True)) ∨ p3) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_622419926848026497541304851247 : ((((p3 ∧ (((p3 → (p5 ∧ p2)) ∧ p4) ∨ ((p3 ∧ (p5 ∧ ((((p3 → (p1 ∨ True)) ∧ p4) → False) ∧ p4))) ∧ (p2 ∨ p2)))) ∨ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113347635043774595667783807633 : (((False ∧ (True → ((p3 ∨ (False ∧ ((p5 ∧ p1) → p3))) ∧ (((p3 → (p1 ∨ False)) → p2) → (p5 → p1))))) ∧ (False ∧ True)) ∨ (False ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257913824510252453311601485697 : ((p4 ∨ False) → ((((p3 ∧ (p1 ∨ p1)) ∨ (((((p5 ∨ p4) → (((p2 ∨ p5) → True) → p1)) ∨ p4) ∨ False) → p5)) ∨ (p1 ∨ p4)) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- False on the left can always be used.
    apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160257417926848789704158251851 : (((p3 ∧ ((p5 → (((p4 ∧ False) → (p3 ∧ p5)) → (p2 ∨ p3))) → (False ∧ p2))) ∨ (True ∧ p3)) → (p2 ∨ ((True → False) → (p4 ∧ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h5 : (p5 → (((p4 ∧ False) → (p3 ∧ p5)) → (p2 ∨ p3))) := by
      -- Implications on the right can always be decomposed.
      intro h6
      -- Implications on the right can always be decomposed.
      intro h7
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h8 := h4 h5
    -- We need to get the left conjuct of h8 based on <expert-advice>.
    let h9 := h8.left
    -- False on the left can always be used.
    apply False.elim h9
  case inr h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h13
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
    have h14 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h13, we can now drive its conclusion.
    let h15 := h13 h14
    -- False on the left can always be used.
    apply False.elim h15
    -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
    have h16 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h13, we can now drive its conclusion.
    let h17 := h13 h16
    -- False on the left can always be used.
    apply False.elim h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_655471334188484664496597089607 : (((((p5 ∨ ((p5 → (p1 ∧ ((p5 ∧ p3) → (p1 ∨ ((True → (True ∧ False)) ∧ (p1 → p5)))))) → p5)) ∨ (p4 ∨ True)) ∨ (True → p5)) ∨ p3) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114492631006074451852515246078 : ((((p5 ∨ (((p1 → (p2 ∧ p5)) → p4) ∨ (p3 ∨ p1))) → (False → (p1 → (p4 → p1)))) → (p3 ∧ (p1 ∨ (p3 → p4)))) ∨ (p2 → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323765397767116910905212763951 : (p5 ∨ (((p2 ∨ p2) → (p1 ∨ ((p4 ∨ ((p5 → (p4 → (p4 ∧ p5))) → (p5 → p3))) ∨ True))) ∧ (True ∨ (True → (False ∨ (p2 ∨ p1)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347131410144987096186903081607 : (p3 → (((((((p2 ∨ p3) ∧ p4) ∨ True) ∨ True) ∨ ((True ∨ p5) → p3)) → False) → (False ∧ ((p2 ∨ p2) → ((p5 ∧ p1) ∨ (p2 ∧ p2)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (((((p2 ∨ p3) ∧ p4) ∨ True) ∨ True) ∨ ((True ∨ p5) → p3)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- False on the left can always be used.
  apply False.elim h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h6
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h7
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_679481910831201584152374743625 : (((((((p1 → (((True ∧ (True → False)) ∨ ((False ∨ p1) → False)) ∨ (False ∧ True))) → True) → p4) ∧ p5) → ((p3 ∧ (p4 → p2)) ∨ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245362138645207480867120529031 : ((p2 ∧ p3) ∨ ((((p2 ∨ (((False ∨ False) ∨ p2) → ((p4 ∧ p5) ∨ (p2 ∨ p4)))) ∨ False) → False) ∨ (p1 ∨ (((p5 ∧ False) → p1) ∨ p1)))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39151024471054025234715471391 : ((((p1 ∨ True) → (((p2 ∨ p3) ∧ ((False → (False ∨ (p2 → True))) → (p4 ∧ (p1 ∧ (True → ((p3 ∨ p2) ∨ p5)))))) ∧ True)) ∧ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205463838145681345948534803627 : (((p2 → (True ∨ p4)) → (False ∧ p4)) ∨ ((((p3 ∧ p3) ∧ (p5 ∨ (True ∨ (p3 → (p4 ∧ (p4 ∧ (True ∧ p4))))))) ∧ p4) → (p3 ∧ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h8 =>
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h11 =>
      -- One of the premise coincides with the conclusion.
      exact h7
  -- Conjunctions on the left can always be decomposed.
  let h12 := h1.left
  let h13 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h14 := h12.left
  let h15 := h12.right
  -- Conjunctions on the left can always be decomposed.
  let h16 := h14.left
  let h17 := h14.right
  -- Disjunctions on the left can always be decomposed.
  cases h15
  case inl h18 =>
    -- One of the premise coincides with the conclusion.
    exact h17
  case inr h19 =>
    -- Disjunctions on the left can always be decomposed.
    cases h19
    case inl h20 =>
      -- One of the premise coincides with the conclusion.
      exact h17
    case inr h21 =>
      -- One of the premise coincides with the conclusion.
      exact h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185452473488421360160421553930 : ((False ∨ (True → (((True → p4) ∧ ((p4 → True) ∨ p1)) ∨ False))) ∨ (((p5 → p5) ∧ (((p5 → False) → p2) ∧ p3)) ∨ (p1 → (False → p4)))) := by
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
theorem thm_5_vars_300365016293249045411046505326 : (False ∨ (((((p1 ∧ ((((False ∧ (True ∨ p3)) → p4) → (p5 ∧ p2)) ∨ p3)) → ((p5 ∧ False) → p4)) ∨ p3) → p4) ∨ ((p5 ∧ p4) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337856885645535069190305471039 : (p1 → (((p2 → (False → ((p4 ∨ p3) ∧ (((p5 ∧ False) ∧ p2) ∨ p4)))) → p4) ∨ ((p5 ∨ ((False → (True → p5)) ∧ p2)) ∨ (p5 → True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177959090774963738858229904167 : ((((p3 ∧ False) ∨ ((((p3 ∨ True) ∧ (p1 ∧ p5)) ∨ p3) ∨ True)) ∨ p1) ∨ (p1 ∧ ((True ∧ p4) ∨ (p4 ∧ (False ∨ ((p4 → p2) ∧ False)))))) := by
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
theorem thm_5_vars_177975766709970412415933896965 : (((False ∧ ((p3 ∨ (p1 ∨ p1)) ∨ (p2 ∨ (True ∨ (True → p2))))) ∨ p4) ∨ ((p4 → (False → True)) ∨ (((True ∧ (False ∨ p5)) → p2) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136130398626140220364892914672 : (((((p4 ∧ p3) ∧ (p1 → (True → False))) ∧ p5) → (False ∨ (((p2 ∨ True) → ((p4 ∨ p4) ∧ (p4 → p5))) → p1))) ∨ ((True ∧ True) ∧ True)) := by
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
theorem thm_5_vars_49146419846718384783768646597 : ((((p5 ∧ (((p5 ∧ p1) → p4) ∨ (p1 ∨ (p4 ∨ p5)))) → ((True ∨ (True ∨ p3)) → ((True ∧ p2) ∨ p2))) ∨ (p2 ∧ (p1 ∨ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54657598042165685126758238404 : (((((p3 ∧ p4) ∨ (p1 ∨ (p2 ∧ p4))) ∨ p1) → (p2 ∧ (p4 → ((p4 ∧ ((True → p1) ∧ (True ∨ p5))) ∨ (p3 → (p3 → True)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234026466993065776790726896986 : ((p5 ∨ (True → p2)) → (((((((((p2 ∧ p1) → p3) ∨ False) → False) ∧ p3) → (p5 → (p1 ∧ p5))) ∧ True) → ((False ∨ False) ∧ p4)) → p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h5 : (((((((p2 ∧ p1) → p3) ∨ False) → False) ∧ p3) → (p5 → (p1 ∧ p5))) ∧ True) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h6
      -- Implications on the right can always be decomposed.
      intro h7
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Conjunctions on the left can always be decomposed.
      let h8 := h6.left
      let h9 := h6.right
      -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
      have h10 : (((p2 ∧ p1) → p3) ∨ False) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h11
        -- Conjunctions on the left can always be decomposed.
        let h12 := h11.left
        let h13 := h11.right
        -- One of the premise coincides with the conclusion.
        exact h9
      -- We have shown the premise of h8, we can now drive its conclusion.
      let h14 := h8 h10
      -- False on the left can always be used.
      apply False.elim h14
      -- Conjunctions on the left can always be decomposed.
      let h15 := h6.left
      let h16 := h6.right
      -- One of the premise coincides with the conclusion.
      exact h7
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h17 := h2 h5
    -- We need to get the left conjuct of h17 based on <expert-advice>.
    let h18 := h17.left
    -- Disjunctions on the left can always be decomposed.
    cases h18
    case inl h19 =>
      -- False on the left can always be used.
      apply False.elim h19
    case inr h20 =>
      -- False on the left can always be used.
      apply False.elim h20



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_747027470103332384892790902310 : ((((p4 ∨ p3) → ((p2 ∧ True) ∨ ((p3 ∨ ((p5 → (p3 → (True ∨ p2))) → ((p4 ∨ p3) ∧ (((p2 ∧ p1) ∧ p4) ∨ p5)))) ∨ p4))) ∨ p5) ∧ True) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_718563161144994679733639122227 : (((((p3 → (p3 ∨ True)) → p3) ∨ (((p1 ∧ (((p3 ∧ True) ∨ (True ∨ (True → True))) → (p4 ∨ (p5 ∨ p5)))) → (p2 ∨ False)) ∧ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307866583472883407659178985072 : (p1 ∨ (p5 → (((((p3 ∨ p2) → p4) ∧ ((p1 ∧ False) → p1)) → ((False ∧ (p1 → p5)) ∧ (p3 → p5))) ∨ (True ∧ ((False → p1) ∨ p5))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165836022137879259716955172965 : ((((p1 ∨ p2) ∧ p4) ∨ ((p2 ∧ p1) ∧ ((p2 → ((p5 ∨ True) ∧ (p4 → p1))) ∨ False))) ∨ (False → ((((False ∧ p3) → p1) ∨ p2) → False))) := by
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
theorem thm_5_vars_262245858388241291533739731178 : (True ∧ (((True ∨ ((((p1 ∧ p3) ∧ False) → ((True ∧ p1) → (True → ((p4 ∧ (p2 ∨ p4)) ∧ p2)))) ∨ (p2 ∨ p5))) → (False ∧ p2)) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_594989201107294128519967599716 : ((((((True ∧ (((True → (p5 ∧ (p3 → p5))) ∧ (p2 → p3)) → p5)) → False) ∨ ((p2 → (p4 ∧ ((p1 → p1) → p5))) ∧ False)) ∧ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_130357347973351024183958215755 : ((((p4 → (((p3 ∨ (p3 ∨ (True → p2))) → p2) ∧ (p5 ∨ (p5 ∨ p3)))) ∨ (True ∧ True)) ∧ (p5 ∨ (p1 ∨ True))) ∧ ((p2 ∨ False) → True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_749066438784714445901646088942 : ((((p5 → True) → ((p2 → ((p4 ∨ True) ∧ (p5 ∧ (p4 ∨ ((p3 ∧ p5) → p5))))) ∧ ((((p2 ∧ (p4 → False)) ∨ p3) ∧ p3) ∧ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_196218679372173967675446321412 : ((p1 ∨ ((True ∧ p1) → ((p3 → p1) ∨ p5))) ∧ (((p3 → (((False → (p5 ∨ False)) → (False → False)) ∨ p3)) → (True → p1)) ∨ (p3 → True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h4
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37897775747493295781499157568 : ((((((p5 ∧ p3) ∨ ((p2 ∧ (p3 ∨ ((p2 → (p2 ∧ (p4 → (True → p4)))) ∧ p5))) ∧ p4)) ∨ (p5 ∨ True)) ∧ (p3 ∨ True)) ∧ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150001933821133638288202900847 : ((p5 ∨ (((False → True) → (p3 ∧ (((p5 ∨ False) ∧ ((((p5 ∨ False) → p2) ∧ p1) ∧ p5)) ∨ False))) ∧ p3)) ∨ (True ∨ ((p3 → False) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47106492143345691116065689571 : ((((p4 ∧ (False ∨ ((((((p4 ∨ True) ∨ True) → (False ∨ True)) ∨ p5) ∨ (p5 ∧ p4)) ∧ p4))) ∧ (p3 ∨ (p1 ∧ False))) ∨ (True ∧ True)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_752533846915640977267171518749 : (((False ∧ ((p1 ∨ (p4 ∨ (((((p4 ∧ p5) ∧ ((p2 → p1) ∧ p2)) ∨ ((p2 → p3) ∧ False)) → ((False ∧ p5) ∨ True)) → False))) ∧ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_21015644934305377074919329360 : (((((False ∧ ((p3 ∧ p5) ∨ (True ∧ (True ∧ p4)))) → False) → False) → ((((((p2 → (p4 → p2)) → False) ∨ p3) → False) → p2) ∨ p3)) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((False ∧ ((p3 ∧ p5) ∨ (True ∧ (True ∧ p4)))) → False) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- False on the left can always be used.
    apply False.elim h4
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h2
  -- False on the left can always be used.
  apply False.elim h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214566529197235123798039658095 : (((p1 ∨ p5) ∧ (p5 → p5)) ∨ (((True ∧ (p1 ∧ p1)) ∨ (p4 → (p5 ∨ (p3 ∧ (p1 → (p5 ∨ ((p5 ∧ p2) ∧ p1))))))) ∨ (p3 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_221923649834818715091918890826 : (((p5 ∧ p3) → True) ∧ (p5 ∨ (((p1 → p1) ∧ p1) → (((p3 ∨ (p1 ∨ (p3 → (p5 ∧ p2)))) → p4) ∨ ((False ∨ (p3 ∨ p2)) ∨ True))))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118453900493919537053234431172 : ((p3 ∨ (((((p5 ∨ False) ∧ False) ∨ (((p3 ∧ p4) ∨ p5) → (p1 ∧ ((True → p4) → (p1 → (p5 ∧ p4)))))) ∧ p3) ∨ p3)) ∨ (p1 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115766480033754632184889925661 : (((p5 ∨ ((p3 → p3) ∧ (p4 ∨ False))) → (((p4 ∧ (((p5 ∧ p3) ∨ (False ∧ (p4 → (p1 ∧ p5)))) ∨ True)) → False) ∧ p5)) ∨ (False → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227351783642806986847740970742 : (((p3 → p2) → p2) ∨ ((p1 ∨ (((p3 ∨ p2) ∨ (True → p3)) ∨ (((((p1 ∧ p5) ∧ p5) ∧ p5) → (p2 ∨ p4)) ∨ (True ∨ p5)))) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_229038224058859598699871558085 : ((p5 ∨ (p1 ∨ p1)) ∨ (((p4 ∧ ((p5 → True) ∨ p4)) ∨ False) → ((p1 → True) ∧ ((p3 ∨ ((p1 ∨ p2) → p4)) ∨ ((p3 ∨ p4) ∨ p4))))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h7
  case inr h8 =>
    -- False on the left can always be used.
    apply False.elim h8



