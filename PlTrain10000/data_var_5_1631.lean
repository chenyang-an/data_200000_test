variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_756171587482046552971455636580 : (((p1 ∧ ((True → ((p3 → ((p3 ∨ (p1 ∨ ((False → ((p4 ∧ p3) ∨ (p4 ∨ (p2 → False)))) ∧ p2))) ∧ p1)) ∨ p2)) ∧ (p1 ∧ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232391947642604196627729419388 : (((p5 → p2) → p4) → (((p5 → (((p1 ∨ False) → (p3 ∧ p3)) ∨ (p2 ∨ p2))) → p3) ∨ (((True → p2) ∧ (p4 ∧ p4)) → (p3 ∨ True)))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_687191618696928995482340509932 : ((((p4 → (p4 → ((p3 → (p3 ∧ ((p5 ∨ (((False ∨ p5) ∧ p2) → p4)) → False))) → p2))) → ((p2 → p5) ∨ ((True ∧ p4) ∧ True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305444530509666608031342238554 : (p1 ∨ (((p4 ∧ p3) ∧ (((p4 → p2) ∨ (p3 → ((False → p3) ∨ False))) ∨ (p4 ∨ p2))) → ((False ∨ ((p4 ∨ (p2 ∨ False)) → p4)) ∨ False))) := by
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
  cases h3
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- One of the premise coincides with the conclusion.
        exact h9
      case inr h10 =>
        -- Disjunctions on the left can always be decomposed.
        cases h10
        case inl h11 =>
          -- One of the premise coincides with the conclusion.
          exact h4
        case inr h12 =>
          -- False on the left can always be used.
          apply False.elim h12
    case inr h13 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h14
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h15 =>
        -- One of the premise coincides with the conclusion.
        exact h15
      case inr h16 =>
        -- Disjunctions on the left can always be decomposed.
        cases h16
        case inl h17 =>
          -- One of the premise coincides with the conclusion.
          exact h4
        case inr h18 =>
          -- False on the left can always be used.
          apply False.elim h18
  case inr h19 =>
    -- Disjunctions on the left can always be decomposed.
    cases h19
    case inl h20 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h21
      -- Disjunctions on the left can always be decomposed.
      cases h21
      case inl h22 =>
        -- One of the premise coincides with the conclusion.
        exact h22
      case inr h23 =>
        -- Disjunctions on the left can always be decomposed.
        cases h23
        case inl h24 =>
          -- One of the premise coincides with the conclusion.
          exact h20
        case inr h25 =>
          -- False on the left can always be used.
          apply False.elim h25
    case inr h26 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h27
      -- Disjunctions on the left can always be decomposed.
      cases h27
      case inl h28 =>
        -- One of the premise coincides with the conclusion.
        exact h28
      case inr h29 =>
        -- Disjunctions on the left can always be decomposed.
        cases h29
        case inl h30 =>
          -- One of the premise coincides with the conclusion.
          exact h4
        case inr h31 =>
          -- False on the left can always be used.
          apply False.elim h31



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_608263696920694244667926410582 : (((((((((p2 ∨ (p3 ∨ ((((True ∧ False) ∨ p3) ∨ ((p5 ∧ True) → True)) ∨ p5))) ∧ False) → (p1 → p2)) → p5) ∨ True) ∨ p1) ∨ p1) ∨ False) ∧ True) := by
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
theorem thm_5_vars_158182017288726112558124969098 : (((p2 ∧ (p3 → (p3 ∧ p4))) → (p1 → ((((True ∧ (False ∧ False)) ∨ (p3 ∧ p4)) → False) ∨ p1))) ∨ (True ∧ ((p4 → (p3 ∧ p4)) → True))) := by
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
theorem thm_5_vars_19522536497978622016035530221 : (((((p4 → (((p2 ∨ ((p3 ∨ (True → False)) ∨ True)) ∧ p1) ∨ p5)) ∨ p5) → p4) ∨ (((True ∨ p1) ∨ (p4 ∨ p5)) ∨ (p1 ∨ p5))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_590511111927951109825672984101 : ((((((p4 ∨ p4) → (((((p5 ∧ p5) ∨ p1) ∨ True) → ((True ∧ ((p4 ∧ p1) ∨ p4)) ∨ (p1 ∨ p4))) ∧ (p3 ∨ p3))) → p2) ∧ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55906812732027451463036679289 : (((p4 ∨ (False → (p2 → False))) ∧ ((p2 ∨ (((p2 ∨ ((((p5 ∧ p1) ∨ True) ∧ p4) → (False ∧ p2))) ∨ (True ∨ p1)) ∨ p3)) ∨ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159099098966925222830019211210 : ((True → ((p4 → (p1 → p2)) ∧ ((p3 ∨ (False → p1)) ∧ ((p2 ∧ (p1 ∧ (True ∧ p3))) ∧ p1)))) ∨ (((p4 ∧ p2) ∧ True) ∨ (False → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_123243281092055710896934245884 : ((((p2 → ((p4 → True) ∨ p5)) → (p2 ∧ (p2 ∨ (p5 → ((p4 ∧ (p2 ∧ False)) → True))))) ∧ (p1 → ((p5 → p5) → p2))) → (p2 ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (p2 → ((p4 → True) ∨ p5)) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h6
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h7 := h2 h4
  -- We need to get the left conjuct of h7 based on <expert-advice>.
  let h8 := h7.left
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_250844835768464650885628564514 : ((p1 → p2) ∨ ((p5 → p2) → (((True ∧ (True ∧ ((((p2 ∨ p4) ∧ p5) ∨ ((p4 ∧ False) → False)) → (False ∧ p2)))) → p4) ∧ (False ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  let h5 := h4.left
  let h6 := h4.right
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h7 : (((p2 ∨ p4) ∧ p5) ∨ ((p4 ∧ False) → False)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- False on the left can always be used.
    apply False.elim h10
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h11 := h6 h7
  -- We need to get the left conjuct of h11 based on <expert-advice>.
  let h12 := h11.left
  -- False on the left can always be used.
  apply False.elim h12
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164971610684835804226496719362 : (((((p1 ∨ (p2 ∨ ((p1 → p2) ∧ p3))) → (p2 → (True ∧ False))) ∨ (p4 ∧ False)) → False) ∨ ((((p4 ∧ (p1 → p1)) ∧ p3) → p3) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- One of the premise coincides with the conclusion.
  exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_657875304236778397891796951423 : ((((False ∧ (True → (((p1 ∨ ((p1 ∨ ((False → p5) → True)) ∧ False)) → (p5 → ((p1 ∧ (p4 ∧ False)) → p3))) → p3))) ∨ (p4 ∨ True)) ∨ False) ∧ True) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_729286627149573258070977929950 : (((((True ∧ p4) ∨ p5) → (p1 → (True ∧ (p2 ∧ (False ∧ ((p4 → ((((p1 → p4) ∨ (p2 ∧ (False ∨ p2))) ∧ False) ∨ p2)) ∧ True)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_688321999342614371475317132731 : (((((p4 ∨ p4) → (p2 → ((p5 ∨ (p3 → p3)) → (p3 → (p3 → (p4 → False)))))) ∧ ((((p3 ∧ p5) ∨ False) ∧ (p5 ∨ p1)) ∧ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1462169804271499583005794629 : ((((True → False) ∧ ((p3 ∨ (p2 → (p4 → (((p5 ∨ p3) ∨ (True → True)) ∨ (p3 ∨ p2))))) ∧ (True ∧ False))) ∧ p4) ∨ (True ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_142966273890212194004624114844 : ((True → ((((((False ∨ (False → (p1 ∨ False))) ∧ (p4 → (p3 ∨ p3))) ∧ ((p4 ∨ True) ∨ True)) ∧ True) ∧ True) ∧ p2)) → ((p5 ∨ p2) ∨ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116752257034866826377538851974 : (((p5 ∧ p2) ∨ (((p5 → p5) ∨ True) → (((False ∨ p1) → (p5 ∨ ((True ∧ (((False ∨ p2) → p5) ∨ p4)) ∧ p2))) ∨ True))) ∨ (p5 ∨ p5)) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58367172949883742566076409913 : (((p1 ∨ p1) ∧ ((True ∨ ((False → (p2 ∨ (False ∧ ((p2 ∨ ((False ∧ (True → (True → True))) ∨ p3)) → (True ∧ True))))) ∨ p2)) → p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_33062901848200318314063202023 : ((p3 ∨ (((p5 ∧ p3) ∧ p3) → ((p1 ∨ ((((p1 ∧ ((p3 ∧ (p5 ∨ True)) ∨ True)) ∨ (p1 → False)) ∨ (p4 ∨ p2)) ∨ p4)) ∨ p5))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208936823708038399977344600615 : ((p5 ∧ (False → ((p3 ∧ p4) → True))) → (((p4 ∧ ((p1 ∧ p2) ∨ p4)) → (p5 ∧ (p1 ∧ (p4 ∨ p3)))) → (p1 → ((p1 → p2) ∨ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67764452357243418683621666235 : ((p2 → (((((((p3 ∧ (p2 ∧ p3)) ∧ p3) ∧ (p1 ∨ True)) ∨ True) ∧ p2) ∧ ((((p1 ∨ (p3 ∨ p2)) ∨ p5) ∧ p1) → p5)) ∨ True)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177851154225297595362497642153 : (((((((p5 ∨ p4) ∨ (p5 → p4)) ∧ (p2 ∨ p4)) ∧ p4) ∨ p2) ∨ p1) ∨ ((((p2 ∧ (p1 → p2)) → (p2 → True)) ∨ (p2 → p1)) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49335828097361714203685606803 : (((True → (((((((False → p5) → ((p2 ∧ ((p1 ∧ False) ∧ p2)) → p5)) → p5) → p2) → False) ∨ p3) ∨ True)) ∨ ((p3 ∧ p4) ∧ p5)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341748621904207634780779923583 : (p2 → ((p3 ∧ (((((p3 ∧ p1) ∧ (((False ∨ False) ∨ p3) ∧ False)) ∨ (p2 ∧ p4)) ∨ ((p3 → p3) ∨ p1)) ∧ (p3 → True))) ∨ (False → p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167935010664580217228684773203 : ((((False ∧ p3) → (False ∧ ((False ∨ p4) → False))) ∨ (((p1 ∨ p4) ∨ (p2 ∧ p1)) ∨ p3)) → ((p2 ∧ (p5 ∧ ((p4 → p2) ∨ False))) ∨ True)) := by
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
        -- Disjunctions on the left can always be decomposed.
        cases h5
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
theorem thm_5_vars_59585703102899575999338699254 : (((p4 → False) ∨ (p3 → ((((((True → p2) ∧ p5) ∧ p1) ∧ ((((p4 ∧ (p1 ∨ True)) → (p4 ∧ p3)) ∨ p1) → p2)) ∨ True) → p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213388368811948719658267324289 : (((False ∨ (p1 ∧ True)) ∧ p4) ∨ (p5 ∨ (p2 → ((p4 ∨ (((p3 ∧ ((p1 ∨ p4) ∨ p4)) ∨ p2) ∨ ((p2 ∧ (False ∨ False)) ∨ p4))) ∨ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_330235026206947697911407173205 : (True → (False ∨ (((p2 → (p3 ∧ ((((True → p4) ∨ (p1 ∧ p3)) → False) ∧ (((True ∧ (p5 → (p5 ∧ p5))) → p4) ∧ False)))) → p1) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206012308210048396851039362103 : ((p2 ∧ ((p1 ∨ (p4 ∨ p4)) ∧ p4)) ∨ ((False ∧ p5) ∨ ((p1 ∨ (((p1 ∨ (p2 ∨ (p4 → (True ∨ p4)))) ∧ p3) → (p3 ∨ p2))) ∧ True))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
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
      exact h3
    case inr h7 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_705182009691737639024091651425 : (((((((p1 ∧ p4) ∧ False) ∨ (True ∨ p3)) ∧ p1) ∧ (((p2 → p5) ∨ False) ∧ ((p1 ∧ p3) → (p1 → (((p1 → p1) ∨ p4) ∨ p1))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41103761569706697023906125009 : ((((((p5 → (False ∨ p1)) → p3) ∧ ((True → p1) → (p2 ∨ ((((p3 ∨ False) ∨ True) → p3) → p4)))) ∧ ((p3 ∧ p1) ∧ p3)) ∨ True) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168835275770766415065284072181 : ((p3 ∨ (((((p5 ∨ False) ∨ ((p5 ∧ p3) ∧ p4)) ∨ p4) ∧ (p4 → True)) ∧ (True ∨ p4))) → ((p1 ∧ (p1 ∧ (p4 ∧ p4))) ∨ (False → p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Disjunctions on the left can always be decomposed.
        cases h10
        case inl h11 =>
          -- Disjunctions on the left can always be decomposed.
          cases h6
          case inl h12 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h13
            -- False on the left can always be used.
            apply False.elim h13
          case inr h14 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h15
            -- False on the left can always be used.
            apply False.elim h15
        case inr h16 =>
          -- False on the left can always be used.
          apply False.elim h16
      case inr h17 =>
        -- Conjunctions on the left can always be decomposed.
        let h18 := h17.left
        let h19 := h17.right
        -- Conjunctions on the left can always be decomposed.
        let h20 := h18.left
        let h21 := h18.right
        -- Disjunctions on the left can always be decomposed.
        cases h6
        case inl h22 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h23
          -- False on the left can always be used.
          apply False.elim h23
        case inr h24 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h25
          -- False on the left can always be used.
          apply False.elim h25
    case inr h26 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h27 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h28
        -- False on the left can always be used.
        apply False.elim h28
      case inr h29 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h30
        -- False on the left can always be used.
        apply False.elim h30



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200353672265584378542328681066 : (((True → p2) ∧ ((True → p5) ∨ (p3 → True))) → (p2 ∧ ((False ∨ ((p3 ∧ p5) → (p3 ∧ p2))) ∨ (((p2 ∧ p1) ∨ (p3 ∨ False)) ∨ p5)))) := by
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
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h5 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h6 := h2 h5
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h8 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h9 := h2 h8
    -- One of the premise coincides with the conclusion.
    exact h9
  -- Conjunctions on the left can always be decomposed.
  let h10 := h1.left
  let h11 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h11
  case inl h12 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
    have h13 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h12, we can now drive its conclusion.
    let h14 := h12 h13
    -- One of the premise coincides with the conclusion.
    exact h14
  case inr h15 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h16
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the left can always be decomposed.
    let h17 := h16.left
    let h18 := h16.right
    -- One of the premise coincides with the conclusion.
    exact h17
    -- Conjunctions on the left can always be decomposed.
    let h19 := h16.left
    let h20 := h16.right
    -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
    have h21 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h10, we can now drive its conclusion.
    let h22 := h10 h21
    -- One of the premise coincides with the conclusion.
    exact h22



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112245573307094838584185393125 : (((p3 ∨ (((p1 ∨ True) → False) ∨ (p3 ∧ (p1 ∧ (True → ((False ∨ (p3 → (p2 ∨ ((p1 ∧ True) → p4)))) ∨ p5)))))) ∨ True) ∨ (p5 → True)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_918990687988907912126248236940 : (((((True ∧ (p3 ∨ (False → ((p5 → (False ∧ p2)) ∧ p1)))) ∧ (False ∨ p1)) ∧ (((((False ∧ p3) → False) ∨ True) → False) ∧ (p2 ∧ p1))) → False) ∧ True) := by
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
  let h6 := h4.left
  let h7 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h9 =>
      -- False on the left can always be used.
      apply False.elim h9
    case inr h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h3.left
      let h12 := h3.right
      -- Conjunctions on the left can always be decomposed.
      let h13 := h12.left
      let h14 := h12.right
      -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
      have h15 : (((False ∧ p3) → False) ∨ True) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h11, we can now drive its conclusion.
      let h16 := h11 h15
      -- False on the left can always be used.
      apply False.elim h16
  case inr h17 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h18 =>
      -- False on the left can always be used.
      apply False.elim h18
    case inr h19 =>
      -- Conjunctions on the left can always be decomposed.
      let h20 := h3.left
      let h21 := h3.right
      -- Conjunctions on the left can always be decomposed.
      let h22 := h21.left
      let h23 := h21.right
      -- We want to use the implication h20 based on <expert-advice>. So we show its premise.
      have h24 : (((False ∧ p3) → False) ∨ True) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h20, we can now drive its conclusion.
      let h25 := h20 h24
      -- False on the left can always be used.
      apply False.elim h25
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_325672974435474196007724711602 : (p5 ∨ (p1 ∨ ((((p4 ∧ False) ∧ ((p2 ∧ ((p1 ∧ p3) ∧ (True → (p4 ∨ (True → True))))) ∧ (True ∨ (p3 ∨ p4)))) ∨ (p2 → p2)) ∨ p4))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134300421132839729343787717223 : ((((p5 ∨ p1) → (True ∧ ((p1 ∨ (p4 ∨ (p1 → False))) → ((p5 ∧ True) ∨ (p5 → ((p5 → False) ∨ p5)))))) ∨ True) ∨ ((p3 ∧ p4) → p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56886240343971151431359817174 : (((p2 ∧ (p4 → p2)) ∧ ((((p1 ∧ False) ∧ p3) ∧ (p5 → ((p5 ∧ ((False ∨ (p1 → False)) ∨ (True ∨ False))) ∨ p2))) ∨ (False → p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_69303771234420783242686763588 : ((p5 → (p1 ∧ (((p4 ∨ p5) ∧ True) ∧ (False ∧ ((((p2 → p5) ∧ True) → p3) ∨ (((p3 → (p2 → p1)) → p2) ∨ (p2 ∨ True))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159177633822765247379113295066 : ((p1 → ((True ∨ p1) → (((((True ∨ ((p1 → p1) ∧ p4)) → p1) → (p4 ∧ False)) ∨ p2) ∨ p1))) ∨ ((p1 ∧ p1) ∨ ((p1 ∧ p4) → p5))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160277207332599129084773293790 : (((((False → (p3 → ((True → (p3 → ((p5 → p4) → p2))) ∧ p3))) → p5) ∧ False) → (p2 ∨ p2)) → ((p1 ∧ p2) → (p1 → (p2 ∨ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
theorem thm_5_vars_767980546024739463481235931859 : (((p5 ∧ ((True → ((True ∨ ((True → p1) → (p5 → ((p3 → (p2 ∨ p4)) ∧ True)))) → ((p1 ∧ (p2 ∨ (p2 ∧ False))) ∨ p3))) → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_673357410602763853762660689251 : ((((((((p1 → p2) ∨ p5) → False) ∨ False) ∨ (((p5 ∨ p3) ∨ ((((p5 ∨ p2) → True) ∧ True) → False)) → p1)) → (p5 ∧ (p3 → p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_788623427939152256878969741472 : (((p5 ∨ (((((True ∧ (p3 ∨ (False → (p3 → True)))) ∨ (False ∨ p5)) → (((p5 → p1) ∨ p4) ∧ ((p5 ∧ False) ∨ p2))) → p5) → p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_718254543294933642305300863010 : (((((p3 → (False ∧ p1)) ∨ p1) ∨ ((((p1 ∨ (p4 → (p1 ∨ False))) ∧ (((p2 ∧ (p4 ∨ False)) ∧ False) ∧ False)) ∨ (p1 ∨ p3)) ∨ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_624986540366351996570975598333 : ((((p5 ∨ (p4 ∨ (p3 ∧ (((p1 ∧ (p3 → ((((p5 ∨ p4) ∨ p5) ∧ (p5 → p3)) ∧ p1))) ∧ ((p4 ∧ p1) ∧ p4)) ∧ p3)))) ∨ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_142293539304512605217622216092 : ((p2 ∧ (False ∨ ((((p5 ∨ p1) → p1) ∨ ((((True ∧ p4) → p5) → (((True → p2) ∨ False) ∧ p2)) ∨ False)) ∨ p2))) → ((p5 ∧ p3) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h2
      case inr h8 =>
        -- Disjunctions on the left can always be decomposed.
        cases h8
        case inl h9 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h2
        case inr h10 =>
          -- False on the left can always be used.
          apply False.elim h10
    case inr h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217015863425101314900713238723 : ((((p2 ∧ p3) ∧ p5) ∨ p3) → (((True → p5) ∧ (p5 ∨ ((p5 ∨ p4) ∧ ((p4 ∨ True) ∨ (((p3 ∧ p3) ∨ p5) → p3))))) ∨ (True ∨ p3))) := by
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
theorem thm_5_vars_114372555251444100948526358642 : ((((p2 ∨ ((((((True → p4) ∧ p2) ∨ p5) ∨ p5) ∨ ((p4 → False) → p3)) → p1)) ∨ False) ∨ (((p2 ∧ p5) → p5) ∨ False)) ∨ (p1 ∨ p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113847781039736379045748705931 : (((p5 ∨ (p3 ∨ (((p4 ∨ p2) ∨ (p3 ∨ p4)) ∧ ((p1 ∨ ((p2 ∨ False) → p1)) → ((p2 → False) ∨ True))))) → (False ∧ p5)) ∨ (False → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50240723619158992048889314604 : (((((p5 ∧ ((p4 ∨ (True ∨ (p3 ∨ p2))) → ((p2 → (p5 ∧ p2)) ∧ True))) ∧ (p1 ∧ p3)) → False) ∨ (((p5 ∧ True) ∧ p1) ∨ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354718271861945201617143158542 : (p5 → ((((((p2 → False) ∧ (p5 → p1)) ∧ p5) ∧ (((p3 ∧ (False ∧ p5)) ∧ ((p2 ∧ p4) ∨ p4)) ∨ p1)) ∨ (p4 ∨ (False ∨ p5))) ∨ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119375680524021146548303558807 : ((p3 → (p5 ∨ (p1 ∨ (p4 ∧ (((p2 ∨ p4) → p4) → (p1 ∨ (False ∧ ((p3 → ((p1 ∧ p5) ∨ False)) ∧ (p3 ∧ p2))))))))) ∨ (True ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_318664966326151775847590795874 : (p4 ∨ (((((p3 → p4) ∧ ((p3 ∧ ((p1 ∧ p5) ∨ p4)) → p5)) ∧ ((p2 → (True ∧ p3)) ∧ ((p2 ∧ p5) ∨ p1))) ∧ p3) → (p3 → p4))) := by
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
  let h5 := h3.left
  let h6 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- Conjunctions on the left can always be decomposed.
  let h9 := h6.left
  let h10 := h6.right
  -- Disjunctions on the left can always be decomposed.
  cases h10
  case inl h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h14 : p3 := by
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h15 := h7 h14
    -- One of the premise coincides with the conclusion.
    exact h15
  case inr h16 =>
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h17 : p3 := by
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h18 := h7 h17
    -- One of the premise coincides with the conclusion.
    exact h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177844531568175529723508134444 : ((((p1 ∧ ((p4 → p2) → (((p2 ∨ True) → p4) ∨ False))) ∧ p3) ∨ p1) ∨ (((((p4 ∨ False) → False) ∧ (p2 ∧ p4)) ∧ (True ∨ p2)) → p4)) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h8 =>
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h9 =>
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_302573563946979016195282178658 : (False ∨ (p1 ∨ ((p4 ∨ (((p4 ∧ ((p3 ∨ True) ∨ (((True → p5) ∨ (p5 ∨ (p3 → p5))) ∨ p5))) → p1) → p5)) ∨ (True ∨ (p2 → p5))))) := by
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
theorem thm_5_vars_624386973333817873144345497894 : ((((p3 ∨ ((p1 → p2) → ((((((True ∧ False) → ((p5 ∧ p2) ∧ (False ∨ (p5 ∧ True)))) ∧ p4) → (p1 ∨ p4)) → p5) ∧ p2))) ∨ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230329054936572663551505211693 : (((p2 ∨ True) ∧ p5) → (((p1 ∨ (p2 ∧ p3)) → (((p3 → (p1 ∧ (p4 ∧ True))) ∧ p1) ∨ p3)) → ((p5 ∧ p1) ∨ ((p4 ∨ True) ∨ p2)))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234711770126835004912557736155 : ((p4 → (p2 ∨ p1)) → ((True → (p2 ∧ (False ∨ ((p2 ∨ ((((p3 ∨ True) ∧ p5) ∨ (p5 ∧ (p5 ∨ True))) → True)) ∧ False)))) ∨ (False → p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_952181914740713955894434634383 : (((((p5 ∧ p2) ∧ p4) ∨ ((p4 ∧ p2) ∨ ((True ∧ (((True ∧ p4) → True) ∨ (p5 ∧ (p5 → p3)))) ∧ (True → ((p5 → p1) ∧ p2))))) → p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- One of the premise coincides with the conclusion.
      exact h10
    case inr h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- Conjunctions on the left can always be decomposed.
      let h14 := h12.left
      let h15 := h12.right
      -- Disjunctions on the left can always be decomposed.
      cases h15
      case inl h16 =>
        -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
        have h17 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h13, we can now drive its conclusion.
        let h18 := h13 h17
        -- We need to get the right conjuct of h18 based on <expert-advice>.
        let h19 := h18.right
        -- One of the premise coincides with the conclusion.
        exact h19
      case inr h20 =>
        -- Conjunctions on the left can always be decomposed.
        let h21 := h20.left
        let h22 := h20.right
        -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
        have h23 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h13, we can now drive its conclusion.
        let h24 := h13 h23
        -- We need to get the right conjuct of h24 based on <expert-advice>.
        let h25 := h24.right
        -- One of the premise coincides with the conclusion.
        exact h25
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_611962132538170430479567438908 : (((((((((p5 ∧ (((((p1 ∧ p3) ∧ (False ∨ False)) ∨ p2) → p1) ∧ p2)) ∨ (p4 → p3)) ∧ p3) → False) ∨ p4) ∧ (False ∨ p3)) ∨ True) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_808645170382650199887808371152 : (((p4 → (p1 → ((p2 → (((p4 → p5) → (((True ∨ (p4 ∧ p5)) ∧ ((False → p3) ∨ p1)) → ((p3 ∨ True) ∧ p3))) ∨ False)) ∧ True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67735167873705880309850716152 : ((p2 → ((True ∧ (((((p1 ∨ ((p2 → (p1 ∧ (((p5 ∨ p1) → p3) → p2))) ∨ p2)) → p5) ∧ (p5 ∧ p1)) ∨ p4) ∧ p4)) ∧ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_950243735673482956024162575781 : (((((False → False) → False) ∧ ((False ∧ p5) ∨ (((p2 ∨ (((p2 ∨ p1) ∨ p4) ∨ (p1 ∨ p2))) → (((False ∨ False) ∧ False) ∨ p2)) ∨ p1))) → p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- False on the left can always be used.
    apply False.elim h5
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h9 : (False → False) := by
        -- Implications on the right can always be decomposed.
        intro h10
        -- False on the left can always be used.
        apply False.elim h10
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h11 := h2 h9
      -- False on the left can always be used.
      apply False.elim h11
    case inr h12 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h13 : (False → False) := by
        -- Implications on the right can always be decomposed.
        intro h14
        -- False on the left can always be used.
        apply False.elim h14
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h15 := h2 h13
      -- False on the left can always be used.
      apply False.elim h15
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_721735106855990628547873712216 : ((((p1 ∨ ((p5 → p2) ∨ True)) → ((p3 → ((False ∧ p5) ∨ (p3 → p5))) ∨ ((p5 → (False → (True ∨ False))) ∧ ((p5 ∧ False) ∨ True)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258850483743097009462191662452 : ((True → p1) → ((((p2 ∧ (p1 → True)) ∨ p2) → True) ∧ (((p3 ∧ (p2 ∨ ((p1 ∨ p2) → p1))) ∧ ((p5 ∧ p4) ∨ False)) ∨ (p1 ∨ p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49386153805694581389047615212 : (((((p3 ∧ (p3 ∨ (p5 ∨ ((((p1 ∨ p5) ∨ (p5 ∧ p4)) ∨ (p2 ∨ (p3 ∧ p5))) ∨ False)))) ∨ p5) ∧ p1) → (p4 ∨ (p3 → p3))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    cases h6
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h11
        -- One of the premise coincides with the conclusion.
        exact h11
      case inr h12 =>
        -- Disjunctions on the left can always be decomposed.
        cases h12
        case inl h13 =>
          -- Disjunctions on the left can always be decomposed.
          cases h13
          case inl h14 =>
            -- Disjunctions on the left can always be decomposed.
            cases h14
            case inl h15 =>
              -- Disjunctions on the left can always be decomposed.
              cases h15
              case inl h16 =>
                -- Show the right disjunct based on <expert-advice>.
                apply Or.inr
                -- Implications on the right can always be decomposed.
                intro h17
                -- One of the premise coincides with the conclusion.
                exact h17
              case inr h18 =>
                -- Show the right disjunct based on <expert-advice>.
                apply Or.inr
                -- Implications on the right can always be decomposed.
                intro h19
                -- One of the premise coincides with the conclusion.
                exact h19
            case inr h20 =>
              -- Conjunctions on the left can always be decomposed.
              let h21 := h20.left
              let h22 := h20.right
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
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
              -- Conjunctions on the left can always be decomposed.
              let h27 := h26.left
              let h28 := h26.right
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- Implications on the right can always be decomposed.
              intro h29
              -- One of the premise coincides with the conclusion.
              exact h29
        case inr h30 =>
          -- False on the left can always be used.
          apply False.elim h30
  case inr h31 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h32
    -- One of the premise coincides with the conclusion.
    exact h32



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148077824922706310865888287951 : ((((p5 → (((p2 ∨ (((p3 ∨ p4) ∧ p4) ∨ False)) ∨ p5) → ((p4 → p4) ∨ p1))) ∧ p2) → (p3 ∨ p1)) ∨ ((p1 → p1) ∨ (p4 → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177645010412816593147570283593 : ((((p4 → (((p3 → False) ∨ (p5 ∧ (p4 → p1))) ∨ p5)) ∧ True) ∧ p4) ∨ (p4 ∨ (True ∧ (p4 → (False → (((p3 ∧ p2) → p3) ∧ False)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
  -- False on the left can always be used.
  apply False.elim h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_760903359937235767095324698287 : (((p2 ∧ (p4 ∨ (p4 ∧ (((True → ((False ∨ (True ∧ True)) ∨ (((p4 ∨ True) ∨ p5) ∨ p4))) → p5) → (False ∧ ((p1 ∧ True) ∧ False)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113164114824635920503318293087 : (((p4 → (p2 → (((p5 → p3) ∨ False) ∧ (p5 ∨ ((False ∨ True) ∧ ((p2 → p2) ∨ (True ∨ (True → (p1 ∧ True))))))))) → False) ∨ (False → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115551838841640435620433365134 : ((((((p4 ∧ p1) → p4) → False) ∧ p3) ∧ ((((True ∨ ((p4 ∨ p1) → (p4 → (p3 ∧ p3)))) ∧ p1) ∨ (p1 → True)) ∧ True)) ∨ (True ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40888044688202547869750105032 : (((((p3 ∧ (p5 ∨ ((p3 ∧ (p2 ∧ False)) → p1))) ∨ ((((p1 ∨ p1) ∧ True) ∧ (p4 ∨ (True → p3))) ∨ p5)) ∧ (True → True)) ∨ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_261437309055454615815264336119 : ((p5 → p2) → (((((p5 ∨ (False ∨ p1)) → (p2 → p2)) ∨ p3) → (p2 ∨ ((False ∧ (True ∨ p3)) → (p3 ∧ (p3 → (p1 ∨ True)))))) ∨ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- False on the left can always be used.
    apply False.elim h5
    -- Implications on the right can always be decomposed.
    intro h7
    -- Conjunctions on the left can always be decomposed.
    let h8 := h4.left
    let h9 := h4.right
    -- False on the left can always be used.
    apply False.elim h8
  case inr h10 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h11
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- False on the left can always be used.
    apply False.elim h12
    -- Implications on the right can always be decomposed.
    intro h14
    -- Conjunctions on the left can always be decomposed.
    let h15 := h11.left
    let h16 := h11.right
    -- False on the left can always be used.
    apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60180183718809460647310846216 : (((p5 ∨ p1) → ((p4 ∨ p5) ∨ (((False ∨ p4) ∨ (False ∨ (p3 ∨ True))) → (((p3 ∧ p2) ∨ p1) ∨ ((True → p3) ∨ (p2 → True)))))) ∨ p3) := by
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
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- False on the left can always be used.
        apply False.elim h6
      case inr h7 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h3
    case inr h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- False on the left can always be used.
        apply False.elim h9
      case inr h10 =>
        -- Disjunctions on the left can always be decomposed.
        cases h10
        case inl h11 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h3
        case inr h12 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_734185449774725622106578891543 : ((((False ∨ True) ∧ (((((p4 → ((p4 ∨ p2) → ((p1 ∧ (p2 ∧ p2)) ∨ False))) → p1) ∨ p1) ∧ True) ∨ (((False → p1) → False) → p2))) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (False → p1) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- False on the left can always be used.
  apply False.elim h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_175110906337831981861986054049 : ((p4 ∧ (((p4 → (p3 ∨ (p1 → p5))) ∨ p1) ∨ (p4 → (False ∧ (p3 ∨ p3))))) → (((p5 → p1) → p2) ∨ (p3 → ((p1 → p4) → True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- Implications on the right can always be decomposed.
      intro h7
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h9
      -- Implications on the right can always be decomposed.
      intro h10
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h11 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h12
    -- Implications on the right can always be decomposed.
    intro h13
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_183847735546690281086777013058 : ((((p5 ∧ (p4 ∧ ((p4 ∧ True) ∧ p5))) ∨ (p5 → p3)) ∧ p4) ∨ (p5 → ((((((p1 ∧ p1) → (True → p4)) ∨ True) ∨ False) ∧ True) ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_323941981365688707197494738796 : (p5 ∨ ((p4 ∧ (p1 ∨ ((False → (False ∨ p1)) → (((p4 → True) → (p5 → False)) ∨ p2)))) → (p5 ∨ (((p3 ∨ p2) → (p4 ∧ p5)) ∨ p4)))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184028087933629700353943550582 : (((((((False ∨ (True ∨ p1)) → p2) → p2) → p5) → p1) ∨ False) ∨ ((p4 → (((p5 ∨ p3) → True) ∧ (((p3 ∨ True) ∨ True) → p4))) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h6 =>
      -- One of the premise coincides with the conclusion.
      exact h1
  case inr h7 =>
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317672461031420033302641374210 : (p4 ∨ ((((False → (p2 ∧ (p1 ∨ ((True ∨ p2) → p5)))) ∧ ((p3 → ((p1 ∧ p4) ∧ ((p2 ∨ (p4 ∧ p5)) ∨ False))) ∧ True)) → p3) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_698221324082391479634762715630 : ((((((p3 → p2) ∨ ((p2 → (p3 ∨ (True → p4))) ∧ p5)) → False) ∨ (((p2 → ((p1 → p1) ∨ p5)) ∨ p2) ∨ ((p2 → False) → False))) ∨ p4) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_684056306178499741012188269481 : (((((p1 ∨ (((p2 ∧ (p5 ∨ p5)) → p2) ∨ (((True ∨ (p4 ∨ p2)) ∧ p4) ∧ False))) → p4) ∨ (p3 ∨ (True → (True ∧ (False ∨ True))))) ∨ p2) ∧ True) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319068258467730976267360360240 : (p4 ∨ ((p3 → (p4 ∨ (True → (p1 ∧ ((p2 → p4) → (p5 ∧ (p2 → ((p3 ∨ (p4 ∧ p1)) ∨ p3)))))))) ∨ (p1 → ((p5 ∨ True) ∨ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_666708416523287136103244742624 : ((((((((p1 → p3) → (p2 → p1)) → True) → (p5 → p1)) ∨ (True ∧ (p1 ∧ (p1 ∧ ((True ∧ p4) ∨ True))))) ∧ (p3 ∧ (p3 ∧ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_786860996504165233536628206597 : (((p4 ∨ ((p4 → (p1 ∧ p1)) ∧ ((p1 ∧ p5) ∧ (True ∧ ((((True ∧ True) → False) ∧ (False ∨ ((p2 ∨ p3) ∧ (False ∨ True)))) ∨ p2))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148714892426187704777069386417 : ((((p2 ∧ (p1 → p3)) → (p3 → (p3 ∧ False))) → (p3 ∧ ((False ∨ p3) → (p5 ∨ (p5 ∧ (p4 ∨ p1)))))) ∨ (p5 ∨ (p2 ∨ (False → p2)))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50347589868384031508109823768 : ((((((p3 → p4) ∨ p2) ∧ p3) ∧ ((p2 ∧ (False ∨ ((p3 → p2) → (False ∧ p3)))) ∨ (p3 → p2))) ∨ (p4 → (p4 ∨ (p1 ∨ p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112981800998079903516637470257 : (((p2 ∧ (((p5 ∧ (p2 ∧ ((((p2 → p3) ∧ False) ∧ (p1 ∨ p5)) → p4))) ∨ p4) ∧ ((p1 ∧ (p5 ∨ p5)) ∨ True))) → p3) ∨ (True ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_141849651185631003593997530559 : (((p3 ∨ p1) ∨ (((p5 ∨ False) ∨ p3) ∧ (((p3 ∨ False) → ((False ∧ (p4 ∧ True)) → p4)) ∨ (p3 ∨ (p4 ∨ p1))))) → ((p1 ∨ True) ∨ p4)) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h4 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h4
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Disjunctions on the left can always be decomposed.
        cases h7
        case inl h10 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h11 =>
          -- Disjunctions on the left can always be decomposed.
          cases h11
          case inl h12 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h13 =>
            -- Disjunctions on the left can always be decomposed.
            cases h13
            case inl h14 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- One of the premise coincides with the conclusion.
              exact h14
            case inr h15 =>
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- One of the premise coincides with the conclusion.
              exact h15
      case inr h16 =>
        -- False on the left can always be used.
        apply False.elim h16
    case inr h17 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h18 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h19 =>
        -- Disjunctions on the left can always be decomposed.
        cases h19
        case inl h20 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h21 =>
          -- Disjunctions on the left can always be decomposed.
          cases h21
          case inl h22 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h22
          case inr h23 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h23



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178083434413552123433469125979 : (((((p2 ∨ ((p4 ∨ (True ∨ p2)) ∨ False)) ∧ (False ∧ p4)) → p3) → p1) ∨ (((((p2 ∨ (p2 → False)) ∨ True) → p3) → p1) ∨ (False → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354070338241148831172814766515 : (p4 → (p4 → (p4 → ((((p3 ∨ ((p3 ∨ (p1 ∨ p2)) ∧ (((p3 → p3) → True) → p2))) → (p4 ∧ (p3 ∧ p2))) → (p5 ∧ True)) ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_639713811653179136963096022890 : (((((True → (p1 → p2)) ∧ ((p1 ∧ ((p3 → (p4 ∨ p1)) ∧ p4)) ∨ (p3 ∨ ((p4 ∨ ((p3 ∧ True) ∧ p4)) ∧ (p1 ∧ p4))))) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_139685745733496854984992177201 : (((((False ∨ p5) → True) → (False ∨ (((p3 ∨ True) → p1) ∨ (p2 → (((p3 ∨ p3) ∧ p2) → (p2 → False)))))) → p1) → ((p1 ∧ True) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136307513702225095536184033246 : ((((p3 ∨ (p3 → p5)) ∧ p5) ∧ ((p3 ∨ True) ∧ ((p3 ∨ (p2 ∧ ((p2 → ((p4 ∨ p3) ∧ p1)) → True))) ∨ p3))) ∨ ((False → p2) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246562605132587935582422270409 : ((p5 ∧ p2) ∨ ((((True → False) → (p3 → (((p5 ∨ (((False → False) ∨ p1) ∧ True)) ∧ p2) ∧ ((True ∧ False) → (p2 → False))))) → False) → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((True → False) → (p3 → (((p5 ∨ (((False → False) ∨ p1) ∧ True)) ∧ p2) ∧ ((True ∧ False) → (p2 → False))))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h5 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h6 := h3 h5
    -- False on the left can always be used.
    apply False.elim h6
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h7 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h8 := h3 h7
    -- False on the left can always be used.
    apply False.elim h8
    -- Implications on the right can always be decomposed.
    intro h9
    -- Implications on the right can always be decomposed.
    intro h10
    -- Conjunctions on the left can always be decomposed.
    let h11 := h9.left
    let h12 := h9.right
    -- False on the left can always be used.
    apply False.elim h12
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h13 := h1 h2
  -- False on the left can always be used.
  apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205891106641185986810739484738 : ((True ∧ ((p3 ∨ p2) ∨ (p1 ∧ p4))) ∨ (p4 → (((False ∨ (((((p1 ∧ (p5 ∨ p4)) → p2) ∨ p4) → (p4 → p1)) ∧ True)) ∨ True) ∧ True))) := by
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
theorem thm_5_vars_166269482714340228427424911884 : ((p3 ∧ (p5 ∧ (p4 ∧ ((p3 ∨ (((p3 → ((p5 → p5) ∨ p5)) ∧ p4) → p1)) ∧ True)))) ∨ (((p5 → (p1 → p1)) ∨ (False ∧ p2)) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



