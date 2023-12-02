variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147518668733824285212824055141 : (((p4 ∨ (p1 ∨ (False ∨ ((p4 ∨ (((p4 ∨ p1) ∨ ((p2 ∨ p2) ∧ (p4 ∧ p5))) ∨ p1)) ∧ p1)))) ∨ p5) ∨ (p4 → ((False ∧ False) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336402572236846113714557377139 : (p1 → ((p4 ∧ ((((True ∨ ((p4 ∨ (True ∧ p5)) ∧ False)) ∧ (True → True)) → ((False ∧ ((p4 ∨ p1) ∨ p2)) ∨ p4)) → (p5 → p2))) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1523733692569531577512598946 : (((p2 ∨ ((p4 ∧ False) ∧ False)) ∨ (p1 ∧ ((((p5 ∧ (True ∧ p3)) ∨ p3) ∧ p5) ∨ (((p1 ∨ p3) → p4) → p5)))) ∨ (False → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111996119146081630352634065199 : ((((p2 → ((p5 → p4) ∧ p1)) ∧ (((p3 ∨ False) ∨ False) → ((p3 ∨ (False → (False ∨ ((p4 ∨ p4) → p5)))) → False))) ∨ True) ∨ (p3 ∧ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319630084307845838593410358852 : (p4 ∨ ((((p3 → ((True ∨ p1) → p3)) ∧ False) ∨ False) ∨ ((p2 → p1) → (((p2 ∧ (p2 → (p1 ∨ p2))) ∨ p2) ∨ (p4 → (p2 ∨ p4)))))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114375524597003237051599625108 : (((((False ∨ (((True ∧ p3) ∧ p1) → (((p5 ∧ True) → True) → (p3 → False)))) ∨ p3) → False) ∨ ((p2 → (p4 ∧ p5)) ∨ True)) ∨ (True ∧ p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159484575079483669833897243553 : ((((True ∨ ((p2 ∨ p3) ∧ p1)) ∨ (((p2 ∧ p1) ∨ ((p2 → (False ∨ False)) ∧ p3)) → p5)) ∧ p3) → ((p4 ∨ (p4 ∨ (False ∨ p5))) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h3
      case inr h10 =>
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
theorem thm_5_vars_231449711454285303147493531778 : (((p2 → p3) ∨ False) → ((((((p2 ∧ p4) ∨ p3) → p3) ∨ False) → p1) ∨ (True → (((p2 → p1) ∧ False) ∨ (True ∨ ((False ∨ p5) ∧ p4)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- False on the left can always be used.
    apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_330764527951754380320668175635 : (True → (p1 → (False ∨ ((p1 → False) ∨ ((p5 ∨ ((True → ((((p4 → (p1 ∨ False)) ∨ (p5 → p3)) ∧ True) ∨ p3)) → p4)) ∨ (p1 ∨ p3)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338345632413146019793208165009 : (p1 → (((p2 ∧ (p5 ∧ p2)) ∧ p3) ∨ ((p4 ∨ (((p4 ∧ (p1 ∨ p3)) ∨ (p2 → False)) → (p2 ∧ p2))) ∨ (p1 ∨ ((p5 → p5) → p4))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248352119844049524473954852593 : ((p2 ∨ p3) ∨ ((p3 ∧ True) ∨ (p4 → ((p4 → (((p1 → ((p4 ∧ (p1 ∨ p2)) → (p1 ∧ p1))) ∨ (p5 ∨ p4)) → (False ∧ p4))) ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_635348871514271464043184304299 : ((((((p1 → (p5 → ((((False → p1) → p5) ∨ True) → (p4 ∨ (p5 ∧ False))))) → (p5 → False)) ∧ (True ∧ ((True ∨ p2) ∨ p1))) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115004915120408480639201191579 : ((((p5 ∨ (True ∨ True)) ∧ (((p1 ∨ p2) ∨ (True ∨ p2)) ∨ p2)) ∧ (p4 → (p3 ∨ (p2 ∨ (p4 ∨ (p2 ∨ (p2 ∨ p4))))))) ∨ (p3 ∧ p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_902515367750652888011099545407 : (((((True → (False ∧ ((p4 ∧ (True ∧ p5)) ∧ False))) ∧ (((False ∨ False) → p3) ∨ ((True ∨ True) → True))) ∧ ((p4 → True) ∧ (p5 ∨ True))) → False) ∧ True) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h7 := h3.left
    let h8 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h10 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h11 := h4 h10
      -- We need to get the left conjuct of h11 based on <expert-advice>.
      let h12 := h11.left
      -- False on the left can always be used.
      apply False.elim h12
    case inr h13 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h14 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h15 := h4 h14
      -- We need to get the left conjuct of h15 based on <expert-advice>.
      let h16 := h15.left
      -- False on the left can always be used.
      apply False.elim h16
  case inr h17 =>
    -- Conjunctions on the left can always be decomposed.
    let h18 := h3.left
    let h19 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h19
    case inl h20 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h21 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h22 := h4 h21
      -- We need to get the left conjuct of h22 based on <expert-advice>.
      let h23 := h22.left
      -- False on the left can always be used.
      apply False.elim h23
    case inr h24 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h25 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h26 := h4 h25
      -- We need to get the left conjuct of h26 based on <expert-advice>.
      let h27 := h26.left
      -- False on the left can always be used.
      apply False.elim h27
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137138222462380306381499807109 : ((True ∧ (p3 ∨ (((((((p3 ∧ p2) → False) ∨ p3) ∧ p4) ∨ (p3 → False)) → (False ∨ (p2 ∧ (p1 ∨ p5)))) ∨ False))) ∨ ((True → p2) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_650389769664983943431186702359 : ((((((p4 → True) ∧ ((p2 ∨ (p5 ∧ (p4 ∨ p1))) ∧ (p4 ∨ (p5 ∧ p3)))) ∨ (((p4 → p2) → (True ∨ p5)) → True)) ∧ (True ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204364514114054321329842285984 : (((p2 ∨ (False ∨ (p3 → p2))) ∧ p5) ∨ (p4 ∨ (False → (((p3 ∧ p3) → p2) ∧ ((((p5 → p4) ∨ p3) ∧ p3) → (p2 → (p4 ∧ True))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- False on the left can always be used.
  apply False.elim h1
  -- Implications on the right can always be decomposed.
  intro h5
  -- Implications on the right can always be decomposed.
  intro h6
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h9 =>
    -- False on the left can always be used.
    apply False.elim h1
  case inr h10 =>
    -- False on the left can always be used.
    apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263235036448905482589600316812 : (True ∧ ((((p2 ∨ ((p5 → ((p3 ∨ (p2 → p2)) ∨ (p4 ∧ p4))) → p4)) → p5) ∧ (p4 → ((False → (p2 ∨ False)) ∨ p5))) → (p2 → p5))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h5 : (p2 ∨ ((p5 → ((p3 ∨ (p2 → p2)) ∨ (p4 ∧ p4))) → p4)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h5
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113277675576317824743893635133 : (((((p1 ∨ p4) → (((p5 ∧ True) ∧ True) → (((p5 ∨ False) → False) ∧ p5))) → (p3 ∧ (p4 ∨ (False → p2)))) ∧ (p4 ∨ False)) ∨ (True ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45480068212070898652240084636 : (((False ∨ (((((p3 ∨ (((False ∧ p4) → p2) ∧ p1)) ∧ p4) ∨ False) ∧ p4) ∨ ((True ∨ False) ∧ ((True ∧ p4) → (p3 → p3))))) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345524056634351887694517137147 : (p3 → (((p4 → ((p2 ∨ (((p1 ∧ (p3 ∧ p4)) ∨ p1) → False)) ∧ False)) → (((p4 → ((p2 ∧ True) ∧ p2)) ∧ (p3 ∧ p5)) ∨ True)) ∨ p5)) := by
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
theorem thm_5_vars_113302627596329566038237049316 : ((((((False ∧ p4) ∧ (p5 ∧ p2)) → True) → (((p2 → ((p3 ∧ (False → False)) ∨ (True ∧ p4))) ∨ p1) ∧ p2)) ∧ (p3 → p1)) ∨ (p4 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152248522200482231092247306782 : (((((True ∨ p2) → False) ∨ (p3 ∧ True)) ∨ (((p3 → ((((p1 ∨ p3) → p5) → p3) ∨ True)) → p1) ∨ True)) → ((p2 ∨ p5) ∨ (p1 ∨ True))) := by
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
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h4 =>
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225205629900074868020608433717 : (((p4 ∧ p5) ∧ p4) ∨ ((p3 ∧ ((p3 ∨ (p1 → p2)) ∧ ((p5 ∨ p5) → p1))) → (False ∨ ((((False ∨ p4) ∧ False) ∧ (p1 ∧ p1)) → p5)))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h10 := h8.left
    let h11 := h8.right
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h12 =>
      -- False on the left can always be used.
      apply False.elim h12
    case inr h13 =>
      -- False on the left can always be used.
      apply False.elim h11
  case inr h14 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h15
    -- Conjunctions on the left can always be decomposed.
    let h16 := h15.left
    let h17 := h15.right
    -- Conjunctions on the left can always be decomposed.
    let h18 := h16.left
    let h19 := h16.right
    -- Disjunctions on the left can always be decomposed.
    cases h18
    case inl h20 =>
      -- False on the left can always be used.
      apply False.elim h20
    case inr h21 =>
      -- False on the left can always be used.
      apply False.elim h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60903046672968791442280827094 : ((True ∧ (p5 → ((p4 ∧ (p3 → p5)) → (((True ∨ p1) ∨ p5) → (True → ((p3 → False) → (p3 → ((p4 ∨ (True ∨ p3)) → p1)))))))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- Implications on the right can always be decomposed.
  intro h6
  -- Implications on the right can always be decomposed.
  intro h7
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Conjunctions on the left can always be decomposed.
        let h11 := h2.left
        let h12 := h2.right
        -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
        have h13 : p3 := by
          -- One of the premise coincides with the conclusion.
          exact h6
        -- We have shown the premise of h5, we can now drive its conclusion.
        let h14 := h5 h13
        -- False on the left can always be used.
        apply False.elim h14
      case inr h15 =>
        -- Conjunctions on the left can always be decomposed.
        let h16 := h2.left
        let h17 := h2.right
        -- One of the premise coincides with the conclusion.
        exact h15
    case inr h18 =>
      -- Conjunctions on the left can always be decomposed.
      let h19 := h2.left
      let h20 := h2.right
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h21 : p3 := by
        -- One of the premise coincides with the conclusion.
        exact h6
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h22 := h5 h21
      -- False on the left can always be used.
      apply False.elim h22
  case inr h23 =>
    -- Disjunctions on the left can always be decomposed.
    cases h23
    case inl h24 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h25 =>
        -- Disjunctions on the left can always be decomposed.
        cases h25
        case inl h26 =>
          -- Conjunctions on the left can always be decomposed.
          let h27 := h2.left
          let h28 := h2.right
          -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
          have h29 : p3 := by
            -- One of the premise coincides with the conclusion.
            exact h6
          -- We have shown the premise of h5, we can now drive its conclusion.
          let h30 := h5 h29
          -- False on the left can always be used.
          apply False.elim h30
        case inr h31 =>
          -- Conjunctions on the left can always be decomposed.
          let h32 := h2.left
          let h33 := h2.right
          -- One of the premise coincides with the conclusion.
          exact h31
      case inr h34 =>
        -- Conjunctions on the left can always be decomposed.
        let h35 := h2.left
        let h36 := h2.right
        -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
        have h37 : p3 := by
          -- One of the premise coincides with the conclusion.
          exact h6
        -- We have shown the premise of h5, we can now drive its conclusion.
        let h38 := h5 h37
        -- False on the left can always be used.
        apply False.elim h38
    case inr h39 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h40 =>
        -- Disjunctions on the left can always be decomposed.
        cases h40
        case inl h41 =>
          -- Conjunctions on the left can always be decomposed.
          let h42 := h2.left
          let h43 := h2.right
          -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
          have h44 : p3 := by
            -- One of the premise coincides with the conclusion.
            exact h6
          -- We have shown the premise of h5, we can now drive its conclusion.
          let h45 := h5 h44
          -- False on the left can always be used.
          apply False.elim h45
        case inr h46 =>
          -- Conjunctions on the left can always be decomposed.
          let h47 := h2.left
          let h48 := h2.right
          -- One of the premise coincides with the conclusion.
          exact h46
      case inr h49 =>
        -- Conjunctions on the left can always be decomposed.
        let h50 := h2.left
        let h51 := h2.right
        -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
        have h52 : p3 := by
          -- One of the premise coincides with the conclusion.
          exact h6
        -- We have shown the premise of h5, we can now drive its conclusion.
        let h53 := h5 h52
        -- False on the left can always be used.
        apply False.elim h53



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197921251275961467725346233727 : (((p5 ∨ (p4 ∨ p3)) → (p5 ∧ (p5 ∨ p3))) ∨ ((((True → p2) ∨ True) → p3) → (((True ∨ p2) ∧ p3) ∨ (p5 ∧ (p2 ∧ (p2 ∧ p4)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((True → p2) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157156301529945487758388604043 : (((((p5 → p1) ∧ ((p1 → p5) ∨ (((p3 → (False ∨ False)) ∨ (p1 → False)) ∧ True))) ∨ p3) → p4) ∨ ((((p2 ∨ p3) → p4) → p3) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_141250929387613731344808712458 : (((True ∨ ((p5 ∨ (p3 ∨ p5)) ∧ p2)) → (((p2 ∨ True) ∧ (p4 ∧ False)) ∧ ((p3 ∧ p2) ∧ ((p2 → p3) ∨ p1)))) → ((p3 ∧ p3) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (True ∨ ((p5 ∨ (p3 ∨ p5)) ∧ p2)) := by
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
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- False on the left can always be used.
  apply False.elim h6
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h7 : (True ∨ ((p5 ∨ (p3 ∨ p5)) ∧ p2)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h8 := h1 h7
  -- We need to get the left conjuct of h8 based on <expert-advice>.
  let h9 := h8.left
  -- We need to get the right conjuct of h9 based on <expert-advice>.
  let h10 := h9.right
  -- We need to get the right conjuct of h10 based on <expert-advice>.
  let h11 := h10.right
  -- False on the left can always be used.
  apply False.elim h11
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214636449302584400770302211744 : (((p1 → p1) ∧ (False ∨ p2)) ∨ ((((((p1 ∨ p4) ∧ False) ∧ (p2 ∨ (False → False))) ∨ p4) ∨ (False → (p5 ∨ p3))) ∨ ((p4 ∨ p3) → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257561238805134229190528698549 : ((p3 ∨ p1) → (((p1 ∨ ((p2 ∧ (True ∨ True)) → ((p2 ∧ p3) → False))) → ((p4 ∨ p3) ∧ (((p3 → True) ∧ True) ∧ p5))) ∨ (p4 ∨ True))) := by
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
theorem thm_5_vars_246461127423465570829619030229 : ((p5 ∧ False) ∨ (((True ∨ (p4 ∧ (p3 ∨ (p5 → p4)))) ∨ False) → ((False ∨ (p1 → (p4 → (True ∨ (p4 ∧ p4))))) ∨ (False ∨ (False ∨ p2))))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h4
      -- Implications on the right can always be decomposed.
      intro h5
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h10
        -- Implications on the right can always be decomposed.
        intro h11
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h12 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h13
        -- Implications on the right can always be decomposed.
        intro h14
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h15 =>
    -- False on the left can always be used.
    apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354777061439010358041002323762 : (p5 → (((((p2 ∧ p3) ∨ ((True ∨ (True → True)) → p5)) → False) → (False ∨ (((p5 ∨ p3) ∨ ((True → (p1 ∨ p1)) ∧ False)) → False))) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : ((p2 ∧ p3) ∨ ((True ∨ (True → True)) → p5)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h6 =>
      -- One of the premise coincides with the conclusion.
      exact h1
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h7 := h2 h3
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137648920192154139364734054917 : ((False ∨ (((p1 ∧ False) ∧ p2) ∧ (((p2 → (p5 ∨ p4)) → (((False ∧ (p4 ∧ p4)) ∨ False) → p4)) ∨ (True → p2)))) ∨ (p3 ∨ (True ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53210575769387626204390934914 : ((((p5 ∧ (((p3 ∧ p5) ∨ p1) ∧ p4)) ∧ (p5 ∨ (p3 → False))) ∨ ((p2 ∨ (p4 ∧ (False → ((p3 ∧ p4) → p2)))) ∨ (p2 ∨ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_710665144950399601025539466928 : ((((((p3 → p5) → True) ∨ (True ∧ False)) ∧ (((p1 ∨ p3) ∧ ((True ∧ p1) ∧ (p1 ∧ p3))) ∨ (False → ((p4 → p2) ∧ (p2 ∧ p2))))) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h2
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260925393703588003732709797037 : ((p4 → False) → ((p4 ∨ p5) → (((((True ∨ p3) ∨ p5) ∨ (((((p3 ∧ p5) → p2) ∨ True) ∧ ((p2 ∨ p5) → p3)) ∨ p2)) ∧ p1) ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h4 : p4 := by
      -- One of the premise coincides with the conclusion.
      exact h3
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h5 := h1 h4
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_485710294311052336458100882168 : ((((((p3 ∧ p2) ∧ (p5 → p3)) → p4) ∨ (((((p4 → (p3 ∨ p3)) → (p3 ∧ (p5 ∨ ((p5 ∨ False) ∨ False)))) ∨ p5) ∨ True) ∧ True)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_756731874489587566502753950549 : (((p1 ∧ (((p2 → (True → (p1 → p4))) → ((False → (p4 ∧ p5)) → False)) ∨ (((True ∨ (True → p3)) → (p5 ∧ p5)) ∨ (True ∨ p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148688064295455117089391887503 : ((((p5 → True) → (((p1 → p2) ∨ p5) ∧ True)) ∨ (((p4 ∨ p5) → (p4 ∨ False)) → (p5 → (p1 ∨ True)))) ∨ (p4 ∧ ((False → p1) → False))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_606569407471753912933025920347 : ((((((((p4 ∧ False) ∨ (((p5 ∧ False) ∧ p5) ∧ p4)) → ((((p4 → (p2 ∧ p3)) ∨ (p3 → p2)) ∧ False) ∨ p5)) → p4) ∧ p4) ∨ True) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_40596888889054867342731586132 : (((((p1 → (((False → (((p5 → (False ∨ p1)) ∨ p2) ∨ p5)) ∧ False) ∨ (p3 ∧ (p3 → ((p5 → p3) ∨ p2))))) ∧ p3) → p1) ∨ True) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156744655681136816261922273251 : ((((p5 ∧ (p4 ∨ p2)) ∧ (p3 ∧ (((False ∨ p3) ∧ (p4 → (False ∨ (False ∧ True)))) ∨ False))) ∧ p1) ∨ (False → ((p4 → (p5 ∧ p5)) ∧ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_555405280466482907082312974325 : (((p2 ∨ (p2 → (p5 ∨ ((p3 ∨ (((p5 ∨ ((p1 ∨ ((True ∧ p4) → True)) ∨ (True ∨ (p2 ∧ p4)))) ∧ p1) ∧ p1)) ∨ (p2 ∨ p3))))) ∧ True) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_642554198637594491843304871406 : ((((p1 ∧ (((p5 → ((p3 ∨ (p1 → p1)) ∨ (p4 ∧ p5))) → ((p5 ∨ True) ∨ (p3 → ((p2 ∧ (p1 ∧ p1)) ∨ p3)))) ∧ True)) → p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_668411010369509948604918255373 : ((((((((p5 ∧ (False ∧ p2)) → ((((p2 ∨ True) ∧ True) ∧ ((p1 ∨ p3) → p2)) → p4)) → p4) ∨ p3) ∧ p3) ∨ (p5 → (p5 ∧ p5))) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136899745938000769445205528752 : (((p4 ∨ p5) ∨ (((False → True) → ((p2 ∧ (p4 → p4)) ∨ (p1 ∧ p5))) ∨ (False → (p3 ∧ (False ∧ (p3 ∧ p2)))))) ∨ (False ∧ (p2 ∧ False))) := by
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
  -- False on the left can always be used.
  apply False.elim h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148745062776994108865601377644 : (((((p5 ∨ p2) → p2) → (True → p5)) ∧ (p1 ∧ (p5 ∨ (p4 ∨ ((((p5 → p1) ∨ True) → False) ∧ p4))))) ∨ (p3 ∨ ((False ∧ False) → False))) := by
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
theorem thm_5_vars_252076004891747883529847030923 : ((p4 → p1) ∨ (p5 → ((p5 → ((p1 → p2) → p3)) ∨ (((((p5 ∧ (False → p3)) ∧ ((p2 ∨ p3) → p1)) → p2) ∨ p4) ∨ (False → True))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156950500309956437496126606738 : ((((False → (((p5 → True) → ((p1 ∨ ((p1 → p4) → p3)) → p2)) ∨ p4)) → (p3 ∧ p4)) ∨ p5) ∨ (((p5 → (p5 ∨ p5)) ∧ p3) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135746131167520946537998863401 : (((((p5 → (p2 ∨ p4)) ∨ True) → (p3 → (p2 ∧ ((False ∨ p1) ∧ p5)))) ∨ (p2 ∨ (((p4 ∨ False) ∨ True) ∧ p5))) ∨ (True ∨ (p4 ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_753976098670267694161444572481 : (((False ∧ (((p1 → ((p5 ∨ p5) ∧ p5)) → False) → ((p4 ∧ ((p4 ∨ (p1 ∧ ((False ∧ p1) ∧ p4))) → p5)) ∧ (p1 → (True ∧ True))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_124823129635813858600408492169 : (((((p5 ∨ p1) ∧ True) → True) ∨ ((((False → (False ∧ p2)) ∨ p2) ∨ ((p4 ∧ p5) ∧ (True ∧ p4))) → ((p2 → p1) ∨ p2))) → (p2 ∨ True)) := by
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
theorem thm_5_vars_64921473519892983431399117107 : ((p2 ∨ (((((p5 → (p4 ∧ (True ∧ ((p2 ∨ True) ∧ (p1 → p4))))) ∨ p1) ∧ p2) ∧ p3) → (p4 ∧ (((p4 ∧ p1) ∨ p4) ∧ p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_302983909523688835035633386396 : (False ∨ (p1 → ((((p1 ∧ ((p1 ∧ True) → (p1 ∧ p5))) ∧ p1) ∧ ((p2 → p4) ∧ ((p2 ∨ p5) ∨ (p2 ∧ (p5 → (False ∨ p4)))))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215427502110746882480968120130 : ((p3 ∧ ((p1 ∧ p2) ∨ p1)) ∨ ((p4 ∨ True) ∨ ((p5 → (((p5 ∨ (p4 ∨ p1)) → (p3 → (p3 ∨ (True ∨ False)))) → (p3 ∧ p5))) ∧ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_547933826600783757108537651004 : (((False ∨ ((((((((p3 ∧ False) → p3) ∧ (p1 ∨ p1)) ∧ True) ∨ p5) → (p3 ∨ p1)) ∧ p2) → ((True ∧ (p2 → False)) → (p5 ∧ p5)))) ∧ True) ∧ True) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h1.left
  let h6 := h1.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h7 : p2 := by
    -- One of the premise coincides with the conclusion.
    exact h6
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h8 := h4 h7
  -- False on the left can always be used.
  apply False.elim h8
  -- Conjunctions on the left can always be decomposed.
  let h9 := h2.left
  let h10 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h11 := h1.left
  let h12 := h1.right
  -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
  have h13 : p2 := by
    -- One of the premise coincides with the conclusion.
    exact h12
  -- We have shown the premise of h10, we can now drive its conclusion.
  let h14 := h10 h13
  -- False on the left can always be used.
  apply False.elim h14
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60900287974698989097700592264 : ((True ∧ (p5 → ((((p1 → p1) → ((False → p1) → p2)) → (((((p1 ∧ p3) ∨ p4) → False) ∨ (p2 ∨ False)) → (p4 ∧ p4))) ∨ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314717237380391638520683617562 : (p3 ∨ (((True → ((p5 → (True ∨ p4)) → False)) ∨ (False → (p1 ∨ (p5 → p2)))) ∧ (((False → p3) → True) ∨ (((p2 ∨ p4) ∧ p3) ∨ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46289345047768192991053194916 : ((((((False ∨ (p4 ∨ False)) ∧ p5) ∨ (((p4 ∧ True) ∨ (((True ∧ p3) ∨ p3) ∨ p5)) ∧ p3)) ∨ (p3 ∨ (False ∨ True))) ∧ (True ∨ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309604844150430963882233944094 : (p2 ∨ ((((((p2 ∧ ((p2 ∨ True) ∧ (p2 ∨ (p5 → p5)))) ∨ ((p3 ∧ False) ∨ p4)) → (p5 ∧ False)) ∨ p2) ∨ p4) ∨ (p4 ∨ (p4 → True)))) := by
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
theorem thm_5_vars_42146076474282781068036767907 : ((((True → False) → (False ∨ ((p3 ∧ (((p4 ∧ (p3 → p1)) ∨ (((False ∨ p1) ∨ True) ∧ p3)) ∧ p2)) ∧ (True → (p5 ∧ True))))) ∨ p4) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_571954957679112012111540415590 : (((p1 → ((True → (((p1 ∧ p5) ∨ (p4 ∨ False)) → (p2 ∧ p4))) → ((p2 ∧ (p2 ∧ p5)) ∨ (((True → (p1 ∧ p1)) ∨ p3) ∨ p2)))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134188605124182953644300379145 : ((((((True → (False ∨ ((p4 ∨ p2) ∨ p4))) ∨ (True → p1)) → p3) → (True ∧ ((p3 ∨ (False ∨ True)) ∨ False))) ∨ p3) ∨ (p1 ∨ (True ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_170327755646388028966882921908 : (((((p3 ∨ False) → p3) ∧ p1) → (((True → False) ∨ False) → ((p4 ∧ False) ∧ p3))) ∧ (((p3 ∨ (((True ∨ True) → True) → p2)) ∨ True) ∨ p3)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h1.left
    let h5 := h1.right
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h6 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h7 := h3 h6
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- False on the left can always be used.
    apply False.elim h8
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h1.left
    let h11 := h1.right
    -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
    have h12 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h9, we can now drive its conclusion.
    let h13 := h9 h12
    -- False on the left can always be used.
    apply False.elim h13
  case inr h14 =>
    -- False on the left can always be used.
    apply False.elim h14
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h15 =>
    -- Conjunctions on the left can always be decomposed.
    let h16 := h1.left
    let h17 := h1.right
    -- We want to use the implication h15 based on <expert-advice>. So we show its premise.
    have h18 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h15, we can now drive its conclusion.
    let h19 := h15 h18
    -- False on the left can always be used.
    apply False.elim h19
  case inr h20 =>
    -- False on the left can always be used.
    apply False.elim h20
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64682249975066510067151248839 : ((p1 ∨ (p4 ∨ (((p1 ∨ ((p2 → (((p1 → p2) ∧ p3) → p2)) → p5)) ∧ (p1 → (p1 ∨ ((p5 ∧ p1) ∧ False)))) ∨ (p3 → p3)))) ∨ p5) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218225478891791853318422512216 : (((p4 ∧ p5) ∨ (p4 → False)) → (((p1 ∨ ((p3 → p4) ∧ p3)) ∧ p4) ∨ (p4 ∨ (((p2 ∨ p3) → p2) → ((p1 → (p5 ∨ p1)) ∨ p2))))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h7
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_250710947958868902463156188453 : ((p1 → False) ∨ ((((p5 ∨ (p3 → (p2 → p5))) ∨ p2) → (p1 ∨ p4)) → ((((True ∧ p1) → p4) ∨ (True ∨ (p4 → (False ∨ p4)))) ∨ False))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_142332196999784457865408896729 : ((p3 ∧ (((((p3 ∧ (False ∨ (p4 ∧ p4))) → (p5 → p1)) → (False ∧ p2)) ∨ True) ∧ ((p4 → (False → p1)) ∨ True))) → ((p4 ∨ p1) ∨ True)) := by
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
    cases h5
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215502768384316718547812689252 : ((p4 ∧ ((p4 → p5) ∨ False)) ∨ (p4 ∨ ((p2 ∧ ((((((p3 ∨ p1) ∧ p5) ∧ (p2 ∨ p4)) → (p4 → (True → False))) → p1) ∧ False)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115376376768853932885667481233 : (((((True → (False ∧ True)) ∧ p4) → (p1 ∨ p4)) ∧ ((p4 ∧ p3) ∧ (p4 → ((((True ∧ p1) ∨ (p3 ∧ True)) → p5) ∨ p3)))) ∨ (p1 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164881408240247539361960113450 : (((p1 → (p1 ∧ ((p3 → (False ∧ ((p4 → p1) ∨ (p2 → p5)))) → (p5 → p4)))) ∨ True) ∨ ((p4 ∨ (p1 → False)) ∧ ((True ∧ p5) ∨ p5))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47146981089741273238153743057 : ((((((p4 ∧ (p1 ∧ ((p3 ∧ p3) ∨ p1))) ∧ p4) ∧ (((p2 ∨ p3) → True) ∨ True)) ∨ (False → ((p2 → True) ∧ p2))) ∨ (p4 → p1)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_176773876005914806040288130338 : (((p5 ∨ (False ∨ False)) ∨ (((False ∨ (False ∧ False)) ∧ p1) → (p4 ∧ p5))) ∧ ((False ∨ True) ∧ ((p2 ∨ p3) ∨ ((p1 ∧ True) ∨ (False → p3))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  cases h2
  case inl h4 =>
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- False on the left can always be used.
    apply False.elim h6
  -- Conjunctions on the left can always be decomposed.
  let h8 := h1.left
  let h9 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h10 =>
    -- False on the left can always be used.
    apply False.elim h10
  case inr h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- False on the left can always be used.
    apply False.elim h12
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h14
  -- False on the left can always be used.
  apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46877052262466394713801263116 : (((((((p4 ∧ ((True ∧ p5) ∨ (p5 ∧ (((p1 → (False ∧ p2)) ∧ (p3 → p1)) ∧ True)))) ∨ p2) ∧ p1) ∧ p1) ∨ p4) ∨ (p1 ∨ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172010493758181586672264077453 : ((((True ∨ ((False ∨ p4) → ((p2 ∨ p5) → False))) → (p3 → p2)) ∨ (p4 ∧ p5)) ∨ ((True → (((p2 ∧ (p5 ∨ p1)) ∧ p3) ∧ p3)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190683909918813859616121983769 : (((p5 → (((False ∧ p3) → (p4 ∧ p1)) ∧ p5)) → p3) ∨ (p3 ∨ (((p4 → p4) → p1) ∨ (((p3 ∨ (False ∨ True)) ∨ (p1 ∨ p1)) → True)))) := by
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
theorem thm_5_vars_345586912649745097136515480890 : (p3 → (((p1 ∧ p3) ∧ ((((p5 ∧ p2) ∨ ((True → False) ∧ True)) → (((p3 ∧ (p2 → (p2 ∧ (True ∨ p5)))) ∧ False) ∨ False)) → p1)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192696602012103713902668132885 : ((((((p1 ∨ True) → False) ∧ p5) → (p2 → p4)) → p4) → (((p2 ∧ ((False → ((p4 ∧ (p4 → False)) ∧ (p1 ∨ p3))) → p1)) ∨ p4) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248484347565582736053624200449 : ((p2 ∨ p5) ∨ (p1 ∨ (p3 ∨ ((p5 ∧ (True ∧ (((((p1 ∨ p2) → (False → p3)) ∧ p4) → p2) ∨ ((False ∧ p3) → False)))) → (p4 ∨ True))))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2362626572142493929342913138 : ((((((p5 ∧ True) ∨ (p5 ∨ p1)) ∨ p3) → (p3 ∨ p2)) ∨ p3) ∨ (p1 → ((p5 → (p2 → p2)) ∨ (((True → p1) → p5) → p1)))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178904717166631950404825430997 : (((p3 ∨ p5) ∧ (((p5 ∨ p2) → (p4 ∧ (False ∨ p4))) ∧ (p4 → p3))) ∨ ((((False → (p1 ∧ p4)) → p4) ∧ p3) → ((True ∨ p2) ∧ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h6 : (False → (p1 ∧ p4)) := by
    -- Implications on the right can always be decomposed.
    intro h7
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- False on the left can always be used.
    apply False.elim h7
    -- False on the left can always be used.
    apply False.elim h7
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h8 := h4 h6
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48677411166188139472171614580 : (((((p5 ∧ (((p5 ∧ p3) → False) ∨ (p2 ∨ p4))) → False) ∨ (p2 ∨ (p5 → (((p1 ∨ False) ∨ p1) → p5)))) ∧ ((p1 ∨ p5) ∨ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114384096624473339661551559320 : (((((((p4 → False) ∨ (p2 → p1)) → (p2 → True)) → ((p3 ∧ False) ∧ p4)) ∧ (p1 ∧ p3)) ∨ ((p3 ∧ p3) → (True → False))) ∨ (p2 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_641201935441093016739443531074 : (((((p3 ∨ p1) ∨ ((p5 ∧ (p5 ∨ False)) ∧ (((p3 ∧ ((p3 ∨ (p2 ∨ p2)) ∧ p1)) ∧ (p5 ∧ (p2 → False))) ∨ (p3 ∧ p4)))) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323188276422931304506627734279 : (p5 ∨ (((((p3 ∨ (p1 ∨ (p4 ∧ (p3 ∨ True)))) ∧ (((p2 ∨ (p2 ∧ p3)) ∨ ((p4 ∧ p2) → p3)) → True)) ∨ p2) → p5) ∨ (False → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118238441927215339140302272444 : ((p1 ∨ ((p1 → (((((False ∨ (False ∨ p3)) ∨ p4) → (p3 ∧ p5)) → (p2 ∨ ((True → (p1 ∧ p2)) → p5))) → p2)) → p2)) ∨ (p1 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_800492571090239705177818225705 : (((p2 → ((((p4 ∨ ((p1 ∧ ((False ∨ ((True → (p4 → (p2 ∧ p4))) ∧ (p3 ∧ (p2 ∨ p1)))) ∨ p1)) → p3)) ∨ True) ∨ p4) → p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_379718737833544524404617446497 : ((((((False ∧ ((p2 → (p5 → (False ∧ (False ∧ p2)))) ∧ ((True ∨ (((p1 → p2) ∧ (p2 → p2)) → True)) ∧ p2))) ∧ p2) ∧ p1) ∨ True) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_750718154827947374032152219948 : (((True ∧ (((p5 ∧ p2) ∨ (((p4 → ((False → (p5 ∧ p4)) ∨ p2)) ∨ p3) ∧ False)) ∨ (p2 ∨ (((True → p3) ∧ p5) ∨ (p3 → p1))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303137964523561831448616243366 : (False ∨ (p3 → ((p4 ∧ False) ∨ ((True ∧ (p2 ∨ (p3 ∧ (p1 ∧ (((p4 ∨ (p3 ∨ ((False → False) → p1))) ∨ p2) → (p2 ∧ p4)))))) → p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
    have h11 : ((p4 ∨ (p3 ∨ ((False → False) → p1))) ∨ p2) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h7
    -- We have shown the premise of h10, we can now drive its conclusion.
    let h12 := h10 h11
    -- We need to get the left conjuct of h12 based on <expert-advice>.
    let h13 := h12.left
    -- One of the premise coincides with the conclusion.
    exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_252030549021316367347551736374 : ((p4 → p1) ∨ (((p4 ∨ p4) ∧ (((True → (False ∧ (p1 → (True ∧ p5)))) ∧ (True ∨ (p2 → p2))) ∧ ((p2 ∨ p4) → (True → p4)))) → p3)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h3.left
    let h6 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
      have h10 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h7, we can now drive its conclusion.
      let h11 := h7 h10
      -- We need to get the left conjuct of h11 based on <expert-advice>.
      let h12 := h11.left
      -- False on the left can always be used.
      apply False.elim h12
    case inr h13 =>
      -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
      have h14 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h7, we can now drive its conclusion.
      let h15 := h7 h14
      -- We need to get the left conjuct of h15 based on <expert-advice>.
      let h16 := h15.left
      -- False on the left can always be used.
      apply False.elim h16
  case inr h17 =>
    -- Conjunctions on the left can always be decomposed.
    let h18 := h3.left
    let h19 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h20 := h18.left
    let h21 := h18.right
    -- Disjunctions on the left can always be decomposed.
    cases h21
    case inl h22 =>
      -- We want to use the implication h20 based on <expert-advice>. So we show its premise.
      have h23 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h20, we can now drive its conclusion.
      let h24 := h20 h23
      -- We need to get the left conjuct of h24 based on <expert-advice>.
      let h25 := h24.left
      -- False on the left can always be used.
      apply False.elim h25
    case inr h26 =>
      -- We want to use the implication h20 based on <expert-advice>. So we show its premise.
      have h27 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h20, we can now drive its conclusion.
      let h28 := h20 h27
      -- We need to get the left conjuct of h28 based on <expert-advice>.
      let h29 := h28.left
      -- False on the left can always be used.
      apply False.elim h29



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177795050176075455556840580345 : (((p1 ∨ ((True ∧ (True → True)) → ((p3 → p1) ∨ (p5 ∨ p1)))) ∧ p4) ∨ (True ∨ (((p2 ∧ False) ∧ (p4 ∨ (True ∨ (False ∧ p1)))) → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134320948576211567005676297679 : (((p1 ∧ ((p4 → ((p3 ∧ p3) ∧ p1)) ∨ (((p1 ∨ (False → (p1 → (p5 ∧ (p1 ∧ p3))))) → p4) ∨ p4))) ∨ False) ∨ (True ∨ (p4 ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_382154426497946679792434608984 : ((((((p3 → (((p1 ∨ (p1 ∧ (p4 ∨ ((p3 → (p1 ∧ False)) ∧ (p3 → (True → p1)))))) ∨ p2) ∨ True)) ∨ (p5 ∧ False)) ∨ True) ∨ p1) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_226042511673869185816918817278 : (((p5 ∧ False) ∨ p3) ∨ (((p2 ∨ ((True ∧ (p5 → ((((p1 ∨ False) ∧ p2) → True) → (p4 ∨ True)))) → (True ∧ p1))) ∨ True) ∨ (True ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_163230113111499270179000324135 : (((False ∨ (((p2 ∨ (p2 ∧ True)) ∨ True) ∨ p5)) ∨ ((p5 ∨ False) ∨ (True ∨ (False ∧ p2)))) ∧ (((True ∧ ((p4 → p2) ∧ p1)) ∨ False) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_871190860502215774595970192220 : ((((p1 ∨ ((p2 ∧ True) → ((((p3 ∧ (p5 → ((False ∨ False) ∧ ((False ∨ ((p1 ∧ p5) ∧ True)) → p1)))) ∨ p5) ∧ p1) ∨ p2))) → False) → p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p1 ∨ ((p2 ∧ True) → ((((p3 ∧ (p5 → ((False ∨ False) ∧ ((False ∨ ((p1 ∧ p5) ∧ True)) → p1)))) ∨ p5) ∧ p1) ∨ p2))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h2
  -- False on the left can always be used.
  apply False.elim h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_122443012400547163793995658348 : (((((p1 ∧ True) ∧ (p2 ∨ (False ∨ (True → (p1 ∧ (False ∨ p2)))))) → ((True → False) ∨ ((False ∨ p4) → p5))) ∨ (False ∧ p3)) → (p5 ∨ True)) := by
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
    -- False on the left can always be used.
    apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192853734909123751760137937108 : ((((p3 ∧ ((False → False) ∨ p5)) → p3) ∧ (True ∧ p1)) → (((p1 ∧ p2) → p4) ∨ (p4 ∨ (p4 ∨ ((p2 ∧ (p1 ∧ False)) → (True → p4)))))) := by
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
  -- False on the left can always be used.
  apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48980944696087202085207286761 : (((((p2 ∧ ((p2 ∨ (p5 → (p4 ∨ p5))) → p4)) ∧ (p1 ∧ (False → (p2 ∨ (p4 ∧ (p1 ∧ p2)))))) ∨ False) ∨ (True ∨ (True ∧ p1))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



