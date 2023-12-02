variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_140144816118935837514403726834 : (((((((p3 ∧ ((p3 ∧ True) ∧ (((False ∨ p3) ∨ (p4 → True)) ∧ p1))) ∨ p3) ∧ p1) ∧ False) → p3) → (p3 ∧ p4)) → ((p5 ∨ p4) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((((p3 ∧ ((p3 ∧ True) ∧ (((False ∨ p3) ∨ (p4 → True)) ∧ p1))) ∨ p3) ∧ p1) ∧ False) → p3) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- Conjunctions on the left can always be decomposed.
      let h13 := h11.left
      let h14 := h11.right
      -- Conjunctions on the left can always be decomposed.
      let h15 := h12.left
      let h16 := h12.right
      -- Disjunctions on the left can always be decomposed.
      cases h15
      case inl h17 =>
        -- Disjunctions on the left can always be decomposed.
        cases h17
        case inl h18 =>
          -- False on the left can always be used.
          apply False.elim h18
        case inr h19 =>
          -- False on the left can always be used.
          apply False.elim h5
      case inr h20 =>
        -- False on the left can always be used.
        apply False.elim h5
    case inr h21 =>
      -- False on the left can always be used.
      apply False.elim h5
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h22 := h1 h2
  -- We need to get the right conjuct of h22 based on <expert-advice>.
  let h23 := h22.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h23



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_756233843918862386379793732598 : (((p1 ∧ (((p4 → p1) → (((((p4 ∧ True) ∨ True) ∧ p3) → ((False ∧ p5) ∧ (p2 ∨ p1))) → ((p1 ∧ p2) ∧ p3))) ∨ (p5 → p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161319588846171478192546767270 : ((True ∧ ((p2 → ((p2 ∧ p2) ∧ (p1 → (True ∧ p1)))) → ((p5 ∨ p4) → ((p4 → True) ∨ p3)))) → ((p4 ∨ ((True → p2) ∨ True)) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_221710019282878721834425223454 : (((False ∧ False) → True) ∧ (p3 → (((False ∨ ((((((False → (((True → p5) ∧ False) → p1)) ∨ False) → p2) ∧ True) ∨ p2) ∨ p4)) ∧ p1) ∨ p3))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_675644016166021923423023288997 : ((((((((p5 ∧ p4) → ((((p3 ∨ p3) ∧ p1) ∧ p2) ∨ p2)) → (p5 → True)) ∨ True) → (p4 ∨ True)) ∧ (((True → p4) → p2) → p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_671459862024621100655922166651 : ((((p2 → (((True → ((False ∨ ((p2 ∨ (p5 ∧ p1)) ∧ False)) ∨ False)) → p5) → (True ∧ ((p4 ∨ True) → p3)))) ∨ (False → (True ∨ False))) ∨ False) ∧ True) := by
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
theorem thm_5_vars_160397599556665275397239674961 : ((((((False ∧ (True ∨ p1)) ∧ p4) → (p3 → (p3 ∨ (p5 → p3)))) ∧ False) ∨ ((p3 ∨ True) → p3)) → (p5 ∨ (True → (p3 ∨ (p4 ∧ p2))))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h7 : (p3 ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h8 := h5 h7
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56526593894422968845161971825 : (((True ∨ ((p3 ∧ p2) → p1)) → ((False ∨ p5) → (True ∧ (True → ((p2 → (p4 ∨ False)) ∨ (((p5 ∧ (True ∨ True)) → True) → p5)))))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h7
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h9
      -- One of the premise coincides with the conclusion.
      exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_261318232285578784480372088412 : ((p5 → False) → ((p2 → ((p5 ∧ (((p4 ∧ (p5 → True)) ∧ p2) → ((False → p3) ∨ p1))) → (p4 ∧ ((p3 ∨ (True ∧ p1)) ∨ p5)))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64441874518818788309527744897 : ((p1 ∨ (((p4 ∨ (p2 ∧ p1)) ∨ (p5 ∨ ((False ∧ ((p1 ∧ (True ∧ p2)) ∨ (p4 ∨ (False ∧ (p3 → False))))) ∨ p2))) ∨ (True ∨ p2))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172079485837965182729959955256 : ((((((False → p4) ∨ p5) ∨ p3) ∨ ((p5 ∧ (p3 → p5)) ∧ p5)) → (p1 ∨ p1)) ∨ (((p4 ∧ (p3 ∨ (False ∧ False))) → True) ∨ (p1 → False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49793603819092809601502081365 : (((p5 ∨ ((p5 → ((True ∧ (p4 → (((p3 ∨ p1) ∧ (p3 → (p5 → (True ∧ p5)))) → p4))) ∨ p1)) → True)) → ((p1 ∨ p2) ∧ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157882354010958569224132073484 : (((((p5 → True) ∨ p4) → (False ∨ ((p2 → False) ∨ p4))) ∨ (((False ∧ False) ∧ True) → (p2 → True))) ∨ ((p4 ∨ ((True ∧ False) ∧ p3)) ∨ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315399893032203460505116865899 : (p3 ∨ (((p3 ∧ p4) ∨ p2) ∨ ((((p3 → p2) ∨ (p1 ∧ (p3 → p5))) ∨ p4) ∨ ((p3 ∧ ((False ∧ ((p3 ∧ p5) → p2)) ∧ p4)) ∨ True)))) := by
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
theorem thm_5_vars_137765591494202016357522680152 : ((p2 ∨ (((p4 ∨ p4) ∨ ((p4 ∧ (p5 ∨ p5)) ∨ ((p5 → (p5 → p5)) ∨ ((p3 → p4) → p3)))) → (p3 ∧ False))) ∨ (p1 ∨ (False → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53328582746299595495274867229 : (((p5 → (p4 ∨ ((p3 → ((p5 ∧ p1) ∨ p2)) ∧ (p4 ∧ False)))) ∨ (False → (True → (p2 ∨ ((((p1 ∧ p5) ∧ True) → p5) ∧ p4))))) ∨ p1) := by
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
theorem thm_5_vars_114676502599031593887736262501 : (((p3 ∧ ((True ∨ ((p4 ∧ (p2 ∨ p2)) ∨ ((False ∨ (False ∧ p4)) ∧ True))) → p1)) ∨ (((p4 → (p3 ∨ p3)) ∧ p2) ∧ p5)) ∨ (True ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161841409513152471432137327412 : ((True → (((p5 ∧ p1) → (True → (p5 → ((False ∨ p1) ∨ p4)))) → (p5 ∧ ((p5 → False) ∧ p3)))) → ((False → p5) → ((p4 → p5) → p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h4
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h6 : ((p5 ∧ p1) → (True → (p5 → ((False ∨ p1) ∨ p4)))) := by
    -- Implications on the right can always be decomposed.
    intro h7
    -- Implications on the right can always be decomposed.
    intro h8
    -- Implications on the right can always be decomposed.
    intro h9
    -- Conjunctions on the left can always be decomposed.
    let h10 := h7.left
    let h11 := h7.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h11
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h12 := h5 h6
  -- We need to get the right conjuct of h12 based on <expert-advice>.
  let h13 := h12.right
  -- We need to get the right conjuct of h13 based on <expert-advice>.
  let h14 := h13.right
  -- One of the premise coincides with the conclusion.
  exact h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_719259179481973915997336986141 : ((((p4 ∧ ((p5 ∧ False) ∧ p3)) ∨ ((((False → (p1 ∧ (p2 ∧ p5))) ∧ True) ∨ (p4 ∨ (False ∨ (p3 ∨ (False ∨ False))))) → (p5 → p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217108680360325964267896743065 : ((((True ∨ p5) ∨ p4) ∨ p3) → (((p5 ∨ ((p1 → p1) ∧ (((p4 ∧ True) ∨ p3) ∧ p2))) ∨ (True → ((p3 ∨ p4) ∧ (False ∨ p4)))) ∨ True)) := by
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
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h5 =>
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
theorem thm_5_vars_180117267548537752412658157423 : ((((True ∧ ((((p1 ∨ p5) → (p3 ∧ p2)) → p5) ∨ p3)) ∨ p4) → False) → (True → ((((p2 → (True ∧ p1)) ∨ (p1 ∨ False)) ∧ p4) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217633111898519916817026531081 : ((((p2 ∧ p4) → True) → p1) → (((((False ∨ ((p3 ∨ (p2 → p4)) ∧ p5)) ∨ p4) ∨ p2) → p3) ∨ (((p4 ∧ p1) ∧ True) ∨ (p1 ∨ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p2 ∧ p4) → True) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37859059067085874502776857259 : ((((p2 → ((p4 → (((p3 → False) ∧ (((p2 ∧ p3) ∧ p1) ∧ False)) → ((p5 ∧ (True ∨ True)) → p5))) ∨ (False ∧ p3))) → False) ∧ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185188962043856550357560696528 : ((True ∧ (((False ∧ ((p5 → (p3 → p3)) → p5)) ∧ p5) ∨ True)) ∨ (((((p1 ∧ p1) → p5) ∨ ((p1 ∨ True) → p3)) → (False ∨ p4)) ∧ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_658353084004737403981074931030 : ((((False ∨ (((p2 ∨ (p2 → (((((p5 ∧ p4) ∧ (p1 → True)) → (p3 → (p4 ∧ True))) ∨ True) → True))) ∧ p1) ∨ p4)) ∨ (p4 ∨ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68850688868511068750450375601 : ((p4 → ((p1 → p2) ∨ ((p4 ∧ False) ∨ (False ∨ (((((p1 → p3) → (p2 ∨ ((True → p2) ∨ False))) ∨ p3) ∨ p2) → (p3 → p3)))))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h6 =>
      -- One of the premise coincides with the conclusion.
      exact h6
  case inr h7 =>
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159333049336213627695498244808 : ((p5 → (p2 ∨ (((p3 ∨ (((((p4 → False) → p4) ∧ p4) ∧ (True ∨ p4)) ∨ p1)) → p3) ∨ p4))) ∨ ((False ∧ ((True ∨ p4) → p3)) → p2)) := by
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
theorem thm_5_vars_215536665844621342394098867433 : ((p4 ∧ (True → (p2 ∧ p1))) ∨ ((p1 ∨ p1) → (((p4 ∨ (p4 ∨ p3)) ∧ (((p3 → (False ∨ p4)) ∧ p4) → (p4 ∨ False))) ∨ (p1 ∧ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h2
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h3
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_693904162282085522787121025063 : ((((((p2 ∨ (p3 → ((p5 ∨ (False ∧ p4)) ∧ True))) ∧ p4) ∧ (p5 ∧ False)) ∨ ((((True → (True → False)) ∧ True) → (p4 → p3)) → True)) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135573327253818618638467881384 : ((((p1 ∧ (((p3 ∨ (((p3 ∧ False) → (p1 → True)) → p5)) ∧ p5) ∧ True)) ∧ p2) ∨ (((False → False) ∨ p5) → False)) ∨ ((p4 → False) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49747758729380848875162718770 : (((p4 ∧ (False → ((((p4 ∧ (p3 → p3)) → p1) ∨ False) ∧ (False ∧ (p5 → (False → (p3 → (p4 ∨ p1)))))))) → (p2 ∧ (p3 → p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_469257492864592378062702626096 : (((((p2 ∨ (p5 ∨ p5)) ∨ ((p2 ∨ (p3 → (p4 → (p4 → True)))) ∨ p1)) → (((((p1 ∨ (False ∧ p3)) ∧ p1) ∧ p4) ∧ False) ∨ True)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h4 =>
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
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248166354703774566947132420591 : ((p2 ∨ False) ∨ (((p4 ∨ p2) ∧ p4) ∨ (((p3 ∨ (p5 ∧ False)) ∧ (False ∧ (p4 ∨ False))) → ((p3 ∨ (True ∧ p2)) ∧ ((False ∨ p1) ∧ p2))))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h3.left
    let h6 := h3.right
    -- False on the left can always be used.
    apply False.elim h5
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- False on the left can always be used.
    apply False.elim h9
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h10 := h1.left
  let h11 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h10
  case inl h12 =>
    -- Conjunctions on the left can always be decomposed.
    let h13 := h11.left
    let h14 := h11.right
    -- False on the left can always be used.
    apply False.elim h13
  case inr h15 =>
    -- Conjunctions on the left can always be decomposed.
    let h16 := h15.left
    let h17 := h15.right
    -- False on the left can always be used.
    apply False.elim h17
  -- Conjunctions on the left can always be decomposed.
  let h18 := h1.left
  let h19 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h18
  case inl h20 =>
    -- Conjunctions on the left can always be decomposed.
    let h21 := h19.left
    let h22 := h19.right
    -- False on the left can always be used.
    apply False.elim h21
  case inr h23 =>
    -- Conjunctions on the left can always be decomposed.
    let h24 := h23.left
    let h25 := h23.right
    -- False on the left can always be used.
    apply False.elim h25



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46351541121919502492180978338 : (((((p5 → ((True → p2) ∧ ((p3 → p5) → ((True ∧ False) ∧ p1)))) → p3) → (True → ((p1 ∧ p3) ∨ (p3 → False)))) ∧ (p3 ∨ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193401811718362266096423373425 : (((p4 ∧ p3) ∧ (p2 ∧ (p5 ∨ (False → (p5 → False))))) → (p3 → (((p5 → p1) → (True → p5)) ∨ ((p5 → (p5 → p2)) ∧ (p3 ∨ p5))))) := by
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
  let h7 := h4.left
  let h8 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h9 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h10
    -- Implications on the right can always be decomposed.
    intro h11
    -- One of the premise coincides with the conclusion.
    exact h9
  case inr h12 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h13
    -- Implications on the right can always be decomposed.
    intro h14
    -- One of the premise coincides with the conclusion.
    exact h7
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137912738558490571141909802195 : ((p4 ∨ (((p5 ∨ (True ∨ False)) ∧ p1) → ((p5 → p1) → ((((False ∨ True) ∧ p1) → ((p4 ∧ p3) ∨ True)) ∨ False)))) ∨ ((p1 ∧ p3) ∨ p3)) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h6
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h9 =>
      -- False on the left can always be used.
      apply False.elim h9
    case inr h10 =>
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
      -- Implications on the right can always be decomposed.
      intro h13
      -- Conjunctions on the left can always be decomposed.
      let h14 := h13.left
      let h15 := h13.right
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h16 =>
        -- False on the left can always be used.
        apply False.elim h16
      case inr h17 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h18 =>
      -- False on the left can always be used.
      apply False.elim h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_123430249725108628846113750842 : ((((p5 → (p5 → (False ∨ p3))) → ((((p3 ∨ (p3 → p5)) ∧ (p3 ∨ True)) ∨ p3) ∨ True)) → (((True ∨ False) → False) ∨ p3)) → (p1 ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p5 → (p5 → (False ∨ p3))) → ((((p3 ∨ (p3 → p5)) ∧ (p3 ∨ True)) ∨ p3) ∨ True)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h6 : (True ∨ False) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h7 := h5 h6
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347039894111568337508842340096 : (p3 → (((((p4 ∨ p1) ∧ p4) → (((p2 → (False ∨ True)) ∧ (True → p5)) → p5)) → p3) → ((p1 ∨ (((p1 → p4) ∨ True) ∧ p3)) ∧ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
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
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42865792523086560388207565439 : (((p2 → ((p3 ∨ p4) ∧ (((p5 ∨ (p5 ∧ p3)) → p4) → (p4 ∧ (p3 ∨ ((p1 ∧ ((p2 ∧ p2) → (False → p1))) → p5)))))) ∨ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114038667202298653900568315628 : ((((((((p4 → p1) ∨ False) → (p4 ∨ ((p4 ∨ False) ∨ True))) → (False ∨ p4)) ∨ True) ∧ (p1 ∨ True)) ∨ ((p1 → p2) ∧ True)) ∨ (True ∧ p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_104510023197409855188834979266 : (((((((((((True ∨ p3) ∨ False) ∧ p5) ∨ (p1 ∨ p4)) ∨ p4) → p1) ∧ p2) ∨ (p3 → (False ∨ p4))) ∨ p2) ∨ (False → False)) ∧ (p3 ∨ True)) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_693564172462135064102098087288 : (((((False ∧ ((p1 ∧ (p1 → True)) ∨ (p4 ∨ ((p2 → p2) ∨ p3)))) ∧ p1) ∨ (((p3 ∧ (p1 → True)) → p1) ∨ ((p2 → False) ∧ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_730632036725821885614320001242 : ((((p2 ∧ (False → False)) → ((((True ∨ p5) ∧ (p3 ∧ ((p5 → True) ∧ p2))) → p4) ∨ (p2 → (p2 → (p2 ∨ (p3 → (p1 → True))))))) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_201053259814091655869477060935 : ((p4 ∨ (p2 → (p3 ∧ (p4 ∧ (False → p5))))) → ((p2 ∨ (((False ∧ False) ∨ (p5 ∧ p1)) → p4)) → (p3 ∨ (p2 ∨ ((p4 ∨ False) → p4))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h3
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
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
        -- False on the left can always be used.
        apply False.elim h10
    case inr h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h12
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- One of the premise coincides with the conclusion.
        exact h13
      case inr h14 =>
        -- False on the left can always be used.
        apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_781435895092266248038277735704 : (((p2 ∨ (p4 ∧ (((p4 → (p4 → ((p5 → (((True ∨ (p5 → p2)) → p4) ∧ p3)) ∨ p4))) → ((p4 ∧ p2) ∨ (p4 → p4))) → p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198682731421890934294162004126 : ((p4 ∨ ((p1 ∨ False) ∧ (p3 ∧ (p2 → p1)))) ∨ ((p5 ∨ ((False → p3) ∨ p5)) ∨ ((True → (False ∨ False)) ∨ (p5 ∨ (p5 ∧ (p4 ∧ p4)))))) := by
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
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_339753325617927745693598512712 : (p1 → (p4 ∨ ((p5 → ((p5 → False) → False)) → ((((p3 ∧ (False → p1)) ∧ (p1 ∨ p5)) ∨ (p2 → p3)) ∨ (p2 → (p2 ∧ (True ∨ p5))))))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_652113668423146302541920672445 : ((((p1 ∧ (((False ∧ ((((p4 ∨ ((p3 ∧ p4) ∨ p4)) ∧ p3) ∧ (p3 → p5)) ∧ p3)) → ((p1 ∨ False) ∧ p2)) → p3)) ∧ (False ∨ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_907568634866318846855125659779 : (((((p3 ∨ True) → (p1 ∨ (p4 → (False → (p2 ∧ ((p2 → (((p4 → p3) → False) ∨ p4)) ∧ p1)))))) → (True ∧ ((p5 ∨ True) ∧ p5))) → p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p3 ∨ True) → (p1 ∨ (p4 → (False → (p2 ∧ ((p2 → (((p4 → p3) → False) ∨ p4)) ∧ p1)))))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h5
      -- Implications on the right can always be decomposed.
      intro h6
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- False on the left can always be used.
      apply False.elim h6
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h7
      -- False on the left can always be used.
      apply False.elim h6
      -- False on the left can always be used.
      apply False.elim h6
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h9
      -- Implications on the right can always be decomposed.
      intro h10
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- False on the left can always be used.
      apply False.elim h10
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h11
      -- False on the left can always be used.
      apply False.elim h10
      -- False on the left can always be used.
      apply False.elim h10
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h12 := h1 h2
  -- We need to get the right conjuct of h12 based on <expert-advice>.
  let h13 := h12.right
  -- We need to get the right conjuct of h13 based on <expert-advice>.
  let h14 := h13.right
  -- One of the premise coincides with the conclusion.
  exact h14
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_686915368684431733747268502855 : ((((p1 ∨ ((((((False ∨ p2) ∧ False) → (p4 ∨ p3)) → (p5 → p1)) ∨ (True → p1)) ∧ p5)) → (((p1 ∧ p5) ∧ (p3 → p4)) ∨ True)) ∨ p2) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135270603995364096708450163463 : (((p1 ∨ ((((p4 ∨ (True ∨ p2)) ∨ False) → (p4 → p2)) ∨ (((p1 ∧ p1) ∨ p5) ∨ (True ∨ p2)))) → (p4 → p1)) ∨ ((p5 → p1) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_722318107814217717780173101150 : (((((p1 ∧ p5) ∧ False) ∧ (((((p1 → False) ∨ (((True ∨ (p2 ∧ p1)) → (p3 ∨ p4)) ∨ p5)) ∧ p2) → (p5 ∨ (p2 ∧ True))) ∨ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61514047099597714163642371740 : ((p1 ∧ (((p2 ∨ (True → (p5 ∧ ((p4 ∧ p5) ∨ (((p1 ∨ p1) → p1) ∨ False))))) ∨ p4) ∧ (p1 → ((p2 ∨ True) ∧ (False ∨ p5))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114094694717067481702790464712 : (((True ∧ (((p1 ∧ True) ∧ (True → ((True ∧ p5) → (((p5 ∧ p1) → p1) ∧ (p4 ∨ False))))) → False)) ∨ (True ∧ (p5 ∧ True))) ∨ (False → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_656990633022836670381309693809 : (((((p5 ∧ ((True → p3) ∧ True)) → (((False ∧ p4) → (p3 ∨ p5)) ∧ (False ∨ ((p5 ∨ p5) → ((p3 ∧ p2) ∧ p4))))) ∨ (p5 → p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158039029484653877339028901379 : ((((((False ∧ False) ∨ False) ∨ p1) ∨ p4) ∨ (p5 ∧ (((p1 ∧ (p4 → False)) ∧ (p3 ∧ p1)) → p2))) ∨ (p4 ∨ (False → ((p4 ∧ p1) ∧ True)))) := by
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
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_617432952368468231784121816350 : (((((p3 → (((p4 → p3) → True) → (p4 ∧ p1))) → ((((False ∧ p2) ∨ p1) → ((True → ((p1 → True) ∧ p3)) ∨ p1)) ∨ p4)) ∨ False) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- False on the left can always be used.
    apply False.elim h4
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217384431918103672728200667074 : (((p5 ∨ (True → False)) ∨ p2) → (((True ∨ p3) ∧ (False → p1)) ∧ (p5 → ((((False ∧ p4) ∨ p5) ∧ (p1 → p2)) ∨ ((p5 ∧ p5) ∨ p3))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- Implications on the right can always be decomposed.
  intro h6
  -- False on the left can always be used.
  apply False.elim h6
  -- Implications on the right can always be decomposed.
  intro h7
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h9
      -- One of the premise coincides with the conclusion.
      exact h9
    case inr h10 =>
      -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
      have h11 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h10, we can now drive its conclusion.
      let h12 := h10 h11
      -- False on the left can always be used.
      apply False.elim h12
  case inr h13 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h7
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304685703342204366654267491668 : (p1 ∨ (((((((p3 → (p3 ∧ ((p3 ∧ p3) → False))) → (False ∧ p2)) ∨ (True ∨ (p2 → (p2 → p5)))) ∨ p2) → p4) ∨ True) ∨ (True ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303055412334848973021432570300 : (False ∨ (p2 → ((((((True ∨ True) → False) → p1) → p4) ∧ (p5 ∧ (((p3 → p4) ∧ True) ∧ (True ∨ (True ∧ (p1 → False)))))) ∨ (True → p2)))) := by
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
theorem thm_5_vars_191728798906225020060128418995 : ((False ∨ ((False ∨ ((p1 → False) ∧ (p5 ∨ True))) ∧ p4)) ∨ ((p4 ∨ (p3 → (p3 ∨ (False ∧ ((p1 ∨ (p1 ∧ True)) ∧ (False ∧ p2)))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165813939692294294357655471067 : (((False ∧ (False ∧ True)) ∧ ((p5 ∧ (True ∨ (p3 → ((p5 → p4) ∨ p1)))) ∧ (True ∨ p1))) ∨ (((False → p1) → False) → (p1 ∧ (p5 → False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Implications on the right can always be decomposed.
  intro h5
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h6 : (False → p1) := by
    -- Implications on the right can always be decomposed.
    intro h7
    -- False on the left can always be used.
    apply False.elim h7
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h8 := h1 h6
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158431840143618709621211358961 : (((False ∨ False) ∨ ((p2 ∧ (p2 ∧ (((p3 → p4) ∨ p2) ∨ (p2 ∧ True)))) ∧ (True → (False → p4)))) ∨ (((True ∨ (p4 → p1)) → p5) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40438076712384617586698527062 : (((((p2 → (((((True → p4) ∧ p3) → False) ∨ p4) ∧ p5)) → ((p4 ∧ ((False ∨ p3) ∧ False)) ∨ (p1 ∧ (p3 ∨ p5)))) ∨ True) ∨ p1) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_176254436167087323940593556190 : (((((((False ∧ p1) ∨ True) ∧ (p2 ∧ False)) ∧ p3) ∧ p4) ∨ (p1 ∨ True)) ∧ (p3 → (((True ∨ p4) ∨ True) → (p4 ∨ ((p1 ∨ True) ∧ p3))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
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
      -- True on the right can always be proven directly.
      apply True.intro
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h5 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h5
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68144092503845548230797007083 : ((p3 → (((((((p1 → p4) ∨ (False ∧ p5)) ∧ (p1 ∧ ((p1 ∨ p4) ∧ ((False → p4) ∨ p1)))) ∧ p2) ∨ False) ∨ (False ∧ True)) ∧ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_330375059373595587785124126583 : (True → (p2 ∨ (((True ∧ (((p3 ∧ True) ∨ (p3 → ((p4 ∧ False) ∧ p3))) ∨ (p2 ∧ True))) ∨ (p1 → p1)) → ((p5 ∧ p3) ∨ (p3 → True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Conjunctions on the left can always be decomposed.
        let h8 := h7.left
        let h9 := h7.right
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
      -- Conjunctions on the left can always be decomposed.
      let h14 := h13.left
      let h15 := h13.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h16
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h17 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h18
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187427915292348547375071983864 : ((p5 ∧ (((p2 → p2) ∧ (p1 → p1)) → (True ∧ (p4 ∧ p2)))) → (((p1 → p5) → ((((False ∨ (p1 → p5)) → p1) ∨ p4) ∧ p2)) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h5 : ((p2 → p2) ∧ (p1 → p1)) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h6
    -- One of the premise coincides with the conclusion.
    exact h6
    -- Implications on the right can always be decomposed.
    intro h7
    -- One of the premise coincides with the conclusion.
    exact h7
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h8 := h3 h5
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- We need to get the left conjuct of h9 based on <expert-advice>.
  let h10 := h9.left
  -- One of the premise coincides with the conclusion.
  exact h10
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h11 : ((p2 → p2) ∧ (p1 → p1)) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h12
    -- One of the premise coincides with the conclusion.
    exact h12
    -- Implications on the right can always be decomposed.
    intro h13
    -- One of the premise coincides with the conclusion.
    exact h13
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h14 := h3 h11
  -- We need to get the right conjuct of h14 based on <expert-advice>.
  let h15 := h14.right
  -- We need to get the right conjuct of h15 based on <expert-advice>.
  let h16 := h15.right
  -- One of the premise coincides with the conclusion.
  exact h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114260312972072646695242304679 : (((p4 → (p5 ∧ (p3 ∨ (False ∧ (p5 → (((((p4 → (True ∨ p2)) → p4) → True) ∧ p1) → False)))))) → (p5 ∨ (p3 ∨ p2))) ∨ (p3 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48407936741060944440023352652 : (((p1 → (True → ((p2 → ((p2 ∧ p5) ∨ (p3 → p1))) ∨ (((p3 ∨ p4) ∧ ((False ∨ p3) ∧ (True → True))) ∧ p4)))) → (False ∧ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337654197161114684380618249324 : (p1 → ((((((p3 ∧ (p1 ∧ ((p5 → p4) ∨ False))) ∧ True) ∨ (p1 ∨ True)) ∧ (False → p1)) → p4) ∨ (p3 ∨ ((p5 ∧ (p2 ∨ p2)) → p1)))) := by
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
  cases h4
  case inl h5 =>
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h6 =>
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119791599745552644776921862254 : (((((p2 → (((p4 ∧ p1) ∧ ((p3 ∨ False) ∨ p3)) ∨ ((False ∧ False) ∨ (((p1 ∧ p4) ∨ p1) → p5)))) ∨ p4) → p5) ∧ p1) → (p4 → p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h5 : ((p2 → (((p4 ∧ p1) ∧ ((p3 ∨ False) ∨ p3)) ∨ ((False ∧ False) ∨ (((p1 ∧ p4) ∨ p1) → p5)))) ∨ p4) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h5
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137061528605498176488030094066 : (((p2 → p5) → ((p4 ∧ (p5 ∧ (p4 ∧ ((((((p2 ∨ True) ∧ p4) → p2) ∧ False) → p2) ∨ (p5 → p3))))) → p2)) ∨ ((p4 ∧ p1) → p4)) := by
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
theorem thm_5_vars_119135049875145535517405462318 : ((p1 → (p3 ∨ (((p2 ∨ (p2 ∧ (p5 ∧ (((p3 → (True ∧ p5)) ∧ p3) → (False ∨ ((p4 → False) → True)))))) ∨ True) ∧ p2))) ∨ (True ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351624874880375320876859204562 : (p4 → (((False ∨ (p2 → (((True ∨ ((p5 → p4) ∧ p3)) → False) ∧ (p3 → False)))) ∧ p1) ∨ ((p3 ∧ (p5 → ((p2 → p4) ∧ p1))) ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38563925304891593300114061669 : ((((((True ∧ p4) ∧ (p4 ∧ p1)) ∧ (True ∧ (p2 ∨ p4))) ∨ ((p3 ∧ (p2 → (((p2 ∨ p2) ∨ (True ∨ p5)) ∧ p3))) → True)) ∧ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_810947054350036169418620792066 : (((p5 → ((p1 ∨ p5) → ((True ∨ p1) ∧ (p1 ∨ ((p3 ∧ True) ∨ ((((True → ((p1 ∧ p3) → (True ∨ p4))) ∨ p5) ∧ True) → p3)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205624733258700664414461167709 : (((p2 ∧ True) ∨ ((p2 ∨ p4) ∧ True)) ∨ (((((((True → p2) ∨ (False ∨ p3)) → False) ∨ (True ∧ p4)) ∧ ((p1 ∧ p3) → True)) → p1) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_589306574680692459220630345338 : ((((((True → ((p2 → ((p1 → p5) ∧ ((p5 ∧ False) → (True ∨ True)))) ∧ (p1 ∧ (p3 ∨ (p1 ∧ (True ∧ p1)))))) ∧ True) → p1) ∧ True) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- We need to get the left conjuct of h6 based on <expert-advice>.
  let h7 := h6.left
  -- One of the premise coincides with the conclusion.
  exact h7
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_224605320416026909679440104197 : ((p2 → (p4 → True)) ∧ ((((((((p1 ∧ (True ∨ p3)) → False) ∨ p4) ∨ p1) ∨ (p4 ∨ True)) ∨ ((p4 → (True ∧ p4)) ∧ p1)) → p2) → p2)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : ((((((p1 ∧ (True ∨ p3)) → False) ∨ p4) ∨ p1) ∨ (p4 ∨ True)) ∨ ((p4 → (True ∧ p4)) ∧ p1)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193618866646749494397558534539 : ((True ∧ ((p4 ∨ ((p5 ∨ p3) → (p2 ∨ False))) → p3)) → ((p2 → ((((p3 ∧ p3) ∧ True) ∨ p1) ∧ p5)) ∨ ((True → (p2 ∨ p4)) → p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h5 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h6 := h4 h5
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h7 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h8 : (p4 ∨ ((p5 ∨ p3) → (p2 ∨ False))) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h9
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h7
      case inr h11 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h7
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h12 := h3 h8
    -- One of the premise coincides with the conclusion.
    exact h12
  case inr h13 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h14 : (p4 ∨ ((p5 ∨ p3) → (p2 ∨ False))) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h13
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h15 := h3 h14
    -- One of the premise coincides with the conclusion.
    exact h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200226327573922946576912396121 : ((((p5 → True) ∧ p4) → (False → (p4 → p3))) → ((((((False ∨ False) ∨ (p3 ∧ p5)) ∨ p3) → ((p4 → p1) ∧ p2)) ∨ (p5 → p5)) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_306188318038486568021983563057 : (p1 ∨ ((p1 ∨ (p2 ∨ p5)) ∨ ((p3 ∧ (p2 ∧ (((p2 → p3) → ((((p3 → p3) → p4) ∧ p4) → False)) ∨ p2))) → (p5 → (False ∨ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Disjunctions on the left can always be decomposed.
  cases h6
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_780700635523922085502441877406 : (((p2 ∨ (((p1 ∧ (p4 → (p5 → p2))) ∧ p4) ∧ (False ∧ (((p5 ∧ ((p1 → (p5 ∧ True)) ∧ ((True ∧ p5) ∨ p3))) ∨ False) ∧ True)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228655028682847711307042214500 : ((p2 ∨ (p3 ∧ False)) ∨ (((p1 → (p3 → (False ∧ p1))) ∧ (p1 ∧ p2)) → ((((p4 ∧ (p4 ∧ (p1 → p1))) ∨ (p2 ∨ p4)) ∨ False) ∧ True))) := by
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
  let h4 := h3.left
  let h5 := h3.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158216033015185333647778217626 : (((True ∧ (p2 → p1)) ∧ (p3 ∧ (p4 ∧ ((p4 → p5) → (False ∨ (p3 ∨ ((False ∧ False) ∧ p5))))))) ∨ (p1 ∨ (p5 ∨ ((p1 ∧ p3) ∨ True)))) := by
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
theorem thm_5_vars_116224656659983369148469026089 : ((((True → p5) ∨ p3) ∨ ((((p2 → (True ∨ p3)) → (((p3 ∧ False) → (p2 ∨ True)) ∧ p3)) ∧ p1) ∧ ((p5 → p4) → p5))) ∨ (p3 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225101791693158283502882827269 : (((p2 ∧ p1) ∧ p1) ∨ (((False ∨ (False → p4)) → ((((False → p1) ∨ False) ∨ False) ∧ (False ∧ ((p1 ∨ p1) → (True → (p2 ∧ True)))))) → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (False ∨ (False → p4)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_255207669213884953938212335539 : ((p4 ∧ p4) → (((((p5 ∨ p5) ∨ p4) ∨ True) ∨ p1) → ((p5 ∨ ((False ∨ True) ∨ (p3 → (p4 → (p5 ∧ p4))))) ∧ (True ∨ (p5 ∧ p1))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h5 =>
        -- Disjunctions on the left can always be decomposed.
        cases h5
        case inl h6 =>
          -- Conjunctions on the left can always be decomposed.
          let h7 := h1.left
          let h8 := h1.right
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h6
        case inr h9 =>
          -- Conjunctions on the left can always be decomposed.
          let h10 := h1.left
          let h11 := h1.right
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h9
      case inr h12 =>
        -- Conjunctions on the left can always be decomposed.
        let h13 := h1.left
        let h14 := h1.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h15 =>
      -- Conjunctions on the left can always be decomposed.
      let h16 := h1.left
      let h17 := h1.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h18 =>
    -- Conjunctions on the left can always be decomposed.
    let h19 := h1.left
    let h20 := h1.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h21 =>
    -- Disjunctions on the left can always be decomposed.
    cases h21
    case inl h22 =>
      -- Disjunctions on the left can always be decomposed.
      cases h22
      case inl h23 =>
        -- Disjunctions on the left can always be decomposed.
        cases h23
        case inl h24 =>
          -- Conjunctions on the left can always be decomposed.
          let h25 := h1.left
          let h26 := h1.right
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h27 =>
          -- Conjunctions on the left can always be decomposed.
          let h28 := h1.left
          let h29 := h1.right
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h30 =>
        -- Conjunctions on the left can always be decomposed.
        let h31 := h1.left
        let h32 := h1.right
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h33 =>
      -- Conjunctions on the left can always be decomposed.
      let h34 := h1.left
      let h35 := h1.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h36 =>
    -- Conjunctions on the left can always be decomposed.
    let h37 := h1.left
    let h38 := h1.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_749602649257942621510990505374 : (((True ∧ ((((((p4 → p4) → (p5 ∧ (p2 ∨ p5))) ∨ (False ∨ ((False ∨ p3) → (p5 → ((p4 ∨ p4) ∧ p2))))) ∨ p3) ∧ p4) ∨ True)) ∨ False) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_590802925700043274054781604191 : (((((p2 ∨ (((p1 ∧ (p2 ∨ True)) → p4) ∨ (((((p5 → p4) ∧ p5) → p5) ∧ (True ∨ (True ∧ p4))) → (p5 → p2)))) → p2) ∧ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_3140652307387159677427402808 : ((False → False) ∧ (((p3 ∧ False) ∧ p5) ∨ ((p5 ∧ (p1 ∧ True)) → (False ∨ ((((p2 → True) ∧ p1) → p3) ∨ ((False ∨ p4) → True)))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156759158512937870631788365851 : ((((p3 ∨ p2) ∧ ((((False ∨ p5) ∨ p1) ∧ (True ∧ p2)) ∨ (True ∧ ((p3 ∧ p3) ∨ p1)))) ∧ p3) ∨ ((((False → False) → p4) ∧ p4) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37716531945053640533494353350 : (((((True ∧ ((((False → (p3 → p4)) ∨ (True ∧ ((p4 ∨ p1) ∨ p2))) → p5) ∧ True)) → (p5 ∨ (p3 → (False ∨ p1)))) → False) ∧ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136196402386577587761779126264 : ((((p1 → p3) → ((p1 ∧ p4) ∧ p1)) ∧ (((((p2 ∨ False) ∨ p5) → ((p5 ∨ p2) → p2)) ∨ p5) ∨ (True ∧ p3))) ∨ (p5 → (True ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184978133359425181145836471617 : (((True → (p1 ∨ p4)) → ((p1 ∧ p2) ∧ (p4 ∧ (p5 ∧ p1)))) ∨ (True ∨ (((((((p1 ∨ p5) ∧ False) ∧ p1) → p3) → p1) ∧ p1) ∧ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_247613415200531599172529110656 : ((False ∨ p5) ∨ (((p2 ∧ p4) → ((p2 ∧ p5) → (p3 ∧ (p4 ∧ False)))) ∨ (((False ∧ (p3 → p2)) ∧ p3) ∨ (p1 → ((p3 ∨ p1) → p1))))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h4 =>
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_614554917892335620702750511494 : (((((((p4 ∧ (p4 ∨ p5)) → p5) ∧ ((p3 → (p1 ∨ p2)) ∧ (True ∧ ((True ∧ p5) ∨ p5)))) ∧ (True ∨ (p4 → (p5 ∨ True)))) ∨ True) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_328789944858149117278944233528 : (True → (((False ∧ (((p4 ∨ p3) ∧ False) ∧ p2)) ∧ (p3 ∨ p1)) ∨ (False → (p1 → ((p2 ∧ (False ∨ (p2 → ((p3 ∧ p3) → True)))) ∨ p1))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_706050080873980902347978432113 : (((((False ∧ p5) ∨ ((p5 → (p2 → True)) ∨ p4)) ∧ ((((False ∨ p3) ∨ p5) ∧ (False ∧ (True ∧ p1))) ∧ ((p1 ∨ (False → p5)) ∧ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



