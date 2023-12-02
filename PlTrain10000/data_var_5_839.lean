variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51963154027607149790817403524 : (((((True ∨ True) ∧ p5) ∧ ((p1 ∨ p1) ∧ (((p2 ∧ p1) ∨ p5) ∨ (p5 ∨ p2)))) ∨ ((True ∨ (False ∨ ((False ∨ True) ∧ True))) ∨ p2)) ∨ p5) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218104330655552671712607055238 : (((False → p5) ∧ (p5 → p1)) → ((p1 ∧ (p1 → (p3 → p2))) → ((p3 ∧ (False → (((p1 ∧ p5) ∧ p4) ∨ True))) ∨ ((p5 → p2) → p1)))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h7
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135127172661665195453986009830 : (((p1 ∧ (((p4 ∨ (p4 ∧ ((p4 ∧ ((p5 → p1) ∧ True)) ∧ True))) ∨ False) ∨ ((p4 → p1) → p3))) ∨ (p3 ∨ p3)) ∨ ((p1 → False) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168635705006924077699680015642 : ((p4 ∧ (((p1 ∧ (p5 → p4)) ∨ (((True → p5) ∧ ((p2 ∧ True) ∧ p5)) → p3)) ∨ False)) → ((p2 ∨ p3) → (((p2 ∧ p5) ∨ p5) ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h1.left
    let h5 := h1.right
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
        -- One of the premise coincides with the conclusion.
        exact h4
      case inr h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h4
    case inr h11 =>
      -- False on the left can always be used.
      apply False.elim h11
  case inr h12 =>
    -- Conjunctions on the left can always be decomposed.
    let h13 := h1.left
    let h14 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h14
    case inl h15 =>
      -- Disjunctions on the left can always be decomposed.
      cases h15
      case inl h16 =>
        -- Conjunctions on the left can always be decomposed.
        let h17 := h16.left
        let h18 := h16.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h13
      case inr h19 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h13
    case inr h20 =>
      -- False on the left can always be used.
      apply False.elim h20



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_243005359900379315746778938665 : ((p4 → True) ∧ (((p3 ∨ False) ∨ True) → ((((((p2 ∧ (p3 → False)) ∧ p4) ∧ True) ∧ p2) → ((((p5 ∨ False) ∨ p5) ∧ p3) ∨ True)) ∨ p4))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h5
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
      let h12 := h10.left
      let h13 := h10.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h14 =>
      -- False on the left can always be used.
      apply False.elim h14
  case inr h15 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h16
    -- Conjunctions on the left can always be decomposed.
    let h17 := h16.left
    let h18 := h16.right
    -- Conjunctions on the left can always be decomposed.
    let h19 := h17.left
    let h20 := h17.right
    -- Conjunctions on the left can always be decomposed.
    let h21 := h19.left
    let h22 := h19.right
    -- Conjunctions on the left can always be decomposed.
    let h23 := h21.left
    let h24 := h21.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_154837220503257680564643187487 : (((p1 ∧ (True → (p1 ∨ (((p4 → (True → p5)) ∨ p4) ∧ ((p4 → True) ∨ p1))))) → (p5 → p5)) ∧ (p3 ∨ (True ∨ ((p5 ∧ p5) → p3)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47490291361153711046475296429 : (((False ∨ ((p3 ∨ p5) ∧ (p2 → ((((p3 ∨ p4) → True) ∧ (p4 → (p2 ∧ (p4 ∧ p5)))) → ((p1 ∨ False) ∨ p2))))) ∨ (p5 → True)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313228666178187845987683115278 : (p3 ∨ (((False ∨ p2) ∧ ((p5 ∧ ((p4 → (p1 ∨ p5)) ∨ (((p2 ∧ (p4 ∧ False)) ∧ p2) ∨ (False → True)))) ∧ ((p4 ∨ p4) ∧ p3))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160440907175238934356716565680 : (((((((True ∧ (p4 ∧ p1)) ∧ (False → (p3 → p3))) → False) → p2) ∧ False) → ((p2 → False) → p3)) → ((p1 ∨ (p2 ∨ (False ∨ True))) ∨ p4)) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180924112176369817575794391472 : (((p1 ∧ p2) ∧ (((p2 ∨ True) ∧ (p4 → (p3 ∨ (p5 → p4)))) ∨ p1)) → ((True ∧ (True ∨ (False → p1))) ∧ (p2 → ((p3 ∨ p4) ∨ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h9 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h10 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h11 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- Implications on the right can always be decomposed.
  intro h12
  -- Conjunctions on the left can always be decomposed.
  let h13 := h1.left
  let h14 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h15 := h13.left
  let h16 := h13.right
  -- Disjunctions on the left can always be decomposed.
  cases h14
  case inl h17 =>
    -- Conjunctions on the left can always be decomposed.
    let h18 := h17.left
    let h19 := h17.right
    -- Disjunctions on the left can always be decomposed.
    cases h18
    case inl h20 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h15
    case inr h21 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h15
  case inr h22 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h22



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55822181519484722267275582400 : ((((p1 → p4) → (p3 ∧ p3)) ∧ (((p4 ∨ ((p5 → ((p2 ∧ p5) → ((True → False) ∨ (True ∧ p5)))) ∨ p4)) ∧ (p4 → p2)) ∨ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157109854210531580894238557162 : (((p4 → ((p4 → False) ∧ (p1 ∧ (((p2 ∧ p1) → (p4 → p3)) ∨ ((True → p3) ∧ True))))) ∨ p4) ∨ (((p3 → p5) ∨ p4) ∨ (p5 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_650468328380983351468605882128 : (((((((p2 ∨ p1) ∧ (((True ∨ (p5 ∨ p3)) ∧ p4) → p2)) ∨ False) ∧ (p1 ∨ ((p3 → (p1 ∧ (False ∧ False))) ∨ p2))) ∧ (True ∧ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134509624435884127302968478309 : (((((p4 ∧ p2) → (True → ((((p1 ∧ p1) → p5) ∧ (False → (False ∧ (p2 → (p3 → False))))) → p4))) ∨ p2) → p1) ∨ (p1 → (p2 → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68263074006560332908369014814 : ((p3 → (((p3 → ((p4 → (((p1 → (p1 → (((False ∨ True) → True) ∨ p3))) ∧ p4) ∧ (p1 ∧ p1))) → p2)) ∨ True) ∨ (p3 ∧ False))) ∨ p5) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_216258174097550038239636522112 : ((p1 → (p2 ∨ (False ∨ p3))) ∨ (p5 → (p4 → ((True → ((p2 ∨ p3) ∧ ((False ∧ p4) ∨ (((False ∧ p2) ∨ p2) ∧ p1)))) ∨ (p5 ∧ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_707221234713504331081566225424 : (((((p2 → (p1 ∨ ((p4 → p2) ∧ p2))) → p4) ∨ (((p5 ∧ (p5 ∨ (p2 ∨ False))) ∧ p1) → (((True ∧ True) ∧ p3) → (p4 ∨ p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_216924534533316551281393068552 : (((p5 ∨ (p4 → p5)) ∧ p2) → (((((p3 ∧ False) ∨ ((True ∨ p1) → (True ∧ p1))) ∧ p5) ∨ p2) ∧ ((p4 → p5) ∨ ((True ∧ p5) ∧ p4)))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  -- Conjunctions on the left can always be decomposed.
  let h6 := h1.left
  let h7 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h8 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h9
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h10 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h11
    -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
    have h12 : p4 := by
      -- One of the premise coincides with the conclusion.
      exact h11
    -- We have shown the premise of h10, we can now drive its conclusion.
    let h13 := h10 h12
    -- One of the premise coincides with the conclusion.
    exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51117510473023390589647307409 : (((((((p2 → p3) → False) ∧ (p3 → (p3 → ((p4 ∧ False) ∨ p4)))) ∧ (False ∧ p1)) ∨ p1) ∨ (((p5 ∧ (p4 ∧ True)) → True) ∨ p2)) ∨ p2) := by
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
theorem thm_5_vars_595386519361621727080005866796 : (((((p3 ∨ (p1 → (p1 → (p1 → (((p3 → False) ∨ p3) ∨ p5))))) ∧ ((((p5 ∧ p4) → ((p3 → True) ∧ True)) → p2) ∧ p1)) ∧ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231913996509751052257258699194 : (((False ∨ p1) → p4) → (((p5 → (p1 ∨ (False ∨ False))) ∨ (True ∨ (p4 → p3))) ∧ ((p1 → (p2 ∧ p3)) ∨ (p3 → (True → (False ∨ True)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61023178845198345839062911905 : ((False ∧ ((p5 → (p5 → ((p2 ∧ ((p5 → (p4 → True)) → p2)) → ((((p1 ∧ ((p3 ∨ p4) ∧ True)) → p2) ∧ True) ∨ p1)))) → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150079908005666214269371911191 : ((True → (False ∧ ((p4 ∧ (p2 ∨ True)) ∧ (p3 → (((((False ∧ p2) → False) ∨ p5) → False) ∧ (p5 → p4)))))) ∨ (((p3 → p5) ∨ p3) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114413730854109655184995811941 : ((((p4 ∧ (p2 ∨ p1)) → (p4 → ((((p3 → True) ∧ False) ∧ p1) ∧ (p4 ∧ (False ∧ p3))))) ∨ ((p4 → p2) → (p4 → p4))) ∨ (p2 ∧ p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205451760324191216601125969303 : (((p5 ∨ (p2 ∨ p1)) → (False ∧ p1)) ∨ (p4 → (False ∨ (False → ((p4 ∨ p2) → (((((p5 ∨ (True → p4)) ∧ p4) → p5) ∧ p1) → p1)))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h7 =>
    -- False on the left can always be used.
    apply False.elim h2
  case inr h8 =>
    -- False on the left can always be used.
    apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149492493043069590317702888392 : ((p1 ∧ ((True ∧ ((((False ∨ ((False ∧ p2) ∨ p5)) ∧ p4) ∨ ((p1 ∨ p1) ∧ (True → True))) ∧ False)) ∨ p1)) ∨ ((p2 ∧ (p2 ∧ False)) → p1)) := by
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
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180895162039754919303492357447 : ((((p1 → False) → True) → ((True → (False ∧ ((False ∨ p2) ∨ p1))) ∨ p2)) → (p2 ∨ (p4 ∨ ((False ∧ False) ∧ (((p3 ∨ p1) ∧ p3) ∨ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p1 → False) → True) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h6 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h7 := h5 h6
    -- We need to get the left conjuct of h7 based on <expert-advice>.
    let h8 := h7.left
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174257010178609514615075432437 : ((((p1 ∨ (((p5 ∧ p1) ∨ (False ∧ True)) → False)) ∧ p5) ∧ (p5 ∧ (p2 → p2))) → (((True → False) ∨ ((True ∧ p2) ∨ (True ∨ p4))) ∨ p5)) := by
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
    let h7 := h3.left
    let h8 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h3.left
    let h11 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179431753823962924770368901949 : ((p4 ∨ (p4 ∧ (True ∧ (((p1 ∨ (False ∨ p3)) ∨ False) ∧ (p3 → True))))) ∨ ((((p1 ∧ ((True ∨ (True → p3)) ∨ p3)) → p4) → True) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_383128533290221407025051409492 : (((((False ∨ (p1 ∧ (p5 → (((True ∧ (p1 → ((True → True) ∧ p4))) ∧ (p3 → True)) ∨ ((p2 ∧ (p1 → False)) ∧ p3))))) ∨ False) ∨ True) ∧ True) ∧ True) := by
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
theorem thm_5_vars_137631553772046111620085176456 : ((False ∨ (((p3 ∨ p5) ∨ (((p1 ∧ (((False ∨ False) ∧ p5) ∨ p2)) ∨ p1) ∧ ((p1 ∧ p2) → p3))) ∨ (p2 → p2))) ∨ (p1 → (p1 ∧ p4))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49066311993362572354351100944 : ((((((p1 ∧ False) ∧ p3) ∧ ((p1 ∨ (True → p1)) ∧ (p2 ∨ (p3 ∧ ((p3 → p2) → p1))))) ∨ (False ∨ True)) ∨ (p4 ∧ (p4 ∧ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135793372495330877324728330433 : (((((p2 → p1) → p5) → ((False ∧ (p1 ∨ p4)) ∧ ((p3 ∨ p1) ∨ True))) → (p2 ∨ (p2 ∧ (False ∧ (p1 → p4))))) ∨ (False → (True ∧ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111979965758864761203344134380 : ((((p3 → (((p4 → p5) → p1) ∧ p1)) ∨ ((((((p5 → p3) → p5) ∧ (False ∨ False)) → False) → (p5 → False)) ∨ p3)) ∨ p4) ∨ (True → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_641807183975187909846051546263 : (((((p5 ∨ p5) → (((((True ∧ True) → (p5 → (p4 → p5))) ∧ (False ∧ p1)) → (p5 ∨ (p1 → (p5 → False)))) → (p2 ∧ p4))) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158009622226261615252337531342 : ((((p4 → (p1 ∨ (p3 ∨ p3))) ∧ p3) ∧ (p2 ∧ (p5 ∧ (p4 ∨ ((p2 ∨ (False → p3)) → p4))))) ∨ ((p1 ∨ True) ∧ ((False ∧ p5) → p5))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172361811935260882334214276792 : ((((p5 ∨ (p5 ∨ p3)) ∨ (True ∧ p5)) ∨ ((p5 ∧ (p1 ∧ p5)) ∨ (True → True))) ∨ ((p3 ∧ p4) → (p2 ∨ (((p4 ∧ p4) ∧ p5) ∧ False)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42898529946893145379417385302 : (((p3 → ((p5 ∨ (((p3 ∧ p2) ∨ p3) → ((p2 ∨ (p3 ∧ p5)) → p2))) → (((p4 → True) → ((p5 ∨ p5) ∧ p3)) ∨ True))) ∨ True) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115908671229367590746946261771 : ((((p4 ∧ p3) ∧ (p2 ∧ p3)) ∨ (p2 ∨ (((p1 ∧ (((p2 ∨ p1) ∧ True) ∨ p5)) ∨ (p2 → (p3 → p4))) ∨ (p4 → True)))) ∨ (p4 ∧ p2)) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158518054473673433981225964571 : (((p3 ∨ True) → (False ∧ (p2 ∨ (((p3 ∨ p3) ∧ ((p4 ∧ p3) ∧ p4)) ∨ (p4 ∧ (p5 ∨ p5)))))) ∨ (False → (False ∧ ((True ∧ p5) → p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_718607631219286376733789432389 : (((((p2 ∧ p3) ∧ (p3 ∨ True)) ∨ ((False → (False ∨ ((p3 → ((p4 → p3) → ((p5 ∧ False) ∨ (p5 → False)))) ∨ p5))) → (p3 ∧ True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52124415791358992442381606615 : ((((p5 ∧ (False ∧ (p3 → (p4 ∧ (((False → p1) ∧ p1) → (False ∨ p2)))))) → p1) → (p4 → (p2 ∨ (p1 → ((p4 ∨ p4) ∨ p1))))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_116872093155818978166001659616 : (((p2 → p1) ∨ (False ∧ ((((p5 ∧ p4) ∧ False) ∨ (p2 → p5)) → (p5 ∧ (((True ∧ p5) → False) → ((False → p2) → p5)))))) ∨ (True ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68338636758584252151580583962 : ((p3 → (((((p3 ∨ p3) ∧ p3) ∧ (((p5 ∧ p1) ∨ p5) ∨ p4)) ∧ p2) ∨ (p1 ∨ (((p2 ∧ (p1 → p4)) ∨ (p2 ∨ p3)) → False)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_153276728495883865191255294911 : ((False ∨ (p2 ∨ (((p2 ∧ (False → ((p1 ∧ p3) ∧ (((False → p3) → p1) ∧ False)))) ∨ (p2 → p3)) ∨ p5))) → ((p2 ∨ (False ∧ p2)) ∨ True)) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_87280860706649784809882830993 : (((((True → (False ∧ p1)) → p5) → p4) ∧ ((p1 ∧ ((((p2 ∨ (p1 → p2)) → (p1 ∧ p3)) → p5) ∧ p3)) ∧ ((p3 → p1) ∨ p5))) → p3) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h8 := h7.left
  let h9 := h7.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h10 =>
    -- One of the premise coincides with the conclusion.
    exact h9
  case inr h11 =>
    -- One of the premise coincides with the conclusion.
    exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_654594034710018228752326532349 : (((((True → ((((True ∨ False) ∧ ((True ∨ p3) → False)) ∧ ((p4 ∧ p4) ∧ (True ∨ p1))) ∨ (p1 ∨ (True ∨ p4)))) ∨ p5) ∨ (True → p3)) ∨ p4) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228470094028476166833835265980 : ((False ∨ (p5 ∨ p1)) ∨ ((((True ∨ False) ∧ (((False → True) ∧ (((p5 ∧ p4) ∨ False) ∧ (True → p2))) ∨ (True → True))) → p4) ∨ (True ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43581754346524275902677988940 : ((((((((((p4 → (((p4 → True) ∧ False) ∧ p3)) ∨ p5) → p5) → p5) ∨ (True ∨ (True ∨ True))) ∧ (True → p4)) ∨ p1) → p5) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50288133486740293943011319330 : ((((p4 ∨ (((p1 → (p1 ∧ True)) ∨ False) → (True ∧ ((False ∧ p2) ∨ (p4 → True))))) → (True ∧ p3)) ∨ (p4 → (True ∧ (p2 ∨ p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136136441821890059120389106402 : ((((p5 ∨ (((False ∨ p2) → True) → p2)) ∨ p5) → (True → (((p5 ∧ p4) ∧ (p3 → False)) ∨ ((True ∨ True) → True)))) ∨ ((p3 ∧ p3) → p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h5
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h7
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234029386362713742811449950270 : ((p5 ∨ (True → p5)) → (p2 ∨ ((False ∨ (p3 ∧ ((False ∨ p4) ∧ (p5 ∨ (((False → (p2 → p2)) ∧ p5) → (True ∧ p2)))))) ∨ (p3 → p3)))) := by
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
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112866956197306121516047938786 : (((((p5 ∧ p1) ∧ p2) → (p5 → ((p2 ∧ ((True ∨ ((((p4 → True) → p4) ∧ p1) ∧ (False ∧ p3))) → True)) → p1))) → False) ∨ (True ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135497679601375629403879023670 : (((p2 ∧ (p1 ∨ (((p1 ∧ (p4 ∧ p1)) → ((p3 ∧ True) ∨ (p5 ∧ p4))) → (True → True)))) → (p2 → (p5 ∧ p1))) ∨ ((True ∨ p5) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49136492156806788630403943037 : (((((((True ∧ False) ∧ p5) ∧ (p5 → p5)) ∨ (p5 → p5)) ∧ (((p1 → (p2 ∨ (p2 ∧ p1))) ∧ p4) ∨ p2)) ∨ (p2 ∨ (True → p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52314245537537291795131035357 : (((((False ∨ ((p2 ∧ (False → p4)) ∧ (p5 ∨ (p1 ∨ p1)))) ∨ p2) ∨ True) ∧ ((p4 → ((p3 → ((p4 ∨ True) ∧ True)) → False)) ∨ True)) ∨ False) := by
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
theorem thm_5_vars_40702364989960998241619241390 : (((((p5 ∧ (p5 → (False ∧ (True ∨ (False ∧ (p1 → (False ∧ p3))))))) ∧ (((((True ∨ p2) → False) → p2) ∨ True) ∨ p4)) → False) ∨ p4) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h8 : p5 := by
        -- One of the premise coincides with the conclusion.
        exact h4
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h9 := h5 h8
      -- We need to get the left conjuct of h9 based on <expert-advice>.
      let h10 := h9.left
      -- False on the left can always be used.
      apply False.elim h10
    case inr h11 =>
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h12 : p5 := by
        -- One of the premise coincides with the conclusion.
        exact h4
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h13 := h5 h12
      -- We need to get the left conjuct of h13 based on <expert-advice>.
      let h14 := h13.left
      -- False on the left can always be used.
      apply False.elim h14
  case inr h15 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h16 : p5 := by
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h17 := h5 h16
    -- We need to get the left conjuct of h17 based on <expert-advice>.
    let h18 := h17.left
    -- False on the left can always be used.
    apply False.elim h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_252023610622530423108270732972 : ((p4 → p1) ∨ (((True ∧ ((p4 ∧ (((p2 ∨ True) ∨ p2) → ((p1 ∨ p5) ∨ p5))) ∨ (p2 → p3))) ∨ ((p5 ∨ p2) → (p2 ∨ p5))) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_209573305968914538844213953540 : ((p5 → ((False → p2) ∨ (p3 ∨ True))) → ((((p4 ∧ (p3 ∨ p4)) ∨ (p2 → p5)) ∨ ((p4 ∧ (p4 → False)) → p2)) ∨ (p5 ∧ (p2 → p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h5 : p4 := by
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h6 := h4 h5
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47747134687111661121241024929 : (((((p4 ∨ (p1 ∨ (p3 → p1))) ∧ (((True → ((p2 → p2) → p2)) ∨ p5) ∧ ((p1 ∨ (p5 ∧ True)) ∧ p1))) ∨ p1) → (p1 → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328896896867638773242330217031 : (True → ((p5 ∧ ((((p5 ∨ False) ∨ False) ∧ p3) ∧ p2)) ∨ (p1 → (((False ∧ (p2 ∧ (((p4 → p2) ∨ p4) ∧ False))) ∨ True) ∨ (p3 ∧ p1))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58946461341396931755339422802 : (((p2 ∧ True) ∨ ((((p1 → p5) ∨ ((p3 ∨ (False ∧ (p5 → p2))) ∨ ((((p3 → p1) → p3) ∧ True) ∧ False))) ∧ p2) ∧ (p2 ∧ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_665954756756651762735532222816 : ((((((True ∧ p4) → ((p5 ∧ (((((True ∧ p4) → p2) ∨ True) ∧ False) ∨ (p4 ∨ p5))) → (False ∨ p2))) → p2) ∧ ((False → True) ∧ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_747537844969282674525208351249 : ((((True → p2) → ((p3 ∨ (True ∧ False)) → ((((p1 ∧ (p4 ∧ ((False ∨ p1) ∧ ((p4 ∨ p3) → p5)))) ∧ (True ∧ p5)) → False) → p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112584451847371292827548232181 : (((((True → ((p2 ∨ ((p3 ∧ (False ∧ (False → (p5 ∧ p3)))) → ((p4 → True) → True))) → False)) ∨ False) ∧ (p5 ∨ p3)) → p4) ∨ (p1 ∨ p3)) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h5 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h6 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h7 := h4 h6
      -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
      have h8 : (p2 ∨ ((p3 ∧ (False ∧ (False → (p5 ∧ p3)))) → ((p4 → True) → True))) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h9
        -- Implications on the right can always be decomposed.
        intro h10
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h7, we can now drive its conclusion.
      let h11 := h7 h8
      -- False on the left can always be used.
      apply False.elim h11
    case inr h12 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h13 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h14 := h4 h13
      -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
      have h15 : (p2 ∨ ((p3 ∧ (False ∧ (False → (p5 ∧ p3)))) → ((p4 → True) → True))) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h16
        -- Implications on the right can always be decomposed.
        intro h17
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h14, we can now drive its conclusion.
      let h18 := h14 h15
      -- False on the left can always be used.
      apply False.elim h18
  case inr h19 =>
    -- False on the left can always be used.
    apply False.elim h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136523572684506392519588043218 : (((p4 ∨ (False ∨ True)) ∧ (((((True ∨ p2) → (p1 → ((p3 ∨ p3) ∧ p1))) → False) ∨ (p2 → p2)) ∨ (True ∨ True))) ∨ (True ∧ (False ∧ p5))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_116620702859972431861965127376 : (((False → p3) ∧ ((p2 ∧ (((False ∧ (p2 ∧ p2)) ∨ p2) ∨ (((p1 ∨ p4) ∧ ((True → False) → (p1 ∧ False))) ∨ p4))) ∧ p1)) ∨ (p3 → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_614392432733638448597246083069 : (((((p2 ∨ ((((p1 → ((((p1 ∧ ((p4 ∧ p4) ∨ p5)) → False) → p2) ∨ p2)) ∨ p5) ∨ p3) → p4)) → (p3 ∨ (p2 → p3))) ∨ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_302023650450670848987466183825 : (False ∨ (True ∧ ((p1 → (((p5 ∧ p4) ∨ (((p3 ∧ (p5 → (((False → p5) ∧ p2) → p5))) ∧ p2) ∨ p1)) → (p3 ∧ p3))) ∨ (True ∨ p1)))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66210897518763775716747123406 : ((p5 ∨ ((((True → (p2 ∨ ((p4 → p4) ∨ False))) → False) ∧ (p2 → p2)) ∧ (((p4 ∧ (((p1 → True) → p3) ∧ False)) ∨ False) → p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148855785162907186471193419080 : (((p2 ∧ ((p4 ∧ p2) ∨ p1)) ∧ ((p5 ∧ (((True → p2) ∧ (p3 ∨ False)) → False)) ∧ ((p2 → p1) ∨ p2))) ∨ (p5 → ((p3 ∨ p2) ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149913817705502490909981582453 : ((p3 ∨ ((p5 ∨ ((p3 → p1) → ((((p5 → p4) → (p1 ∧ False)) → True) ∧ ((p1 ∨ p4) ∧ p2)))) ∨ p2)) ∨ (p1 → ((p1 → p1) ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_747362171580894612984556885101 : ((((p5 ∨ p5) → ((p3 ∨ ((((p3 ∧ p4) ∨ ((((p2 → p3) → ((p4 ∨ True) ∧ p1)) → True) ∨ (p4 ∧ p2))) ∨ p3) ∨ True)) ∨ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350089474720432517303631430403 : (p4 → ((((p2 ∧ (p4 → p1)) ∧ (((((p4 → (p3 → p3)) → (p2 ∨ False)) ∧ True) → (p5 ∨ False)) ∨ p1)) ∧ ((p5 → p5) → p1)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37725821061392022862118946655 : (((((((p1 ∧ p3) → (p1 ∧ (True → p1))) ∨ (p5 ∨ (p5 ∨ p4))) ∧ ((((True ∧ (False → p5)) ∨ p4) → p5) ∧ True)) → p4) ∧ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52979233495206722688575334814 : ((((p2 ∨ (p2 → (p2 → ((p1 ∧ (p3 ∧ p2)) ∧ p3)))) → p4) ∧ ((p2 ∨ (((p5 ∧ p1) → p2) → (p1 ∨ p1))) ∧ (True ∧ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_602962160771458047595722453494 : ((((p1 ∨ ((((p5 → (p5 → p4)) → p4) → p1) → ((p1 ∨ (p4 ∧ p5)) ∧ ((((p5 ∨ p1) ∧ (p5 ∧ p2)) → p2) ∨ p3)))) ∧ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345516203576808031475867886010 : (p3 → (((((p1 ∧ ((p5 ∧ p5) → p5)) → (p1 → True)) ∨ (p1 → p1)) ∧ (((True → p4) → ((p4 ∨ (p4 ∨ False)) ∧ p2)) → False)) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_130161994620875793620329250394 : ((((p5 ∨ p1) → (((((((False ∨ p4) ∨ p1) ∧ (False ∨ p3)) ∧ (False ∧ p1)) ∨ p5) ∨ True) ∧ True)) ∨ (p2 ∧ p4)) ∧ (p4 ∨ (False → p1))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177957486985428529345072936152 : ((((p5 → True) ∧ (p3 ∨ ((p4 ∨ p5) → (p5 ∧ (p3 ∨ p5))))) ∨ False) ∨ (p5 → ((False → (p1 ∧ (p2 ∧ ((True → p4) → p2)))) ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_120186027710549474761183242160 : ((((p2 ∨ p5) ∨ ((p4 ∨ p2) ∨ (p2 ∨ (p2 ∨ (p5 ∨ ((p3 ∧ p2) → (((p2 → p5) ∨ False) → (p2 ∧ p4)))))))) ∧ True) → (p4 ∨ True)) := by
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
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h9
      case inr h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
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
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h15 =>
          -- Disjunctions on the left can always be decomposed.
          cases h15
          case inl h16 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h17 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248060407712514488120280677825 : ((p1 ∨ p5) ∨ (p3 ∨ ((True ∧ (((p4 ∧ True) → ((((False ∨ (False → p2)) ∧ True) ∨ False) → p2)) ∨ (p5 → (p4 ∨ p1)))) ∨ (p1 → True)))) := by
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
theorem thm_5_vars_345395461868958605717248385586 : (p3 → (((((((((p5 → p3) ∨ False) → p2) ∧ False) ∨ (p2 ∧ ((p2 ∨ p5) ∨ (True → p1)))) → ((p1 → p1) → p3)) ∨ p5) → p5) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_622249531750793490505443120296 : ((((p2 ∧ (p2 → (p2 ∧ ((((((False ∨ ((p5 ∧ p4) ∨ False)) ∨ p3) ∨ p3) ∨ False) ∨ (p3 ∨ (p4 ∧ (p1 ∨ p3)))) ∧ p5)))) ∨ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245584581373442611128342192838 : ((p3 ∧ False) ∨ ((((((False ∧ p1) → p5) → (p3 → (((p3 → (p4 ∨ p4)) ∨ (p5 ∨ (p4 ∨ p3))) ∨ p5))) ∨ (p5 ∨ True)) ∨ p2) ∨ p4)) := by
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
theorem thm_5_vars_41617850465360140919898586427 : (((((((p3 ∨ p4) ∨ (p5 ∨ p2)) → False) ∧ True) → (((True → ((((p1 ∨ p2) → False) ∧ True) ∧ (p5 ∨ p2))) → p2) ∨ p4)) ∨ True) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249627180669778389351504082225 : ((p5 ∨ p3) ∨ ((True ∧ p3) ∨ ((p5 ∨ (p4 → (((True → (p5 ∨ (p3 ∧ False))) ∨ p4) ∨ p1))) ∨ ((p2 ∧ (True ∧ p2)) → (p4 ∧ p3))))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48568711404370085105056238800 : (((((p2 → True) ∧ ((p1 ∨ (p2 → (True ∧ False))) → ((((p1 → (p5 ∨ p5)) ∨ p1) ∨ True) ∧ p3))) → p3) ∧ ((p1 ∨ True) ∨ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213165133783446275716767976273 : ((((p4 ∧ p2) ∨ p4) ∧ p1) ∨ ((False ∧ p4) ∨ (False ∨ ((p2 ∧ p1) → (((p5 → True) → ((p4 → (True ∧ p1)) → True)) → (p2 ∧ p2)))))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Conjunctions on the left can always be decomposed.
  let h5 := h1.left
  let h6 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39848791014768724517546222737 : (((p1 → ((p4 ∨ (p2 → p2)) ∧ (((False → p2) → (p4 ∧ p4)) ∨ ((True ∨ p2) → (((True ∨ p2) → (False ∨ True)) → True))))) ∧ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323543462589295240078751959295 : (p5 ∨ ((((p4 ∧ p5) ∨ ((p3 ∧ (False ∧ p2)) ∨ (p5 → ((p3 ∧ False) → ((p2 ∨ (p4 → p3)) ∧ False))))) ∨ p1) → (False ∨ (p5 ∨ True)))) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h4 := h3.left
      let h5 := h3.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Conjunctions on the left can always be decomposed.
        let h8 := h7.left
        let h9 := h7.right
        -- Conjunctions on the left can always be decomposed.
        let h10 := h9.left
        let h11 := h9.right
        -- False on the left can always be used.
        apply False.elim h10
      case inr h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h13 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186890615832802235659147327506 : (((p1 ∨ (False ∨ (p2 → p1))) → (((p2 ∧ False) ∨ p5) ∧ p1)) → (((p4 ∧ (p1 ∧ p1)) ∧ (p3 ∨ ((p3 ∧ (p3 → p4)) ∧ True))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191332918933076902328659609066 : (((p4 ∧ True) ∨ (((p1 ∨ (False ∧ p5)) ∧ False) ∨ True)) ∨ (False → (((p2 → p2) → ((p4 → (p1 ∧ (True ∧ p3))) ∧ p1)) → (p1 ∨ True)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179575694882827106197275332149 : ((p2 → (True ∧ ((((p5 → (p1 ∨ p5)) ∨ p5) → (p4 ∧ p5)) → False))) ∨ ((p1 ∨ ((p4 ∧ ((p5 ∨ p5) ∨ True)) ∨ True)) ∨ (False → p2))) := by
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
theorem thm_5_vars_165532272647621427798062293214 : (((True → (((((p3 → p2) ∨ False) → False) ∧ True) ∨ p1)) → ((p4 ∨ False) ∨ (p1 ∧ True))) ∨ (((p1 ∧ False) → p2) ∨ ((p1 ∨ False) ∨ p5))) := by
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
theorem thm_5_vars_708792574531153476802080883611 : (((((p3 ∨ ((p1 ∧ p2) ∧ (False ∨ p2))) → p2) → ((((True → (p5 ∨ False)) ∨ ((((p4 → False) ∧ p1) ∧ p1) → p4)) ∨ p2) ∨ True)) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_636052436704946850843456511554 : (((((p1 ∧ ((p3 ∧ ((p5 → False) → (p3 ∧ (p5 → p3)))) → (False ∨ (p1 ∧ False)))) ∧ ((True ∧ p1) ∧ ((p1 ∧ p3) ∨ p1))) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303967042360153093305646050021 : (p1 ∨ ((((p5 ∧ p5) ∨ p2) ∨ (p1 → ((p2 ∨ ((False ∨ False) → (p1 ∧ (p4 ∨ ((p1 ∨ (False → p3)) ∧ p3))))) ∨ (p3 → p5)))) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- False on the left can always be used.
    apply False.elim h4
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h5 =>
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- False on the left can always be used.
    apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328607490004211808443552832746 : (True → (((p3 ∨ ((p1 ∧ (p5 → (((p4 ∧ p4) → True) ∧ p3))) ∧ p4)) ∨ p5) ∨ ((p4 ∨ (p4 ∨ (False ∨ ((False ∨ p1) ∧ True)))) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_93935914270498478278326834637 : ((p1 ∧ (((p5 ∧ True) → (False ∧ False)) ∧ (p5 ∧ (((p3 ∧ (p1 ∧ (p4 → p1))) ∨ ((p2 ∨ (p3 ∨ p4)) → False)) ∧ (p4 ∨ p1))))) → False) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h8 := h7.left
  let h9 := h7.right
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- Conjunctions on the left can always be decomposed.
    let h13 := h12.left
    let h14 := h12.right
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h15 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h16 : (p5 ∧ True) := by
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h6
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h17 := h4 h16
      -- We need to get the left conjuct of h17 based on <expert-advice>.
      let h18 := h17.left
      -- False on the left can always be used.
      apply False.elim h18
    case inr h19 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h20 : (p5 ∧ True) := by
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h6
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h21 := h4 h20
      -- We need to get the left conjuct of h21 based on <expert-advice>.
      let h22 := h21.left
      -- False on the left can always be used.
      apply False.elim h22
  case inr h23 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h24 =>
      -- We want to use the implication h23 based on <expert-advice>. So we show its premise.
      have h25 : (p2 ∨ (p3 ∨ p4)) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h24
      -- We have shown the premise of h23, we can now drive its conclusion.
      let h26 := h23 h25
      -- False on the left can always be used.
      apply False.elim h26
    case inr h27 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h28 : (p5 ∧ True) := by
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h6
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h29 := h4 h28
      -- We need to get the left conjuct of h29 based on <expert-advice>.
      let h30 := h29.left
      -- False on the left can always be used.
      apply False.elim h30



