variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_241866053704574011063593204494 : ((p1 → p1) ∧ (p3 ∨ (((p3 ∨ (True → (True → ((p5 → (False ∨ (p4 ∨ (p5 ∧ True)))) → p5)))) ∨ p3) ∨ (p2 ∨ ((p3 → p3) ∨ True))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
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
theorem thm_5_vars_688928012726493746088975407497 : (((((p3 ∧ (True → ((((True → (p2 → True)) ∧ False) ∨ p4) → (p4 ∨ False)))) ∧ p2) ∨ ((p2 → ((p2 → (False ∨ p2)) ∨ p1)) → p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_792891134700953365284930182740 : (((True → ((p2 ∨ (p2 → p4)) → ((((((p5 → (p2 → False)) ∨ p4) ∨ (p1 ∧ False)) → (p4 → p5)) ∧ p2) → (p3 ∨ (p4 ∨ True))))) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55405310247259650480567201081 : ((((((p2 → p3) ∨ p4) ∨ p3) ∨ False) → (((p2 ∧ (p1 → p4)) → ((False ∨ (p4 ∨ p3)) ∨ (p3 ∧ ((True ∧ True) → False)))) ∨ p2)) ∨ False) := by
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
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h5
        -- Conjunctions on the left can always be decomposed.
        let h6 := h5.left
        let h7 := h5.right
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
        have h8 : p2 := by
          -- One of the premise coincides with the conclusion.
          exact h6
        -- We have shown the premise of h4, we can now drive its conclusion.
        let h9 := h4 h8
        -- One of the premise coincides with the conclusion.
        exact h9
      case inr h10 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h11
        -- Conjunctions on the left can always be decomposed.
        let h12 := h11.left
        let h13 := h11.right
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h10
    case inr h14 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h15
      -- Conjunctions on the left can always be decomposed.
      let h16 := h15.left
      let h17 := h15.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h14
  case inr h18 =>
    -- False on the left can always be used.
    apply False.elim h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319905226646514733935233732027 : (p4 ∨ ((((True ∨ p1) → False) ∨ p5) → (p4 ∨ ((((True → p3) ∧ ((False → False) → True)) ∨ (p2 ∧ p5)) → (((False ∧ p1) ∨ p3) ∨ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h3 : (True ∨ p1) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h4 := h2 h3
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
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
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_657365343698056483429898670775 : (((((p5 ∨ True) ∧ ((p4 ∨ False) ∨ ((p1 → (p4 → True)) → ((True ∧ (True → (p2 ∧ (p3 ∧ (p1 ∧ p3))))) → p1)))) ∨ (False → p2)) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_149991686461445287685573020471 : ((p4 ∨ (p1 ∨ (p5 ∧ ((False ∨ (False → (p4 ∨ (p5 ∨ ((False ∧ (p3 ∧ False)) → (False ∧ p4)))))) → p2)))) ∨ ((False ∨ (p5 ∧ p2)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207893333278116841468086359580 : ((((p4 → True) → p4) ∧ (p1 → True)) → (((((True → (((p5 ∨ True) ∧ (False → p3)) → True)) ∨ p5) ∨ (p4 ∨ p4)) → (p1 → p4)) ∧ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
      -- Conjunctions on the left can always be decomposed.
      let h6 := h1.left
      let h7 := h1.right
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h8 : (p4 → True) := by
        -- Implications on the right can always be decomposed.
        intro h9
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h10 := h6 h8
      -- One of the premise coincides with the conclusion.
      exact h10
    case inr h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h1.left
      let h13 := h1.right
      -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
      have h14 : (p4 → True) := by
        -- Implications on the right can always be decomposed.
        intro h15
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h12, we can now drive its conclusion.
      let h16 := h12 h14
      -- One of the premise coincides with the conclusion.
      exact h16
  case inr h17 =>
    -- Disjunctions on the left can always be decomposed.
    cases h17
    case inl h18 =>
      -- Conjunctions on the left can always be decomposed.
      let h19 := h1.left
      let h20 := h1.right
      -- One of the premise coincides with the conclusion.
      exact h18
    case inr h21 =>
      -- Conjunctions on the left can always be decomposed.
      let h22 := h1.left
      let h23 := h1.right
      -- One of the premise coincides with the conclusion.
      exact h21
  -- Conjunctions on the left can always be decomposed.
  let h24 := h1.left
  let h25 := h1.right
  -- We want to use the implication h24 based on <expert-advice>. So we show its premise.
  have h26 : (p4 → True) := by
    -- Implications on the right can always be decomposed.
    intro h27
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h24, we can now drive its conclusion.
  let h28 := h24 h26
  -- One of the premise coincides with the conclusion.
  exact h28



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37485330859015615767543293739 : (((((p1 → (False ∨ (p4 → p1))) → (p2 ∨ ((((p4 ∧ p5) → True) → (p3 → (p3 ∨ p4))) → ((p1 ∨ p5) ∨ p2)))) ∨ True) ∧ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115214524918236675820006112897 : (((p4 ∨ ((p2 → p3) → (False ∧ ((p3 ∧ True) → p3)))) ∧ (((True ∨ ((p1 → False) ∨ True)) ∧ True) ∨ ((p1 → p2) ∨ p5))) ∨ (p1 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_83523115907743829037718414763 : (((((((p3 ∨ p5) ∨ (((p5 ∧ (p3 → p2)) ∨ False) ∨ True)) ∨ p1) → False) ∧ (True → True)) ∨ ((p3 ∧ ((p3 ∨ p1) → p2)) ∧ True)) → p2) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h5 : (((p3 ∨ p5) ∨ (((p5 ∧ (p3 → p2)) ∨ False) ∨ True)) ∨ p1) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h6 := h3 h5
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h8.left
    let h11 := h8.right
    -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
    have h12 : (p3 ∨ p1) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h10
    -- We have shown the premise of h11, we can now drive its conclusion.
    let h13 := h11 h12
    -- One of the premise coincides with the conclusion.
    exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_780578033565932760041707610899 : (((p2 ∨ ((((True ∨ p4) → (False → p1)) ∧ ((p3 → p2) → True)) ∧ ((p2 → (((p5 ∧ (p1 ∧ False)) ∨ p2) ∧ (p1 ∨ p2))) → p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228759788998027407429103777587 : ((p3 ∨ (False ∧ p4)) ∨ (p1 → ((p5 → p2) → ((p4 ∨ (False → p2)) ∧ ((False → (p3 ∧ (True ∧ ((True ∨ False) ∨ p4)))) → (p2 → p2)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134138425992530248111338004266 : ((((p4 ∧ ((p3 ∨ p3) → (((p4 ∧ ((p3 ∨ p3) ∧ (p5 → p1))) → (p4 ∨ p1)) ∧ p5))) → (p5 → p3)) ∨ True) ∨ ((False ∧ p5) → False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_734433060828034919894379066279 : ((((False ∨ p5) ∧ ((p1 ∨ p5) → ((True ∧ (((p2 → p4) → ((p2 → p5) ∧ True)) ∨ (((p4 → p5) → (p5 ∨ p5)) ∨ p1))) ∨ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53491510808725690570217628595 : (((p5 ∧ (False → (p2 ∨ ((p4 ∧ False) → (p3 ∨ (p5 ∨ p5)))))) → (p1 ∧ (p1 → (p1 ∨ (((p2 ∨ p5) ∧ False) ∨ (True ∨ p1)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198877146404041776590942287075 : ((p2 → (p3 ∧ (p3 ∧ ((p1 ∧ True) ∨ p2)))) ∨ ((((p3 ∨ p4) ∧ (p4 ∨ (p1 → p2))) → p2) ∨ (False → (False ∨ (False ∨ (p2 ∧ p5)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_689882808376366722969749670640 : (((((p5 → p2) ∨ (p1 ∧ ((p4 → (p3 ∨ p5)) ∧ ((p5 → False) ∧ (p1 ∧ False))))) ∨ (p1 ∨ (p3 → (((p4 ∧ p2) ∨ False) → True)))) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_309404051048674432898003960149 : (p2 ∨ ((True → (p1 → (((p4 ∧ p2) ∧ ((False ∧ (True ∧ ((p2 → (p4 ∧ p2)) ∨ p3))) ∨ p2)) ∨ (p3 → (True ∨ p3))))) ∨ (p1 ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48995774417362407702513479025 : ((((False ∨ ((p5 ∨ p4) ∨ ((p3 ∨ p3) → ((p3 ∨ ((p5 → p1) ∨ False)) ∧ ((True → p5) ∧ False))))) ∨ p3) ∨ (True ∨ (p3 ∧ False))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193236981757095908757234659203 : ((((p5 → p4) ∨ False) ∧ ((True ∨ (True → False)) → p5)) → (((False ∨ ((p3 → p2) → p1)) → (p1 ∨ p4)) ∨ ((p1 → (True → p3)) ∧ p2))) := by
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
    -- Implications on the right can always be decomposed.
    intro h5
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- False on the left can always be used.
      apply False.elim h6
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h8 : (True ∨ (True → False)) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h9 := h3 h8
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h10 : p5 := by
        -- One of the premise coincides with the conclusion.
        exact h9
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h11 := h4 h10
      -- One of the premise coincides with the conclusion.
      exact h11
  case inr h12 =>
    -- False on the left can always be used.
    apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305488837301370714513103501169 : (p1 ∨ (((False ∧ ((p5 → False) ∧ (True → ((p1 ∧ p4) → (p5 ∨ p3))))) ∧ p5) ∨ ((p1 ∨ (p3 → (True ∨ ((p5 ∨ p5) ∧ p3)))) ∨ p4))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63927229287704043327798794498 : ((False ∨ (((True → ((((p3 ∨ (p1 ∨ p5)) ∧ True) → (True → (((False ∨ p3) → (p4 → p4)) → False))) ∧ (p3 → True))) ∨ p4) ∨ True)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_120096378212703685719415724414 : ((((True → (p4 ∨ (p4 ∨ p5))) ∧ ((((p4 → (p5 → ((True → p4) ∧ p1))) → (p2 ∧ False)) ∧ (p4 → False)) ∧ p2)) ∧ p1) → (p4 ∨ p3)) := by
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
  -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
  have h10 : (p4 → (p5 → ((True → p4) ∧ p1))) := by
    -- Implications on the right can always be decomposed.
    intro h11
    -- Implications on the right can always be decomposed.
    intro h12
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h13
    -- One of the premise coincides with the conclusion.
    exact h11
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h8, we can now drive its conclusion.
  let h14 := h8 h10
  -- We need to get the right conjuct of h14 based on <expert-advice>.
  let h15 := h14.right
  -- False on the left can always be used.
  apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336084707068528119647874006008 : (p1 → ((((p5 → (((p2 ∧ (p4 ∨ (p5 → (p2 → p1)))) ∨ p1) ∧ p4)) → ((p5 → ((p2 ∧ (p4 ∧ False)) ∨ p1)) → p4)) ∧ p5) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62612240922750098015638795768 : ((p4 ∧ (((False ∨ ((p3 ∧ ((p4 → p5) → (((p5 → (True ∧ (p4 → p4))) → (True ∧ p1)) ∨ (False ∨ p4)))) ∨ p4)) ∨ p1) ∧ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180020930494216402429756747074 : (((True ∧ ((p4 → p4) → (p1 ∧ (False ∧ (False → (True → p1)))))) ∨ False) → (p3 ∨ (((p5 → p3) ∧ p4) → (((False ∨ False) ∧ p1) ∧ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h5 : (p4 → p4) := by
      -- Implications on the right can always be decomposed.
      intro h6
      -- One of the premise coincides with the conclusion.
      exact h6
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h7 := h4 h5
    -- We need to get the right conjuct of h7 based on <expert-advice>.
    let h8 := h7.right
    -- We need to get the left conjuct of h8 based on <expert-advice>.
    let h9 := h8.left
    -- False on the left can always be used.
    apply False.elim h9
  case inr h10 =>
    -- False on the left can always be used.
    apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_163509040985365093280267186734 : (((p3 ∨ (p4 ∧ True)) ∨ (p5 → (p4 ∨ (((p1 → (p2 ∧ p1)) ∧ p3) → (p3 ∧ p3))))) ∧ ((((False ∨ p5) → (p4 ∧ False)) → p5) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h2.left
  let h6 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h6
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_229483920601362376175916159165 : ((p2 → (p3 ∧ p3)) ∨ ((p3 ∧ (False ∧ ((((p4 → (p2 ∧ (p3 → (False ∧ (p3 ∧ False))))) → p4) ∧ p4) ∧ True))) ∨ ((p2 → True) ∨ p2))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249318235911268449582857294757 : ((p4 ∨ p5) ∨ (((p5 ∧ p1) ∧ (p3 ∧ p2)) ∨ (p3 ∨ ((((True → ((p4 ∧ p2) → (p2 ∨ p5))) ∨ (p5 ∧ p4)) ∧ (p4 ∧ p3)) → p4)))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h3.left
    let h6 := h3.right
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h3.left
    let h11 := h3.right
    -- One of the premise coincides with the conclusion.
    exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64255274951553570475680433705 : ((False ∨ (p3 ∨ (p4 → (p5 → ((((p4 → (((p3 → (True ∧ p5)) ∨ (False → p1)) → ((p5 ∧ p3) ∨ p1))) ∧ True) ∧ p4) ∨ True))))) ∨ p3) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_8089619955562388586015270591 : ((((((p2 → (p5 → True)) ∨ (False ∨ False)) → ((p5 ∨ (p2 → ((True ∧ False) ∨ (p1 ∨ p5)))) ∨ (p5 ∨ (p2 ∨ p5)))) ∨ True) ∨ False) ∧ True) := by
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
theorem thm_5_vars_40254453977265762866723005040 : ((((p1 ∨ ((p2 → (((False ∨ p2) ∨ (p2 ∧ (p4 ∨ p2))) ∨ ((False ∧ (p1 → (p4 → p2))) ∧ p2))) → (p4 ∧ p5))) ∧ p1) ∨ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53752321918344029490909166775 : ((((((p5 → (p2 → p5)) ∨ p1) ∨ (p1 → p3)) ∧ False) ∨ ((p3 ∧ (p4 ∧ ((p3 → p4) ∨ (p4 → True)))) ∧ (p1 ∧ (p1 → p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113374683684958392859480460058 : (((p2 ∨ ((p4 ∨ (False ∨ p5)) ∧ (((p2 → (p1 ∧ (p2 → ((p1 ∧ p2) → p3)))) ∧ p1) ∨ (p3 → p3)))) ∧ (p3 → p2)) ∨ (p2 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157563820047322655014730822273 : (((((False → p4) → (((True ∧ False) ∧ True) ∧ p5)) → (((p3 → p5) ∧ p4) ∨ p5)) → (p1 → p4)) ∨ (((p5 ∨ p1) ∧ (p4 ∧ p4)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67850603167293268195797869391 : ((p2 → (((True ∨ (p1 ∧ (p5 ∧ (((p2 ∨ p4) ∨ (p4 → (((p2 ∧ p5) → False) → False))) ∧ p5)))) ∨ (p1 ∨ p5)) → (p4 ∨ True))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h12 =>
        -- Disjunctions on the left can always be decomposed.
        cases h12
        case inl h13 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h14 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h14
      case inr h15 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h16 =>
    -- Disjunctions on the left can always be decomposed.
    cases h16
    case inl h17 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h18 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_613230732878100518635691879943 : ((((((p4 ∧ ((((False → (p1 ∨ p3)) → p1) → p3) ∧ (p3 → p1))) ∨ (False → (p1 → (p2 → (p3 ∧ p1))))) → (p1 ∨ p2)) ∨ True) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_65330943175384824570647239008 : ((p3 ∨ (((((((p5 ∧ (p5 ∧ (p3 → (p4 → True)))) → p4) ∨ (False → p3)) → False) ∨ p5) ∨ p4) ∨ (p3 ∧ (p2 → (p2 ∧ p4))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42145196312168718751338315873 : ((((True → True) → (((p3 ∧ (p4 → p3)) → ((False ∧ (p2 → (p2 ∨ (p2 ∨ p3)))) ∧ ((p4 → (p2 → p1)) ∨ p1))) ∨ False)) ∨ True) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_330732925909575623754603977241 : (True → (p1 → (((((p3 ∨ (True ∨ p1)) → p3) → (p5 → p5)) ∧ ((((p4 → p4) → p4) ∧ ((p4 → p2) ∨ p5)) ∨ p5)) ∨ (p4 ∨ p1)))) := by
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
theorem thm_5_vars_178069525981077361969001397571 : ((((True ∧ ((p1 ∨ (((p5 → p2) ∨ False) ∧ p4)) ∨ p4)) ∨ p5) → p1) ∨ ((True ∧ True) ∨ ((p4 ∨ (p3 → p1)) → ((p4 ∨ False) ∧ p4)))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_241287221977913323228758302342 : ((False → True) ∧ ((((((p4 ∨ True) ∨ True) ∨ ((p3 → p3) ∧ p4)) → p3) ∧ (((p5 ∨ (p4 ∧ (p5 ∨ p2))) ∨ True) → p1)) → (p3 ∨ p4))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h5 : (((p4 ∨ True) ∨ True) ∨ ((p3 → p3) ∧ p4)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h5
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_616976675144751461433115155717 : ((((((((p4 ∧ p2) → (p5 ∨ p4)) → p4) ∧ False) ∧ ((p3 → ((p2 → (((p2 ∧ p3) ∨ p4) ∨ (p2 ∧ p2))) ∧ False)) → p3)) ∨ True) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_115635915535770841650396854128 : (((((p5 ∨ (p2 ∧ p2)) ∨ False) ∨ p1) ∨ (((p5 ∧ ((p5 ∨ (p4 ∨ p5)) → p4)) → True) ∨ (p5 ∨ ((p2 → True) ∧ p4)))) ∨ (p2 → False)) := by
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
theorem thm_5_vars_778387682107375530054456683308 : (((p1 ∨ (p2 ∧ ((p3 ∨ ((p2 ∨ (p2 → ((p2 ∨ True) ∧ p5))) → (((p4 ∧ True) ∨ p2) → (p4 → p1)))) ∨ ((p4 ∨ p2) → True)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198694674749943397981786092601 : ((p4 ∨ (p3 ∨ (False ∧ ((p3 ∧ p1) ∧ p4)))) ∨ (False ∨ (p4 ∨ ((False ∧ (False → ((p5 → (p3 → (False → True))) → False))) ∨ (False → p2))))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324487893083987214083060695883 : (p5 ∨ ((((p1 ∨ p2) → p5) → p2) ∨ (True ∨ (((((p2 ∧ p2) → p4) ∧ p3) → True) ∨ ((((p4 → (p5 ∨ False)) → True) → True) ∧ p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219733501877907776569146535101 : ((p1 → (p4 ∨ (True → p5))) → ((p4 → (p1 ∧ (((((p4 ∧ p1) ∧ p4) ∧ p5) → False) ∧ (p4 ∧ p1)))) ∨ (False ∨ ((False → p1) → True)))) := by
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
theorem thm_5_vars_66302425577652003387421793866 : ((p5 ∨ ((True ∧ True) → (((p3 → p5) ∨ ((p5 ∧ (False ∨ (p1 → (p3 ∨ p2)))) ∧ p3)) ∨ (p5 → (((p1 ∧ p1) ∧ p2) ∧ p4))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65359784421462596397274660487 : ((p3 ∨ ((((p4 ∧ ((p4 → (True ∨ (p3 ∨ p3))) → p2)) ∨ p1) ∧ p1) ∧ (p3 → (p5 ∧ ((p1 ∨ (p5 ∧ p5)) ∧ (p5 ∧ False)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44344025122491249603087769500 : (((((p4 ∨ ((p1 → p5) ∧ p4)) ∨ (False ∨ (p2 ∧ (((True → p2) ∧ True) ∧ p5)))) → (False → ((p3 ∧ (False ∨ p4)) ∨ p2))) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_807054505272302185486314015695 : (((p4 → (((p3 → ((p2 ∨ ((p5 ∧ (p1 ∧ False)) → False)) → ((False ∨ p4) ∨ (p5 ∨ p2)))) ∧ False) ∧ (False ∨ (False ∧ (False → p3))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44369991364953189431575399194 : (((((p1 ∨ True) ∨ (((p5 ∧ p4) ∨ (p5 → p1)) ∧ (p3 ∨ (p5 → p2)))) ∧ ((((p2 ∧ (p1 ∨ p4)) ∨ False) ∧ True) → p4)) → p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309828908143107289646531447243 : (p2 ∨ (((((((((True ∧ False) → (p3 ∧ p5)) → ((p3 ∨ p1) ∧ p3)) → p2) → p1) → p5) → p4) ∨ p3) → (p4 → (p4 ∨ (False ∨ p1))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314012940321743596190115164054 : (p3 ∨ ((p4 ∧ (p1 → (p4 → (((p2 ∨ (p2 ∨ p3)) ∨ ((False ∨ True) ∧ (((True → (p4 → p2)) → p3) ∧ False))) ∨ p1)))) ∨ (p1 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158345407194352420904653505112 : (((p4 ∧ False) ∧ ((p4 ∨ p3) ∧ ((((True ∨ p1) → ((p5 ∧ p1) ∧ p2)) ∧ False) ∨ (p1 ∨ p1)))) ∨ (p1 → ((p5 ∨ True) ∨ (p3 ∨ True)))) := by
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
theorem thm_5_vars_113536738478698164157038602189 : (((((False ∧ p2) ∧ (False → p5)) ∧ ((p2 → ((p2 ∧ (p4 ∧ ((p5 ∨ p4) → p4))) ∧ (p4 ∧ p1))) ∨ p4)) ∨ (p3 ∨ p3)) ∨ (p1 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47121542025214455245288312578 : ((((p5 → (True → (((((False ∧ p5) ∧ (p3 ∧ True)) → (p5 ∨ p4)) → (False → True)) → False))) ∨ ((p5 → p4) ∧ p1)) ∨ (False → p3)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168697178034950351578209254514 : ((True ∨ (((p3 ∨ ((p5 ∨ p1) ∨ (p4 → True))) → ((p1 ∧ (p3 → True)) ∧ False)) ∧ p1)) → (((p5 ∧ (p2 ∧ p4)) ∧ True) ∨ (p5 → p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_196921222050404940585121738260 : (((((False ∧ p1) ∨ (True ∧ p1)) ∧ p4) ∨ p4) ∨ ((True ∨ p2) ∧ ((((p2 ∧ p5) ∧ (False ∨ p1)) → ((p2 ∧ True) ∧ (p5 ∨ p3))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134095602730495704151680024855 : ((((True ∨ ((True ∨ (p2 → (p3 ∧ (True → (p4 ∨ ((False ∧ p3) → p5)))))) ∧ (p2 ∧ (p5 ∨ False)))) → False) ∨ p1) ∨ ((False ∨ True) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301961841399977349375048117077 : (False ∨ ((p5 ∨ p2) → (p2 ∨ ((((p3 → (p3 ∧ False)) ∨ (((p3 → p5) → p3) ∧ p1)) ∨ (True ∨ ((p3 → p4) ∨ (p1 ∨ p3)))) ∧ True)))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_792877553445432663672935530108 : (((True → (((True → p1) → True) → ((((p4 ∨ (False → p2)) ∨ p4) ∧ (True ∨ p4)) ∧ ((p5 ∨ (p1 → p4)) ∨ ((p1 ∧ p4) → p4))))) ∨ p2) ∧ True) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- One of the premise coincides with the conclusion.
  exact h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40939805236437998887855217798 : (((((p4 → ((((p3 ∧ (((p2 ∨ False) ∧ p1) → True)) ∧ p2) → False) ∨ ((p2 ∨ (p2 → p5)) ∨ True))) ∨ True) ∨ (p4 ∧ p3)) ∨ p1) ∨ p4) := by
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
theorem thm_5_vars_134346409351095037035437575724 : (((p5 ∧ ((p4 → p4) ∧ ((((((p3 → p5) ∨ ((p4 ∧ p5) ∨ p2)) ∧ p1) ∨ (p1 ∨ p4)) ∨ False) ∨ p5))) ∨ False) ∨ (True ∨ (True ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190154475077605377094304694630 : ((((True → p4) → (False ∨ ((p4 → p1) ∨ False))) ∧ False) ∨ ((False → ((p2 ∧ ((p1 ∨ True) ∧ p5)) ∧ False)) ∨ ((p4 ∨ p4) ∨ (True ∧ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_634199206980737574354124731764 : (((((True ∧ (((((((((False ∨ p4) ∨ p5) ∧ p1) ∧ (True ∨ False)) → (True ∨ True)) ∧ True) ∨ False) ∧ p4) ∧ p3)) → (p1 ∨ p5)) → p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213384547870336122912376407901 : (((True ∨ (False → p4)) ∧ p5) ∨ ((p1 ∧ (((((p3 ∧ True) ∨ (p2 ∨ (p3 ∨ p3))) ∧ (p1 ∧ p5)) → p4) → ((p3 ∧ False) ∨ False))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119209481896592727950930417343 : ((p2 → (((((p1 ∧ False) ∨ (p1 → p3)) ∧ (p1 ∧ p3)) ∨ False) ∨ (((((p5 → True) ∧ p3) → p4) ∨ True) ∨ (p4 → p2)))) ∨ (p4 ∧ True)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53362237315678319621122005518 : (((((p3 ∧ p4) ∧ ((p4 ∨ (p2 ∨ (True ∨ False))) ∧ p5)) ∨ p1) → ((((p2 ∧ True) ∧ ((p2 → p5) ∧ False)) ∧ p1) ∨ (True ∨ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51976946191256449571044372613 : ((((p4 ∧ p1) ∧ (((((p3 ∧ ((p4 ∨ p1) → True)) ∧ p1) → p1) → p2) ∨ p5)) ∨ (p1 → (p4 ∧ (p3 ∨ (p2 → (False ∧ p2)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193487266267734342787494965653 : (((False ∨ p1) ∨ ((p1 ∨ p4) ∨ (p4 → (p4 → p2)))) → (((((p4 → False) ∧ p3) ∧ True) ∨ (p5 → p5)) ∨ (True ∨ ((p3 → False) ∧ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
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
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
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
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234566091595838837550825411740 : ((p3 → (p4 ∧ p1)) → (p4 → ((p1 → ((p1 → False) ∧ True)) ∨ ((p4 ∧ p3) ∨ (p2 → ((p3 ∨ False) ∨ ((p3 ∨ p2) → (False → p3)))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147547031094352211620330269485 : (((p4 → (((p3 ∨ (((p2 ∧ (p4 ∧ (p4 ∧ p2))) ∨ ((p4 ∧ False) ∧ p1)) ∧ False)) → p5) → p1)) ∨ p1) ∨ ((True ∨ (p4 → p5)) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_151773938734836281742922454814 : (((((p3 ∨ p2) ∨ p5) ∨ (True ∨ (p5 ∨ (((p2 → (False ∧ False)) ∧ p1) → True)))) → ((False ∧ p4) ∧ p5)) → ((False ∧ (p2 → p4)) ∧ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p3 ∨ p2) ∨ p5) ∨ (True ∨ (p5 ∨ (((p2 → (False ∧ False)) ∧ p1) → True)))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the left conjuct of h3 based on <expert-advice>.
  let h4 := h3.left
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- False on the left can always be used.
  apply False.elim h5
  -- Implications on the right can always be decomposed.
  intro h6
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h7 : (((p3 ∨ p2) ∨ p5) ∨ (True ∨ (p5 ∨ (((p2 → (False ∧ False)) ∧ p1) → True)))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
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
  -- One of the premise coincides with the conclusion.
  exact h10
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h11 : (((p3 ∨ p2) ∨ p5) ∨ (True ∨ (p5 ∨ (((p2 → (False ∧ False)) ∧ p1) → True)))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h12 := h1 h11
  -- We need to get the left conjuct of h12 based on <expert-advice>.
  let h13 := h12.left
  -- We need to get the left conjuct of h13 based on <expert-advice>.
  let h14 := h13.left
  -- False on the left can always be used.
  apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260924960107185959545289881726 : ((p4 → False) → ((True ∨ True) → ((p2 ∨ (False ∧ p1)) ∨ (p5 → ((False → (False ∨ p3)) ∧ ((p2 ∨ False) ∨ (((False → p5) ∨ True) → p5))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
    -- Implications on the right can always be decomposed.
    intro h5
    -- False on the left can always be used.
    apply False.elim h5
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h8 =>
      -- One of the premise coincides with the conclusion.
      exact h4
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h10
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h11
    -- False on the left can always be used.
    apply False.elim h11
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h12
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h13 =>
      -- One of the premise coincides with the conclusion.
      exact h10
    case inr h14 =>
      -- One of the premise coincides with the conclusion.
      exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260477157529904472165218518930 : ((p3 → False) → ((((p4 ∨ True) → ((((p4 ∨ (p2 → ((True ∧ False) → (p4 ∧ p4)))) ∧ p3) → p2) ∧ (p4 → p5))) ∧ p4) → (p5 ∧ p5))) := by
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
  have h5 : (p4 ∨ True) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h5
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
  have h8 : p4 := by
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h7, we can now drive its conclusion.
  let h9 := h7 h8
  -- One of the premise coincides with the conclusion.
  exact h9
  -- Conjunctions on the left can always be decomposed.
  let h10 := h2.left
  let h11 := h2.right
  -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
  have h12 : (p4 ∨ True) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h11
  -- We have shown the premise of h10, we can now drive its conclusion.
  let h13 := h10 h12
  -- We need to get the right conjuct of h13 based on <expert-advice>.
  let h14 := h13.right
  -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
  have h15 : p4 := by
    -- One of the premise coincides with the conclusion.
    exact h11
  -- We have shown the premise of h14, we can now drive its conclusion.
  let h16 := h14 h15
  -- One of the premise coincides with the conclusion.
  exact h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_716238960380604549389311895896 : (((((p5 ∨ (False → p1)) → True) ∧ ((p4 → ((p2 ∨ p3) → (p2 ∨ (True ∧ (p1 ∧ (((p5 ∨ (p4 ∧ p3)) ∧ p1) → False)))))) ∨ True)) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115710761017122858596990168724 : ((((((p1 ∨ True) ∧ p2) ∨ p1) ∨ p4) → ((p4 ∨ ((((p5 → (p5 ∧ True)) ∧ ((p1 → p3) → p5)) ∨ p5) ∧ True)) ∧ p4)) ∨ (True ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_667470000084302506916064743860 : ((((True ∧ (((p1 → p1) ∨ (((p4 ∧ (False → (p5 ∨ (True → p3)))) ∨ ((p3 ∧ p1) → p4)) ∧ p3)) → False)) ∧ ((p5 ∨ p2) ∧ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_241716561280104070162316738011 : ((p1 → True) ∧ ((((False → p5) ∧ (p4 ∨ (False ∧ (((((p1 ∨ p1) → p5) → False) ∧ True) ∨ p1)))) ∨ True) ∨ (p4 → (p3 → (p4 ∨ True))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313349282890650780124856821568 : (p3 ∨ ((p1 → (((p2 ∨ (((True → (p3 ∨ (False ∧ (p2 ∨ True)))) → (p1 ∨ True)) ∧ (False ∨ True))) ∨ p2) ∧ ((p4 ∧ p4) ∨ p5))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248455393652621553893842183111 : ((p2 ∨ p5) ∨ (((p4 ∧ (((((False → True) ∨ (p5 → p3)) → (p3 ∨ p1)) ∧ p2) → p3)) ∨ ((p5 ∨ p3) ∨ p2)) ∨ (p4 → (True ∨ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_675722642774702358948095191348 : ((((((p5 ∧ p3) ∨ ((p2 → ((p4 → (p1 ∧ (True ∨ p2))) → p1)) ∨ p5)) ∧ ((p3 → False) ∨ p1)) ∧ ((True ∧ (False → p5)) → p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_343474081149419917786954364403 : (p2 → ((p2 → p3) ∨ ((((((p5 ∨ False) → p3) ∨ p3) ∨ (((p4 ∧ p3) ∨ (p3 → False)) ∨ (p3 → p5))) ∨ True) ∧ (p2 ∨ (p4 → False))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115918462733937749161560062522 : ((((p2 → p3) ∨ (p3 ∧ p5)) ∨ (((p3 ∧ ((((p5 ∧ (p3 → p1)) ∨ p2) ∨ False) ∨ p1)) ∨ ((False ∨ p5) ∧ p4)) ∨ True)) ∨ (False ∨ p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_725851708110143254054640391502 : (((((True → p1) ∧ True) ∨ (((((True ∨ p5) ∨ p1) ∧ (p1 ∨ p5)) → (False ∨ (p2 ∧ (((p5 ∨ p3) → (True → p1)) ∧ False)))) ∧ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158754194355235501797309293115 : ((p4 ∧ ((((False ∧ p3) ∨ p4) → (p2 → (True ∨ ((p5 → (p4 → p3)) ∨ p1)))) → (p4 ∧ False))) ∨ ((p1 ∧ ((p3 ∧ p4) → p4)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51656387846481507185604687774 : (((((p2 ∨ (p5 ∨ ((((p3 ∧ (False → p3)) ∨ p5) → p3) ∨ False))) ∨ p4) → p1) ∧ (((p2 → p3) ∧ (False ∧ (True ∨ p4))) ∨ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165313503890471027623605846955 : (((p3 ∨ ((False ∧ ((p1 ∨ p4) → (p2 ∨ (False ∧ p3)))) → (p5 ∧ p1))) → (False ∧ p1)) ∨ (((p3 ∨ (p5 ∨ p4)) → p1) → (p1 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64871831681323835173155864308 : ((p2 ∨ ((((False → (p4 → p1)) ∨ (((p2 ∨ (p1 ∨ (p1 → (p1 ∧ (False → (p2 → p5)))))) → p5) ∨ p3)) ∧ p3) → (p5 ∨ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115160469624109228080238769292 : ((((((p3 ∨ ((p2 → p1) ∧ p2)) → p5) ∨ False) ∧ p4) ∧ (p5 → (((p2 ∧ (p1 → p5)) ∨ True) ∨ (p1 ∧ (p2 ∨ p5))))) ∨ (p2 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56681344216095843864609790073 : ((((p4 → True) ∧ True) ∧ ((p5 ∨ (p5 ∨ ((p3 → p2) ∧ (p2 → ((p1 → True) ∧ p4))))) ∨ (((True → p2) ∨ p3) ∨ (p5 ∨ True)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244510350292143297239967825736 : ((False ∧ p3) ∨ (((p4 ∨ (((True ∧ True) ∨ p2) ∧ p5)) ∧ (p3 → ((True ∧ ((p2 → p1) ∧ p1)) → p2))) ∨ ((p5 ∧ (p3 ∧ p1)) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_992528873763519991048305648185 : (((p4 ∧ (((p1 ∨ p1) ∨ False) ∧ (((p1 → (p2 ∨ ((p3 → (True → True)) ∧ p4))) ∨ (p3 ∨ False)) → (((p3 ∨ p3) → False) ∧ p5)))) → p5) ∧ True) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h8 : ((p1 → (p2 ∨ ((p3 → (True → True)) ∧ p4))) ∨ (p3 ∨ False)) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h9
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Implications on the right can always be decomposed.
        intro h10
        -- Implications on the right can always be decomposed.
        intro h11
        -- True on the right can always be proven directly.
        apply True.intro
        -- One of the premise coincides with the conclusion.
        exact h2
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h12 := h5 h8
      -- We need to get the right conjuct of h12 based on <expert-advice>.
      let h13 := h12.right
      -- One of the premise coincides with the conclusion.
      exact h13
    case inr h14 =>
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h15 : ((p1 → (p2 ∨ ((p3 → (True → True)) ∧ p4))) ∨ (p3 ∨ False)) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h16
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Implications on the right can always be decomposed.
        intro h17
        -- Implications on the right can always be decomposed.
        intro h18
        -- True on the right can always be proven directly.
        apply True.intro
        -- One of the premise coincides with the conclusion.
        exact h2
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h19 := h5 h15
      -- We need to get the right conjuct of h19 based on <expert-advice>.
      let h20 := h19.right
      -- One of the premise coincides with the conclusion.
      exact h20
  case inr h21 =>
    -- False on the left can always be used.
    apply False.elim h21
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_699499470580035777354722840639 : ((((((p5 ∧ True) ∧ ((True ∨ (p3 ∧ (False → p4))) → p5)) ∨ p3) → (((((True ∨ False) → p4) → (p2 → (p2 ∧ p3))) ∨ True) ∨ p3)) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h3.left
    let h6 := h3.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_23968183155390770450863039219 : (((((p3 ∧ False) ∧ False) ∨ p3) → (((((p3 → p3) ∧ (p1 ∨ p3)) → p2) ∨ p3) → ((((p4 → False) ∧ p3) ∨ (p1 → p4)) ∨ True))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- Conjunctions on the left can always be decomposed.
      let h7 := h5.left
      let h8 := h5.right
      -- False on the left can always be used.
      apply False.elim h8
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- Conjunctions on the left can always be decomposed.
      let h14 := h12.left
      let h15 := h12.right
      -- False on the left can always be used.
      apply False.elim h15
    case inr h16 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299355066473322130375291411490 : (False ∨ (((p5 → (p5 → True)) → (p2 ∧ (((p5 ∧ True) ∧ (p5 → (((p4 ∧ p1) ∧ (p4 → (p4 → p5))) ∨ True))) → (p5 ∧ False)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_713211564549859110741757331846 : ((((p2 ∨ (((p1 → p5) ∨ p1) → p2)) ∨ (((p2 ∨ (p1 ∧ (p2 ∨ False))) ∨ ((((True ∨ p2) ∧ p4) → True) ∨ (p5 ∨ p3))) ∨ p5)) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



