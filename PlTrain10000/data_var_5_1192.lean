variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_592524136816324777986562754806 : ((((((True ∧ True) → (((((True ∨ (p3 ∨ p4)) ∨ p3) → True) → ((False → p5) → (p4 ∨ p2))) → (p5 ∨ p3))) → (p4 ∨ False)) ∧ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_617537881824089721024607253673 : ((((((p3 ∧ p4) ∨ ((p2 → p3) ∨ p1)) ∧ (p2 → (False ∧ (((p4 → (p2 ∨ p5)) ∧ p4) → (((True → True) ∧ p3) ∧ p1))))) ∨ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53754050785081118466575033524 : ((((((p5 ∨ p5) ∨ p4) ∧ (p3 ∧ (p4 ∨ p2))) ∧ p3) ∨ ((p5 → (False → False)) ∨ (((p4 ∧ (False ∨ p3)) ∨ p4) ∧ (p1 → p3)))) ∨ False) := by
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
theorem thm_5_vars_797850187604249049195386942747 : (((p1 → (((((((p1 ∧ p5) → p3) ∨ p2) ∧ (p4 → p5)) → (((False ∨ p4) ∧ ((p4 ∨ True) ∨ p4)) ∨ p4)) ∨ True) ∨ (p4 ∧ False))) ∨ False) ∧ True) := by
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
theorem thm_5_vars_179972146726835144334439389473 : ((((p1 ∧ ((True ∨ p1) → (p2 ∧ False))) → (p4 ∨ (True → False))) ∨ p3) → (p2 → ((p1 ∧ (p4 ∨ ((p1 ∧ (True → p1)) → p5))) ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321139005182542838841764786378 : (p4 ∨ (p2 ∨ ((p2 → ((p3 → p4) → p1)) ∨ (True → (((((p4 → (False ∧ (True ∧ p4))) ∨ p2) → p5) ∨ False) ∨ (p3 → (p3 ∨ p1))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_678069068163039395466485148266 : ((((((p3 ∨ ((True → p1) → ((p3 ∨ p1) ∨ ((True ∧ p4) ∧ p1)))) ∨ False) → (p1 ∨ (p3 → p5))) ∨ (((p4 → True) → False) → False)) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p4 → True) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- False on the left can always be used.
  apply False.elim h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346373451404091287512240693793 : (p3 → ((p4 ∧ (((p1 ∨ ((p5 ∨ (p3 ∧ True)) ∨ (p5 ∧ (p4 ∨ p5)))) ∧ (True ∧ p2)) ∨ (((p5 ∧ p1) → p3) ∨ True))) ∨ (p1 ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51408243104394604970323027351 : (((((False ∨ (((p4 → (False ∧ False)) ∨ True) ∨ True)) ∨ (True ∧ ((p1 → p2) → p3))) → p4) → ((p5 ∨ p3) ∨ (p3 → (True → False)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350932618338733705434518984945 : (p4 → ((((p1 ∧ False) → ((False → (p5 ∨ (((p1 → (p3 → p4)) ∧ p4) ∧ ((p2 ∨ (True ∧ p2)) ∧ True)))) ∨ False)) → p1) ∨ (p3 → p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_79689197618138956991892651289 : ((((False → (False ∨ p3)) → ((((p1 ∧ ((p1 ∧ (p2 → (p5 ∧ p1))) ∨ ((False ∧ p2) ∧ p4))) ∧ True) → p2) ∧ p1)) ∨ (False ∧ p5)) → p1) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h3 : (False → (False ∨ p3)) := by
      -- Implications on the right can always be decomposed.
      intro h4
      -- False on the left can always be used.
      apply False.elim h4
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h5 := h2 h3
    -- We need to get the right conjuct of h5 based on <expert-advice>.
    let h6 := h5.right
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- False on the left can always be used.
    apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256355066601547635666878518714 : ((False ∨ p2) → ((p3 ∨ (p5 → (((((True → p4) ∨ (p3 → p4)) ∨ p2) ∨ (p4 → p3)) ∨ p2))) → (((p4 → (p5 → p3)) ∧ True) ∨ p2))) := by
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
      -- False on the left can always be used.
      apply False.elim h4
    case inr h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h7 =>
      -- False on the left can always be used.
      apply False.elim h7
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64547505694159268771651439870 : ((p1 ∨ ((True → (False → ((p3 → p2) → p2))) → ((p1 ∨ p3) ∧ ((False ∨ True) ∧ (((p5 → True) ∨ ((p4 ∧ p1) → p4)) → p4))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_343249139042926408561918220594 : (p2 → ((p1 → (False ∧ p2)) → ((((True ∧ (False ∧ p3)) ∨ ((p5 → p4) ∨ p4)) ∧ False) ∨ ((p2 ∧ p5) ∨ ((False → True) ∧ (False → False)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h4
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_21431843379951279753208812053 : (((((p3 → ((True → p5) ∨ (True ∨ p5))) ∨ False) → p4) ∨ (p4 → ((((((True → p3) ∨ p4) ∧ p4) → p4) → p1) ∨ (False → p3)))) ∧ True) := by
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
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_608162099579514599224105053641 : (((((((False → p1) ∧ (((p4 ∨ False) ∨ False) → (((p4 ∧ ((False ∨ ((p1 ∧ p1) ∨ p5)) → True)) → False) ∧ True))) ∧ p3) ∨ p5) ∨ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_613615156774145019748721614742 : ((((((p2 ∧ (p2 → ((((p4 ∧ ((False ∨ (True ∧ p4)) → p5)) ∧ p4) ∨ p4) ∨ p5))) ∧ (p4 ∨ p3)) ∧ ((False ∨ p2) ∨ p3)) ∨ True) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_219266424896263202995207725264 : ((p1 ∨ (p2 ∨ (False ∧ True))) → (p5 → (p2 ∨ ((((p1 ∧ p2) ∨ (False → (p4 → p1))) ∧ p3) → ((p1 → (p4 ∧ (p4 ∨ p1))) ∨ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
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
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h12
    case inr h13 =>
      -- Conjunctions on the left can always be decomposed.
      let h14 := h13.left
      let h15 := h13.right
      -- False on the left can always be used.
      apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41245833017912268347704497674 : ((((((p5 ∨ (p1 ∨ (p1 → ((((False ∨ True) ∨ p4) → p3) → False)))) → (p3 ∨ p3)) ∨ p1) ∨ ((True → p2) ∨ (False ∧ p5))) ∨ True) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347944609466074188913115403515 : (p3 → ((p3 ∨ p2) ∧ ((((p1 ∧ p3) ∧ (p1 ∧ ((p5 ∨ p1) → p1))) ∧ True) ∨ ((p2 ∧ False) ∨ (p5 → ((True → False) → (p1 ∨ False))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_748061942712113853810923908335 : ((((p1 → p1) → (p2 → (((((p4 → (p2 ∧ (p3 ∧ False))) ∧ (p5 → False)) ∨ (p2 → p2)) ∨ p3) ∧ (p2 ∨ (True ∧ (p5 → p3)))))) ∨ p1) ∧ True) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_209277039393696925228743333410 : ((True → (((p3 → True) ∨ p2) ∨ True)) → (((p4 ∨ (False ∧ False)) ∨ ((True ∧ p1) ∨ (False ∨ ((p2 ∧ True) → True)))) ∨ (p2 → (p4 ∨ p3)))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40755108408806162526380600813 : (((((p1 → p4) ∧ (((((((p5 → p5) → (p4 ∨ ((False → p3) → False))) ∨ p2) → p2) ∨ False) ∧ (True ∧ p3)) ∧ p4)) → p2) ∨ p2) ∨ p3) := by
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
  let h4 := h3.left
  let h5 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h7.left
    let h10 := h7.right
    -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
    have h11 : (((p5 → p5) → (p4 ∨ ((False → p3) → False))) ∨ p2) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h12
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h5
    -- We have shown the premise of h8, we can now drive its conclusion.
    let h13 := h8 h11
    -- One of the premise coincides with the conclusion.
    exact h13
  case inr h14 =>
    -- False on the left can always be used.
    apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_89008324278239901243240918693 : ((((p1 ∨ p3) ∧ p3) ∧ (((p5 ∨ p3) → ((p5 ∧ ((True ∧ ((p5 → (p5 → p2)) ∨ True)) → (p3 → True))) ∧ p3)) ∧ (p3 → p4))) → p5) := by
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
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h9 : (p5 ∨ p3) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h10 := h7 h9
    -- We need to get the left conjuct of h10 based on <expert-advice>.
    let h11 := h10.left
    -- We need to get the left conjuct of h11 based on <expert-advice>.
    let h12 := h11.left
    -- One of the premise coincides with the conclusion.
    exact h12
  case inr h13 =>
    -- Conjunctions on the left can always be decomposed.
    let h14 := h3.left
    let h15 := h3.right
    -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
    have h16 : (p5 ∨ p3) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5
    -- We have shown the premise of h14, we can now drive its conclusion.
    let h17 := h14 h16
    -- We need to get the left conjuct of h17 based on <expert-advice>.
    let h18 := h17.left
    -- We need to get the left conjuct of h18 based on <expert-advice>.
    let h19 := h18.left
    -- One of the premise coincides with the conclusion.
    exact h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50089174588775503597256180424 : (((p2 ∧ (((p5 → (p1 → ((p5 → p5) ∨ ((True ∨ (p4 ∧ (True ∧ p2))) ∧ p4)))) → p4) ∨ p3)) ∧ ((p3 ∧ False) ∧ (p4 ∧ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_318865529968442339875822848483 : (p4 ∨ ((((p3 → p5) ∧ ((((p4 → ((p5 ∨ False) → p5)) → (True ∨ False)) → (p4 ∨ p5)) ∨ p1)) ∨ (p5 → p4)) ∨ (False → (p5 → p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227912607189882616348991635040 : ((p2 ∧ (p4 → False)) ∨ ((((False → (p2 ∨ (p4 ∧ (p1 ∧ p3)))) → False) ∨ (p2 → ((False ∨ (True → p2)) → (p1 ∨ p3)))) ∨ (p4 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63232925791153876203831293482 : ((p5 ∧ (((p3 ∨ (p2 ∨ p2)) → (p4 ∨ (False → ((p5 ∨ p1) → (p5 → True))))) → ((p3 ∧ p4) ∧ (p2 → ((p4 ∨ p5) → True))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157019539499090719404258244231 : ((((True ∨ p5) ∧ ((False ∨ True) ∧ ((p1 ∨ (p2 → False)) ∨ (p3 ∧ ((p2 → p4) ∨ False))))) ∨ p4) ∨ (p2 → (p3 → (p3 ∨ (False ∧ p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314547203133791685392523170857 : (p3 ∨ ((((False → (p4 → (p5 → ((p5 → False) → p1)))) → p5) ∨ ((p1 → p4) ∨ (p2 ∨ p2))) ∨ ((((p5 → p4) → True) → p4) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_335681676968064414789632875737 : (p1 → (((((p4 ∨ (False → (p2 ∨ (p2 ∧ (p3 → p3))))) → (True → (((False ∧ p1) ∧ p4) ∨ (p4 → (p4 → False))))) ∧ p3) ∨ p1) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_266121544273874231346250888517 : (True ∧ (p3 → ((((True ∧ True) ∧ p4) ∨ ((((True ∨ p2) ∧ (((True ∧ p5) ∧ (p2 ∧ p4)) → p3)) → p4) → ((p4 → p2) → p5))) ∨ True))) := by
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
theorem thm_5_vars_116738270682914882375968574022 : (((p4 ∧ False) ∨ (False ∧ (True → (((((p4 ∧ p4) ∧ (((p5 → (p3 ∨ False)) ∨ p5) ∨ (p2 → p1))) → True) → p4) ∨ p5)))) ∨ (p3 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164509002865359392945000618530 : ((((((((p5 → p5) → (p1 → p3)) ∧ True) ∨ (p5 ∧ p4)) → p2) ∧ (p5 ∨ p5)) ∧ False) ∨ (False → (p3 ∧ (True ∧ ((p4 ∧ p1) → p4))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57670142139202014652034146381 : ((((False → False) ∨ True) → (p1 ∨ (((p5 ∨ (False ∨ (p5 → p2))) ∨ (True ∨ p1)) → (p1 ∨ ((p5 ∨ (p3 ∨ (p2 → p2))) ∨ p2))))) ∨ p3) := by
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
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h9
          -- One of the premise coincides with the conclusion.
          exact h9
    case inr h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h12
        -- One of the premise coincides with the conclusion.
        exact h12
      case inr h13 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h13
  case inr h14 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h15
    -- Disjunctions on the left can always be decomposed.
    cases h15
    case inl h16 =>
      -- Disjunctions on the left can always be decomposed.
      cases h16
      case inl h17 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h17
      case inr h18 =>
        -- Disjunctions on the left can always be decomposed.
        cases h18
        case inl h19 =>
          -- False on the left can always be used.
          apply False.elim h19
        case inr h20 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h21
          -- One of the premise coincides with the conclusion.
          exact h21
    case inr h22 =>
      -- Disjunctions on the left can always be decomposed.
      cases h22
      case inl h23 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h24
        -- One of the premise coincides with the conclusion.
        exact h24
      case inr h25 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h25



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_746414250612212229050068447256 : ((((p2 ∨ p2) → ((p4 → (p1 → (p3 → (((((((p2 ∨ p5) ∧ True) ∧ p1) ∨ p5) ∧ (p5 → True)) → p5) ∨ (True → p4))))) ∧ True)) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- One of the premise coincides with the conclusion.
    exact h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190656581742504184374242111626 : (((p4 ∨ ((p1 ∨ (p3 ∧ p4)) → (p4 → p4))) → p2) ∨ (p4 → ((p5 ∨ ((p5 ∧ (True ∨ False)) → (p3 → (False → p5)))) ∨ (False ∨ p3)))) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_709121492322534014571219777034 : ((((((p2 ∧ p1) ∨ p3) → ((p2 ∧ False) ∧ p1)) → ((True ∨ False) ∧ (p3 ∧ ((((p3 → ((p5 → p3) → p5)) → p5) → p3) ∧ p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112828770344192201150066733436 : (((((p5 → p2) → (p2 ∧ p1)) ∨ (((((False → p3) ∨ p3) → (p5 ∨ (((p2 ∨ p1) ∧ True) ∨ p4))) ∧ p1) → p5)) → p4) ∨ (True ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337805828132370471113440946391 : (p1 → (((p3 ∧ p5) ∧ (((True ∨ p4) → ((((p3 ∨ p1) → p4) ∨ p2) ∧ True)) → p1)) → (p5 ∧ (((True → p4) → False) ∨ (True ∧ p1))))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h6
  -- Conjunctions on the left can always be decomposed.
  let h7 := h2.left
  let h8 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h9 := h7.left
  let h10 := h7.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_929187340460401021032803489328 : ((((((False ∨ (True → p5)) ∧ (p5 ∨ p5)) ∧ (p3 → p1)) ∨ ((p5 ∧ (p3 ∧ ((True ∧ False) → (p1 ∧ p4)))) ∧ ((p3 ∧ p1) ∧ p4))) → p5) ∧ True) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- False on the left can always be used.
      apply False.elim h7
    case inr h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h9 =>
        -- One of the premise coincides with the conclusion.
        exact h9
      case inr h10 =>
        -- One of the premise coincides with the conclusion.
        exact h10
  case inr h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- Conjunctions on the left can always be decomposed.
    let h14 := h12.left
    let h15 := h12.right
    -- Conjunctions on the left can always be decomposed.
    let h16 := h15.left
    let h17 := h15.right
    -- Conjunctions on the left can always be decomposed.
    let h18 := h13.left
    let h19 := h13.right
    -- Conjunctions on the left can always be decomposed.
    let h20 := h18.left
    let h21 := h18.right
    -- One of the premise coincides with the conclusion.
    exact h14
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117420679510471730151713635537 : ((p1 ∧ (((True ∨ (True ∨ True)) ∨ (True ∧ (True → (((p1 → True) → ((p4 → (p5 ∨ p4)) ∨ False)) ∧ True)))) → (p3 ∨ p1))) ∨ (False → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218260694068761782621997645659 : (((p1 ∨ False) ∨ (p4 ∧ p5)) → ((((False ∨ (p5 ∧ p1)) ∨ (p1 → True)) ∧ (False ∧ ((True → (p2 → False)) ∧ p3))) ∨ (p4 ∨ (p1 ∧ p1)))) := by
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
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h3
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h4 =>
      -- False on the left can always be used.
      apply False.elim h4
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_344287090291892941281090306997 : (p2 → (p3 ∨ ((((p4 ∨ (p5 ∧ ((p1 ∧ (p2 → p5)) ∨ (p2 → ((False → p2) ∧ True))))) ∨ False) ∧ ((False ∧ (False → p4)) ∧ False)) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_598244318553445165411595422889 : ((((((p3 → False) → p3) ∨ ((((p3 ∨ p4) ∨ (p4 ∧ (((p3 ∨ p4) ∨ p5) ∨ (p3 → True)))) ∨ (False ∨ (p5 ∧ p5))) → p3)) ∧ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200508292191818383162028837362 : (((True ∨ False) → (False ∨ ((p4 → p3) ∨ p3))) → ((p5 ∨ (p4 ∨ (p5 → (((p3 ∨ p1) ∨ (True → (p5 → p5))) ∨ True)))) ∨ (p3 → p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304771409992961876128487463431 : (p1 ∨ ((False ∨ (p1 ∨ (((p5 ∨ (((True ∨ True) → True) → p4)) → (False ∧ False)) ∧ (((p5 ∧ p4) ∧ (p2 ∧ True)) → False)))) ∨ (p3 → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_657676648936338845415970005183 : (((((p5 ∨ p5) → ((p4 → (((p1 → (p4 ∧ p5)) ∧ p3) ∧ p4)) → ((((p1 ∧ (p5 ∨ p5)) → p2) → False) ∨ p1))) ∨ (p3 → p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160595127399406719786677892403 : ((((((True ∨ (p5 ∧ p3)) → False) → p3) ∨ (p1 → p4)) ∧ ((p5 → p2) ∧ ((p4 → False) ∧ p4))) → (p1 → (p4 ∧ ((p2 ∧ p3) ∧ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- One of the premise coincides with the conclusion.
    exact h9
  case inr h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h4.left
    let h12 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h13 := h12.left
    let h14 := h12.right
    -- One of the premise coincides with the conclusion.
    exact h14
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h15 := h1.left
  let h16 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h15
  case inl h17 =>
    -- Conjunctions on the left can always be decomposed.
    let h18 := h16.left
    let h19 := h16.right
    -- Conjunctions on the left can always be decomposed.
    let h20 := h19.left
    let h21 := h19.right
    -- We want to use the implication h20 based on <expert-advice>. So we show its premise.
    have h22 : p4 := by
      -- One of the premise coincides with the conclusion.
      exact h21
    -- We have shown the premise of h20, we can now drive its conclusion.
    let h23 := h20 h22
    -- False on the left can always be used.
    apply False.elim h23
  case inr h24 =>
    -- Conjunctions on the left can always be decomposed.
    let h25 := h16.left
    let h26 := h16.right
    -- Conjunctions on the left can always be decomposed.
    let h27 := h26.left
    let h28 := h26.right
    -- We want to use the implication h27 based on <expert-advice>. So we show its premise.
    have h29 : p4 := by
      -- One of the premise coincides with the conclusion.
      exact h28
    -- We have shown the premise of h27, we can now drive its conclusion.
    let h30 := h27 h29
    -- False on the left can always be used.
    apply False.elim h30
  -- Conjunctions on the left can always be decomposed.
  let h31 := h1.left
  let h32 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h31
  case inl h33 =>
    -- Conjunctions on the left can always be decomposed.
    let h34 := h32.left
    let h35 := h32.right
    -- Conjunctions on the left can always be decomposed.
    let h36 := h35.left
    let h37 := h35.right
    -- We want to use the implication h36 based on <expert-advice>. So we show its premise.
    have h38 : p4 := by
      -- One of the premise coincides with the conclusion.
      exact h37
    -- We have shown the premise of h36, we can now drive its conclusion.
    let h39 := h36 h38
    -- False on the left can always be used.
    apply False.elim h39
  case inr h40 =>
    -- Conjunctions on the left can always be decomposed.
    let h41 := h32.left
    let h42 := h32.right
    -- Conjunctions on the left can always be decomposed.
    let h43 := h42.left
    let h44 := h42.right
    -- We want to use the implication h43 based on <expert-advice>. So we show its premise.
    have h45 : p4 := by
      -- One of the premise coincides with the conclusion.
      exact h44
    -- We have shown the premise of h43, we can now drive its conclusion.
    let h46 := h43 h45
    -- False on the left can always be used.
    apply False.elim h46
  -- Conjunctions on the left can always be decomposed.
  let h47 := h1.left
  let h48 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h47
  case inl h49 =>
    -- Conjunctions on the left can always be decomposed.
    let h50 := h48.left
    let h51 := h48.right
    -- Conjunctions on the left can always be decomposed.
    let h52 := h51.left
    let h53 := h51.right
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h54 =>
    -- Conjunctions on the left can always be decomposed.
    let h55 := h48.left
    let h56 := h48.right
    -- Conjunctions on the left can always be decomposed.
    let h57 := h56.left
    let h58 := h56.right
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258187979671361946634146783902 : ((p4 ∨ p4) → (((p3 → False) → p5) → ((p2 ∧ (((p2 → (True ∨ p5)) → (p2 → (((p5 ∨ p4) ∨ (p3 ∨ p4)) → p3))) ∧ p2)) ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51060694843574579538844256172 : (((True → ((p4 ∨ (p2 ∧ ((((False → p2) ∧ p1) ∧ p3) ∨ False))) ∨ (p5 ∨ (p5 → p3)))) ∧ (p3 ∨ ((True ∨ p2) ∧ (p2 → p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_657753338896108324916933026546 : ((((True ∧ (((p4 ∧ p4) → (p1 ∨ (p3 ∨ (p1 ∧ (False ∧ ((True → (p2 → p5)) ∧ (p3 ∧ p3))))))) ∨ (p5 → True))) ∨ (p5 ∨ p3)) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187709427137184209262733660875 : ((False → (p4 ∨ ((((p2 ∧ p4) → p3) ∨ p3) ∧ (p1 ∨ p2)))) → ((p4 → p2) ∨ ((((p3 ∨ p4) ∨ False) ∧ True) → ((p5 → p3) ∨ p4)))) := by
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
  cases h3
  case inl h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h7
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h8
  case inr h9 =>
    -- False on the left can always be used.
    apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135984075165602657922415410553 : ((((p5 → (True ∨ ((p3 ∧ True) ∨ p5))) ∧ (False ∧ p2)) ∨ ((p2 ∨ (((True ∧ p5) → False) ∨ p3)) ∧ (False ∨ p4))) ∨ (p1 → (p3 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114552639005378368106411759244 : (((((p4 → ((((p4 ∧ p4) → p1) ∨ (p1 ∨ p2)) ∨ p5)) ∧ (p3 ∨ p3)) ∨ p3) ∧ (((p1 → (True → False)) ∧ False) → p5)) ∨ (True ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113611603767553125776937834049 : (((p4 ∨ (((p3 ∨ ((p2 → (True → (p3 ∨ (p2 ∧ p3)))) ∨ p5)) → ((p5 → p5) ∧ False)) → (False ∨ p5))) ∨ (False → p1)) ∨ (p1 → p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_614336122083893010582491426107 : ((((((True ∨ False) ∨ ((p5 → (p1 ∨ False)) → (p2 ∧ (((p1 ∨ (p4 ∨ (p4 → p4))) → p3) → p2)))) → (p2 → (p1 ∨ p2))) ∨ False) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h5 =>
      -- False on the left can always be used.
      apply False.elim h5
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_487966012350733534586423000 : (((((p4 ∧ (p2 → (p2 → ((p5 ∨ p2) ∨ (((p1 ∧ (p4 ∧ p3)) → (True → p5)) → p4))))) → (p3 ∨ p2)) ∧ p4) ∧ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181177534806246390953840476899 : ((p1 ∧ ((((True ∧ False) ∨ (p3 ∧ False)) ∨ p1) → ((p5 ∨ p3) → p2))) → ((((p3 ∨ p5) → p5) ∧ (True → ((p2 → False) ∧ False))) → False)) := by
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
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h7 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h8 := h4 h7
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- False on the left can always be used.
  apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156625113574249979927575809621 : (((((((False ∨ ((True ∧ (p2 → p3)) ∧ p5)) ∧ True) ∧ (True → True)) ∨ (p4 ∨ p1)) ∨ True) ∧ p1) ∨ (p1 ∨ (((False ∨ p4) ∧ p3) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48509094601103321125165079231 : (((((((((p5 ∨ (p1 ∨ (p3 ∨ False))) ∧ False) ∨ p5) ∨ ((p3 → p3) ∨ p2)) ∧ False) ∧ (p5 ∧ p2)) ∨ True) ∧ (False → (True ∨ True))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_175122766462163221496066153341 : ((p4 ∧ (p3 ∨ ((p2 → p3) ∨ (p3 ∨ (p5 ∧ (p4 ∨ ((p2 ∨ p2) ∨ p5))))))) → ((False ∨ False) ∨ ((((p4 ∨ p2) ∨ p5) ∨ p3) ∧ p4))) := by
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
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h2
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h8
        -- One of the premise coincides with the conclusion.
        exact h2
      case inr h9 =>
        -- Conjunctions on the left can always be decomposed.
        let h10 := h9.left
        let h11 := h9.right
        -- Disjunctions on the left can always be decomposed.
        cases h11
        case inl h12 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h10
          -- One of the premise coincides with the conclusion.
          exact h12
        case inr h13 =>
          -- Disjunctions on the left can always be decomposed.
          cases h13
          case inl h14 =>
            -- Disjunctions on the left can always be decomposed.
            cases h14
            case inl h15 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- Conjunctions on the right can always be decomposed.
              apply And.intro
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- One of the premise coincides with the conclusion.
              exact h10
              -- One of the premise coincides with the conclusion.
              exact h2
            case inr h16 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- Conjunctions on the right can always be decomposed.
              apply And.intro
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- One of the premise coincides with the conclusion.
              exact h10
              -- One of the premise coincides with the conclusion.
              exact h2
          case inr h17 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Conjunctions on the right can always be decomposed.
            apply And.intro
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h17
            -- One of the premise coincides with the conclusion.
            exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51876566292203080548847586260 : ((((p3 ∨ (p3 ∨ (p1 ∧ ((p4 → p1) ∧ ((False ∧ True) ∧ (False ∨ p3)))))) ∨ p5) ∨ ((((True ∧ p5) ∧ (False → p4)) ∨ p4) → True)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113660578132058865593843302541 : (((((((True → (((True ∧ False) ∧ ((True ∨ (p5 ∨ p3)) ∨ p2)) ∨ (p1 → p1))) ∨ p2) ∨ True) ∧ True) ∨ True) → (p3 → p2)) ∨ (p3 → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42645691337612300157465320007 : (((p4 ∨ (((p1 → p4) ∨ (p3 ∧ (p1 → (p2 ∨ (p2 ∧ ((p4 ∧ (((p1 ∨ True) → (p5 → p5)) ∧ p1)) ∨ p2)))))) ∧ p4)) ∨ True) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39551156628364263045832426499 : (((p1 ∨ (((((p2 → p1) ∧ False) → ((p2 ∧ (p1 ∨ p4)) → True)) → ((p2 ∨ (p2 ∨ (p2 ∨ p4))) ∨ (p3 ∧ False))) ∧ p5)) ∧ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67430381288272970178199521372 : ((p1 → ((p3 ∧ ((True ∨ (p2 → (p5 ∨ ((p1 ∨ p3) ∧ (p3 ∧ ((((p1 ∨ p2) → p1) ∨ p3) → p3)))))) → p5)) → (False ∧ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_705054374442397180104209458187 : ((((p3 → (((True ∧ p1) ∨ True) ∨ (p5 → (True ∧ p5)))) → (True → (p3 → ((False → p1) → ((((p2 ∧ p2) ∨ p3) → False) → p2))))) ∨ p4) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h6 : ((p2 ∧ p2) ∨ p3) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h7 := h5 h6
  -- False on the left can always be used.
  apply False.elim h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147404568980317162213783814289 : (((((p4 → (False ∧ True)) ∧ (p1 → p5)) → (((p4 ∨ (p1 ∧ p1)) ∨ ((p2 ∧ p2) → False)) ∨ p5)) ∨ True) ∨ (False ∨ ((p1 → False) ∧ p5))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62422726579040434615657261431 : ((p3 ∧ (((p5 ∧ (p4 ∧ p5)) ∧ p2) ∧ ((p1 ∧ p1) ∨ (((((p5 → p4) ∧ p4) ∧ False) → True) → (((True ∧ False) ∨ p2) → False))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305716629604810856358459828739 : (p1 ∨ ((p2 ∧ (p4 ∧ ((p2 → p4) ∧ (False ∨ (p4 ∧ p1))))) → ((p3 ∧ (False ∧ ((p4 ∧ (True ∧ p3)) ∧ ((True ∧ False) ∧ p1)))) ∨ p2))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178667953129776902937869486025 : ((((False → p3) → (p3 → p3)) ∧ (False ∨ ((p3 ∧ p3) → (p4 ∨ False)))) ∨ (p2 ∨ ((True ∧ ((p3 ∧ (p3 → p3)) ∨ (p3 ∧ p2))) → p3))) := by
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
  cases h3
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- One of the premise coincides with the conclusion.
    exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148373827020280176081766759845 : (((((p3 → (True ∨ (p1 ∨ (p4 → (False ∨ True))))) ∨ (True → p2)) → p3) ∨ ((p5 ∧ (p3 ∨ p5)) ∨ p1)) ∨ ((True ∨ p5) ∨ (p1 → False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319461494323098582063542011778 : (p4 ∨ ((((True → p3) → p4) ∨ ((p1 ∧ (p4 ∧ p5)) ∧ (False → p1))) ∨ ((p3 ∧ (p3 → p4)) → ((False → False) ∨ ((True → p1) ∧ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118611274272352696201835760438 : ((p4 ∨ ((((False ∧ False) ∧ (False ∧ (True → (p5 ∧ p3)))) → (True ∨ ((p4 ∨ False) ∧ p5))) → ((p3 ∨ (True ∨ p1)) ∨ True))) ∨ (p3 ∨ p5)) := by
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
theorem thm_5_vars_653735321323450405737068160454 : ((((((((((p3 ∧ (p3 ∨ p2)) ∨ p3) ∧ (p2 → False)) ∧ p1) ∧ (((True → True) ∨ True) ∨ p4)) ∨ (p4 ∧ p3)) ∧ p2) ∨ (p2 ∨ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_670099841223596743010604783293 : ((((((p1 ∧ p1) → (p4 ∨ (p4 ∧ p5))) ∧ ((True → (p1 → ((p2 → p4) ∨ p5))) ∨ ((p4 → False) ∧ True))) ∨ (p3 → (p1 → p3))) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39132053197146027317599545593 : ((((p2 ∧ p4) → (True → ((p1 ∧ (p1 ∧ (p3 ∨ (True ∧ False)))) ∨ (((p1 → (p4 ∨ (p3 → (False ∨ p1)))) ∨ p3) ∧ False)))) ∧ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_585695372793947428187665695247 : (((((((p3 → (p4 → (((True ∧ p3) ∨ True) → ((((p1 ∨ (True → p4)) ∨ (False ∧ p4)) ∨ p5) ∧ p5)))) → p2) → p4) ∧ p3) ∧ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137245219903251259936848457592 : ((p1 ∧ (((p4 ∨ (p2 → ((p1 ∧ p1) → p2))) ∧ (p4 ∧ p4)) ∨ (p5 ∨ (((p4 ∨ p1) → (p5 → p5)) ∨ p1)))) ∨ ((False ∧ p5) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_92635541455452622716117567052 : (((False → p4) → ((((p5 ∧ p4) ∧ (((p2 → (p3 ∧ p2)) ∨ p1) ∨ (True ∧ (p2 → True)))) ∧ p2) ∧ ((p5 → False) ∨ (p1 ∧ False)))) → p2) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (False → p4) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42580714004267845215206037081 : (((p2 ∨ ((True ∨ (((p1 ∧ p4) → (p5 ∧ (p5 → (p2 ∧ (p3 → p4))))) → (p4 → p5))) ∧ ((p4 ∧ (p5 → p3)) ∧ True))) ∨ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110899140808120307641036007817 : (((((p1 → (p1 → False)) → (((p4 ∧ p1) → (True ∧ p1)) ∨ ((((p2 → p2) → p4) ∧ p5) ∧ (p5 ∨ p4)))) → p3) ∧ p4) ∨ (True ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_783826697795284765038874878407 : (((p3 ∨ (((p3 → True) ∧ (p1 → p5)) → (((p5 → p4) ∧ (p3 → (True ∧ p3))) ∨ (((p1 ∨ p4) ∨ p5) → (p3 ∧ (p2 ∨ p5)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56352727766502169835967171471 : ((((p1 ∧ (False → p4)) ∨ p1) → (p2 ∨ (p3 → ((p2 → ((p3 → (p3 ∨ (p4 ∨ (p4 → p1)))) ∧ p3)) ∧ (True → (p5 ∨ False)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64163774063377448697330409584 : ((False ∨ ((p2 → True) ∧ (((p2 ∧ (p1 ∨ p1)) ∧ p3) ∨ (p2 → (((False ∨ (p2 ∧ False)) ∨ p2) ∨ ((p1 ∧ p4) ∧ (True ∨ p1))))))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147361936298709851666011447120 : ((((((p3 ∧ p3) ∨ p4) ∧ ((((p5 ∧ p1) → p5) → p5) ∨ (p3 → p1))) → ((p1 ∨ p2) ∨ p5)) ∨ p4) ∨ (False → (p1 ∨ (p5 ∧ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149471239243209545637006060836 : ((False ∧ ((p1 → False) → (p4 ∧ ((p5 → False) → (((p1 → True) ∧ p2) ∧ ((p2 ∧ False) ∨ (True ∨ False))))))) ∨ (True ∨ (p5 → (p2 → p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48969396661853036677310715139 : ((((((p2 ∧ (p2 ∨ (p1 → ((p3 ∧ (p1 → (p3 → p2))) → p4)))) ∧ (p4 ∧ (p2 → True))) → p1) ∨ False) ∨ (True → (p5 → p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168825880353752705979266918338 : ((p3 ∨ ((((((p1 ∨ p4) ∧ p1) → (p5 ∨ p5)) ∧ (p4 ∨ (p2 ∨ p5))) ∨ False) ∧ True)) → ((False ∨ (p5 → ((p3 ∨ True) ∧ p5))) ∨ False)) := by
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
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h11
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
        -- One of the premise coincides with the conclusion.
        exact h11
      case inr h12 =>
        -- Disjunctions on the left can always be decomposed.
        cases h12
        case inl h13 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h14
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
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
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
          -- One of the premise coincides with the conclusion.
          exact h16
    case inr h17 =>
      -- False on the left can always be used.
      apply False.elim h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40057724883141752916764562494 : (((((((((p4 → ((False ∨ p5) → False)) ∧ p3) ∧ p4) → (p4 ∧ ((False ∨ False) ∧ p3))) → ((True → p4) ∧ p1)) ∨ True) ∧ p3) ∨ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_787658607199488642536489414354 : (((p4 ∨ (p4 ∨ (((True ∨ (False ∨ (p5 ∨ (((p4 → p3) ∧ ((((p2 → (False ∧ True)) ∧ p5) ∨ p1) ∨ p3)) ∧ p3)))) → p5) ∨ True))) ∨ p1) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_316895222908622054997205954697 : (p3 ∨ (p1 → (False ∨ (((p3 ∧ (p3 ∨ (False → p3))) ∨ ((p2 ∨ (p1 ∧ p3)) → p4)) → (((p5 ∨ p1) ∨ p3) ∨ ((p2 ∧ p1) → p4)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h7 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
  case inr h8 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172375581179898944031319028908 : (((p1 → ((p2 ∨ p5) ∧ (p1 → True))) ∨ ((False ∨ (True → (p1 ∧ p5))) ∨ True)) ∨ ((((False ∧ (p3 ∨ p1)) → (p1 → p4)) ∨ p2) → True)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354735627306616465075774481927 : (p5 → (((False ∨ (((p1 ∧ (((p2 → (p3 ∨ True)) → (p2 ∧ (p1 ∧ p5))) ∨ True)) ∧ p2) ∨ p3)) ∨ (((p5 ∨ p4) ∨ p2) ∧ p5)) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54412986730628336896531066055 : ((((p5 ∨ (((p1 ∧ p3) → True) → p2)) ∧ p2) ∨ ((True ∧ ((p3 ∧ p5) ∨ True)) ∨ (((p1 → (p2 → False)) ∨ (p3 → False)) ∧ p4))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_310060206692758121187749791852 : (p2 ∨ (((p5 ∨ ((p1 ∧ p1) → (((False ∧ p2) ∨ p4) ∧ p2))) ∧ (p4 ∨ (p3 ∧ True))) → ((p2 ∨ True) ∧ (True ∨ ((p2 ∧ False) ∨ p4))))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h14 := h1.left
  let h15 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h14
  case inl h16 =>
    -- Disjunctions on the left can always be decomposed.
    cases h15
    case inl h17 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h18 =>
      -- Conjunctions on the left can always be decomposed.
      let h19 := h18.left
      let h20 := h18.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h21 =>
    -- Disjunctions on the left can always be decomposed.
    cases h15
    case inl h22 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h23 =>
      -- Conjunctions on the left can always be decomposed.
      let h24 := h23.left
      let h25 := h23.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_719513640558014542272708116154 : ((((p2 ∨ (p1 → (p2 ∧ p2))) ∨ (((((((False ∧ True) ∨ (False ∧ p5)) ∧ p2) ∨ False) ∨ p4) → p5) ∨ (p5 ∨ (False → (p5 → True))))) ∨ p2) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46656752213654204536286863659 : (((False ∨ ((((((False ∧ True) ∨ p3) ∧ (p5 → (True → p3))) ∨ (p3 → (((True ∧ False) ∨ p5) → p4))) → False) ∧ p5)) ∧ (False ∨ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347385852275111546420277911878 : (p3 → (((p3 → p4) → (((p3 → False) ∧ p3) ∧ p1)) ∨ ((p2 ∧ (((((True ∧ ((p2 → p2) ∨ True)) ∧ p2) ∨ p4) → p2) ∧ p1)) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



