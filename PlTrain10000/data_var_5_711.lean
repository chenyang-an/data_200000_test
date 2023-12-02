variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_693245717368224382603710906962 : ((((p2 ∨ (p2 ∨ ((False ∧ ((p4 ∨ ((p5 ∧ True) ∨ p2)) ∧ p5)) ∨ p1))) ∧ ((p2 → p2) ∧ ((False ∧ True) → (p5 ∧ (p1 ∨ False))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64461827134516119611174683084 : ((p1 ∨ ((p2 ∧ ((False ∨ (((True → p2) ∨ (False → p3)) ∨ ((True ∧ (p5 → p1)) → (p3 → p5)))) ∨ p5)) ∧ (p2 ∨ (p3 ∨ False)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_616065298141350566516461432391 : (((((p2 ∨ (((p3 ∧ (((p1 ∨ True) ∨ (p4 ∨ True)) ∨ p2)) ∨ p4) → True)) → (True ∧ (p1 ∧ ((False → False) ∨ (p4 ∨ p2))))) ∨ True) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_972833040641760343027924962678 : ((((p2 ∨ True) → ((((p2 ∧ p1) ∧ (p3 ∧ (p3 → (p4 ∨ ((p5 ∧ True) ∨ (((p1 → p2) ∨ p3) ∧ p4)))))) ∨ True) ∧ (False ∧ p4))) → p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p2 ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- False on the left can always be used.
  apply False.elim h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53432306999290564967109050294 : ((((True ∨ ((p4 ∧ p1) ∨ p4)) ∨ (p2 ∨ ((p5 ∧ True) → p1))) → (((((p1 ∧ p4) ∧ True) ∧ True) ∨ p1) ∨ (True ∨ (p5 ∧ True)))) ∨ p3) := by
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h4 =>
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h5 =>
        -- Conjunctions on the left can always be decomposed.
        let h6 := h5.left
        let h7 := h5.right
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h7
      case inr h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_651141720558935694676646437729 : (((((p5 ∧ ((p5 ∨ p2) → p5)) ∨ ((((p5 ∨ (True ∨ p3)) ∧ p1) ∧ ((p3 ∧ p1) → False)) → ((False ∨ p1) ∨ p1))) ∧ (True ∨ p1)) ∨ p5) ∧ True) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113612058875391825672193511045 : (((p4 ∨ ((((p4 ∨ p5) ∨ (p4 ∨ p3)) ∨ (p3 ∨ p1)) ∨ ((((p1 ∨ False) ∧ p4) ∧ True) ∨ (p1 ∨ True)))) ∨ (True ∧ p1)) ∨ (True ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_745582157409013250423290183746 : ((((True ∨ p1) → (p2 → ((False ∨ ((p4 → p3) ∧ (((p3 ∧ (p5 ∨ p3)) ∧ (p2 → p4)) ∨ False))) ∨ (p4 ∨ (p2 ∨ (True ∧ p5)))))) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114495284664849291032455568344 : (((((p4 ∧ ((p4 ∨ False) → (p4 ∨ p1))) → p4) → (p4 ∨ ((p2 → True) → (p4 ∨ p1)))) → (p2 ∧ ((p4 ∧ False) ∧ p2))) ∨ (False → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_122868656961361937311593269098 : ((((p2 → (True ∨ (p4 ∨ (True ∧ p1)))) → ((((True ∧ p3) ∧ True) ∨ True) → (p4 ∧ (True ∧ False)))) ∧ (p4 → (p4 ∨ p4))) → (p5 ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (p2 → (True ∨ (p4 ∨ (True ∧ p1)))) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h4
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h7 : (((True ∧ p3) ∧ True) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h8 := h6 h7
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- We need to get the right conjuct of h9 based on <expert-advice>.
  let h10 := h9.right
  -- False on the left can always be used.
  apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207913309087639626780035496640 : (((p4 ∧ (p1 → p2)) ∧ (p3 ∨ True)) → ((((p1 ∧ p3) ∧ (p3 → p2)) ∨ ((((p2 ∨ (p2 ∨ True)) → False) ∧ p1) → False)) ∧ (False → p2))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
    have h10 : (p2 ∨ (p2 ∨ True)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h8, we can now drive its conclusion.
    let h11 := h8 h10
    -- False on the left can always be used.
    apply False.elim h11
  case inr h12 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h13
    -- Conjunctions on the left can always be decomposed.
    let h14 := h13.left
    let h15 := h13.right
    -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
    have h16 : (p2 ∨ (p2 ∨ True)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h14, we can now drive its conclusion.
    let h17 := h14 h16
    -- False on the left can always be used.
    apply False.elim h17
  -- Implications on the right can always be decomposed.
  intro h18
  -- False on the left can always be used.
  apply False.elim h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_247286991851285504563901795750 : ((False ∨ False) ∨ ((((((p4 ∧ (p4 ∨ p3)) ∨ True) ∨ True) → (p5 ∨ (p1 ∧ True))) ∨ (p4 ∨ (p1 → (True → ((False → p1) → True))))) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114437343540680775404201428980 : (((p3 ∨ ((p1 → p3) → ((p3 ∧ ((True → False) ∨ p2)) ∨ (p2 ∨ ((p1 → p3) ∨ False))))) ∨ ((p1 ∨ p5) ∧ (True ∨ False))) ∨ (p2 ∧ p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : p1 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172631236790877326464738977313 : (((p4 ∧ False) ∧ (False ∨ (p3 ∧ (((True ∧ ((p2 ∨ p4) ∨ p3)) ∨ p5) ∨ p3)))) ∨ ((p1 ∨ ((True ∨ (False ∧ (p4 → True))) ∨ True)) ∨ p1)) := by
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
theorem thm_5_vars_206618517027528467988012069337 : ((p1 → ((False ∧ (p1 → p1)) ∧ p4)) ∨ ((p3 ∧ (((False ∧ (p1 ∧ True)) → ((p5 ∨ p3) ∨ (p3 ∨ p1))) → p2)) ∨ (p3 ∨ (p1 ∨ True)))) := by
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
theorem thm_5_vars_45090235594553558097882018413 : ((((p4 ∧ p3) → (((p1 → p1) → p3) → (p1 ∧ (True ∧ (((((p1 ∧ p4) → p1) → False) → (p5 ∨ (p4 ∨ p4))) → True))))) → p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199465068467130300225830616855 : (((True ∨ (p5 → (p1 → (False ∧ p2)))) ∨ p3) → ((p1 ∧ (False ∧ p2)) ∨ (((p2 → (p2 → ((False → (p4 → p5)) ∧ p2))) ∨ p3) ∨ p5))) := by
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h4
      -- Implications on the right can always be decomposed.
      intro h5
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h6
      -- Implications on the right can always be decomposed.
      intro h7
      -- False on the left can always be used.
      apply False.elim h6
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h9
      -- Implications on the right can always be decomposed.
      intro h10
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h11
      -- Implications on the right can always be decomposed.
      intro h12
      -- False on the left can always be used.
      apply False.elim h11
      -- One of the premise coincides with the conclusion.
      exact h9
  case inr h13 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248459442691817020049991658677 : ((p2 ∨ p5) ∨ (((((p3 → p2) ∨ ((p4 → p2) → p2)) ∨ (p3 → p3)) ∧ ((p5 → True) → False)) ∨ (((p1 → p1) ∨ (p3 → p3)) ∨ False))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_355699379979901356278138899565 : (p5 → ((((p4 ∧ (p5 ∧ p5)) ∧ (p3 ∧ ((True → (False ∧ False)) ∧ p4))) ∧ (((p1 → p3) ∨ p1) ∨ (p1 → (p5 ∧ p5)))) → (p2 → p1))) := by
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
  let h8 := h6.left
  let h9 := h6.right
  -- Conjunctions on the left can always be decomposed.
  let h10 := h9.left
  let h11 := h9.right
  -- Conjunctions on the left can always be decomposed.
  let h12 := h7.left
  let h13 := h7.right
  -- Conjunctions on the left can always be decomposed.
  let h14 := h13.left
  let h15 := h13.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h16 =>
    -- Disjunctions on the left can always be decomposed.
    cases h16
    case inl h17 =>
      -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
      have h18 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h14, we can now drive its conclusion.
      let h19 := h14 h18
      -- We need to get the left conjuct of h19 based on <expert-advice>.
      let h20 := h19.left
      -- False on the left can always be used.
      apply False.elim h20
    case inr h21 =>
      -- One of the premise coincides with the conclusion.
      exact h21
  case inr h22 =>
    -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
    have h23 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h14, we can now drive its conclusion.
    let h24 := h14 h23
    -- We need to get the left conjuct of h24 based on <expert-advice>.
    let h25 := h24.left
    -- False on the left can always be used.
    apply False.elim h25



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314282667556360924375211203691 : (p3 ∨ ((p1 → (((p1 ∨ (p4 ∨ (True ∧ p3))) → ((((True → False) → False) → (p5 → (p5 → False))) ∨ p2)) ∨ p1)) ∨ (p2 ∨ (p1 → p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303817328742556457915326409211 : (p1 ∨ (((p3 ∨ (((p2 → p5) → False) → (True ∨ (((p2 → (p2 → True)) ∧ True) → (((p4 → p4) ∨ (p4 → p3)) ∧ p4))))) → p3) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137705335999392664273731264401 : ((p1 ∨ ((p5 ∨ (p2 ∨ (p5 ∧ ((p2 ∨ ((p4 → p4) ∨ (p2 ∨ p1))) ∧ p5)))) → ((False ∧ True) ∨ (True ∨ p3)))) ∨ ((p2 → p1) → p5)) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h11 =>
        -- Disjunctions on the left can always be decomposed.
        cases h11
        case inl h12 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h13 =>
          -- Disjunctions on the left can always be decomposed.
          cases h13
          case inl h14 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h15 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- True on the right can always be proven directly.
            apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_612889633782645869131240257303 : (((((False ∨ (((p4 → p5) → ((((p3 ∨ False) ∨ (p4 → p5)) ∧ False) ∨ (p1 ∨ (p5 ∨ p4)))) → (p2 ∨ p4))) ∨ (False → True)) ∨ p2) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_669354380288111900076171517397 : (((((False ∧ (False ∧ (((((p5 ∨ ((False → p2) ∨ p3)) ∧ p5) → (p2 ∧ p4)) → p1) → p2))) ∧ (p2 ∨ p5)) ∨ ((p2 → p1) ∨ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179136440741990115560557449754 : ((p1 ∧ ((p5 ∨ p2) → (p5 ∨ ((p3 → ((False ∧ p4) ∧ p5)) → p1)))) ∨ (((p3 ∧ p1) → ((p4 → (p4 ∨ (p5 ∨ p1))) ∨ p2)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_611465365947341690664852142772 : (((((p3 ∧ ((((p5 → (p2 ∨ p5)) ∨ (((False ∨ False) ∨ True) ∨ p4)) ∨ (p1 ∨ ((False → True) ∨ (p5 ∨ p3)))) ∧ True)) → False) ∨ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314008347440796061945216477402 : (p3 ∨ ((p2 ∧ ((((p4 → True) → (((p3 ∨ p3) ∨ p2) → (p2 ∨ (((p4 → p3) → p4) ∧ p3)))) ∧ (p2 → p1)) ∧ p3)) ∨ (p4 → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_780051922585305183383810472666 : (((p2 ∨ ((p3 ∨ ((p4 → (p3 ∨ (p2 ∨ (((False ∧ (p1 ∧ p3)) ∨ p3) ∨ p4)))) ∨ (((False ∨ p2) ∧ p4) → p1))) ∨ (p5 ∧ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185457703650666378409109255739 : ((p1 ∨ ((True ∧ ((p1 ∧ (p1 ∨ (False ∧ True))) ∧ p4)) ∧ p1)) ∨ ((p5 → ((p1 ∨ False) → ((((p5 ∧ p3) ∨ p4) → True) → p1))) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337693990944120915747460560903 : (p1 → (((p4 → ((p2 ∧ (((((True ∨ (p3 ∨ p2)) ∧ True) ∧ p1) → True) ∨ p3)) ∨ True)) → p3) → (((True ∨ p1) ∧ p1) → (p3 ∨ p5)))) := by
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
  cases h4
  case inl h6 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h7 : (p4 → ((p2 ∧ (((((True ∨ (p3 ∨ p2)) ∧ True) ∧ p1) → True) ∨ p3)) ∨ True)) := by
      -- Implications on the right can always be decomposed.
      intro h8
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h9 := h2 h7
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h9
  case inr h10 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h11 : (p4 → ((p2 ∧ (((((True ∨ (p3 ∨ p2)) ∧ True) ∧ p1) → True) ∨ p3)) ∨ True)) := by
      -- Implications on the right can always be decomposed.
      intro h12
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h13 := h2 h11
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40026198239176302880050868109 : ((((((p3 ∨ (((((p3 → (True ∨ (((True ∧ p4) ∧ (p4 ∧ True)) ∨ p1))) ∨ False) → p3) ∧ p2) → p1)) ∨ p5) ∧ False) ∧ False) ∨ True) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_239589141971557471865420555977 : ((p3 ∨ True) ∧ ((True ∧ (((False ∧ (((p5 ∨ True) → (p1 ∨ p4)) → (p4 ∨ (p4 ∨ (False ∨ p5))))) ∧ p4) ∧ p5)) ∨ ((p1 ∨ p2) ∨ True))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184553357378170676440816348284 : ((((p1 → (p1 → ((p5 → p4) → p1))) → True) → (True ∧ p2)) ∨ ((True ∧ (((False ∨ p1) ∧ (p1 ∨ (p3 ∧ (True ∧ False)))) ∨ True)) ∨ p3)) := by
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
theorem thm_5_vars_315373414247751262049288349652 : (p3 ∨ ((p4 ∨ (p1 → p1)) ∧ ((p4 ∧ (((((p2 ∨ (p2 ∨ p2)) → (False ∨ (False ∨ p5))) → p4) ∨ (False ∧ p3)) ∧ False)) ∨ (p3 → True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50236156775262365235602757909 : (((((True ∧ ((p1 ∨ (p2 → p3)) ∧ (((False ∨ (p2 ∧ p2)) ∧ (p3 ∨ False)) ∨ True))) ∨ p1) → p1) ∨ (p5 → (True ∨ (p3 ∨ True)))) ∨ p5) := by
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
theorem thm_5_vars_592676215488270061456629720525 : (((((p3 → (False → (p3 ∨ (p5 ∧ ((((p2 → (p4 ∧ (p3 → p5))) ∧ p2) ∨ (p5 ∧ (True ∨ p5))) ∨ p1))))) → (p4 → False)) ∧ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328126140683914361776118296812 : (True → (((((p5 ∨ False) → (p1 → p3)) ∧ p2) → (p4 ∨ ((p4 ∨ ((p3 ∨ (False → p2)) ∨ p5)) ∧ (True ∨ p3)))) ∨ (False → (p3 ∨ p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_607923492268576323908697743933 : (((((p1 → ((((((p3 ∧ (p2 ∧ p3)) ∨ p5) ∧ p1) → ((p1 ∧ (p1 → False)) → (p5 ∨ p1))) → False) ∨ (p2 ∨ False))) ∧ p2) ∨ True) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_127031850461653645319902090133 : ((False ∨ ((((p4 ∨ p4) ∧ (p1 ∧ ((p1 ∨ p4) ∨ p3))) ∧ (True ∨ ((((False ∧ True) → p3) → p3) ∨ (p2 ∨ False)))) ∨ p2)) → (p5 ∨ True)) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- Conjunctions on the left can always be decomposed.
      let h7 := h5.left
      let h8 := h5.right
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h9 =>
        -- Conjunctions on the left can always be decomposed.
        let h10 := h8.left
        let h11 := h8.right
        -- Disjunctions on the left can always be decomposed.
        cases h11
        case inl h12 =>
          -- Disjunctions on the left can always be decomposed.
          cases h12
          case inl h13 =>
            -- Disjunctions on the left can always be decomposed.
            cases h6
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
                -- Disjunctions on the left can always be decomposed.
                cases h17
                case inl h18 =>
                  -- Show the right disjunct based on <expert-advice>.
                  apply Or.inr
                  -- True on the right can always be proven directly.
                  apply True.intro
                case inr h19 =>
                  -- False on the left can always be used.
                  apply False.elim h19
          case inr h20 =>
            -- Disjunctions on the left can always be decomposed.
            cases h6
            case inl h21 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- True on the right can always be proven directly.
              apply True.intro
            case inr h22 =>
              -- Disjunctions on the left can always be decomposed.
              cases h22
              case inl h23 =>
                -- Show the right disjunct based on <expert-advice>.
                apply Or.inr
                -- True on the right can always be proven directly.
                apply True.intro
              case inr h24 =>
                -- Disjunctions on the left can always be decomposed.
                cases h24
                case inl h25 =>
                  -- Show the right disjunct based on <expert-advice>.
                  apply Or.inr
                  -- True on the right can always be proven directly.
                  apply True.intro
                case inr h26 =>
                  -- False on the left can always be used.
                  apply False.elim h26
        case inr h27 =>
          -- Disjunctions on the left can always be decomposed.
          cases h6
          case inl h28 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h29 =>
            -- Disjunctions on the left can always be decomposed.
            cases h29
            case inl h30 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- True on the right can always be proven directly.
              apply True.intro
            case inr h31 =>
              -- Disjunctions on the left can always be decomposed.
              cases h31
              case inl h32 =>
                -- Show the right disjunct based on <expert-advice>.
                apply Or.inr
                -- True on the right can always be proven directly.
                apply True.intro
              case inr h33 =>
                -- False on the left can always be used.
                apply False.elim h33
      case inr h34 =>
        -- Conjunctions on the left can always be decomposed.
        let h35 := h8.left
        let h36 := h8.right
        -- Disjunctions on the left can always be decomposed.
        cases h36
        case inl h37 =>
          -- Disjunctions on the left can always be decomposed.
          cases h37
          case inl h38 =>
            -- Disjunctions on the left can always be decomposed.
            cases h6
            case inl h39 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- True on the right can always be proven directly.
              apply True.intro
            case inr h40 =>
              -- Disjunctions on the left can always be decomposed.
              cases h40
              case inl h41 =>
                -- Show the right disjunct based on <expert-advice>.
                apply Or.inr
                -- True on the right can always be proven directly.
                apply True.intro
              case inr h42 =>
                -- Disjunctions on the left can always be decomposed.
                cases h42
                case inl h43 =>
                  -- Show the right disjunct based on <expert-advice>.
                  apply Or.inr
                  -- True on the right can always be proven directly.
                  apply True.intro
                case inr h44 =>
                  -- False on the left can always be used.
                  apply False.elim h44
          case inr h45 =>
            -- Disjunctions on the left can always be decomposed.
            cases h6
            case inl h46 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- True on the right can always be proven directly.
              apply True.intro
            case inr h47 =>
              -- Disjunctions on the left can always be decomposed.
              cases h47
              case inl h48 =>
                -- Show the right disjunct based on <expert-advice>.
                apply Or.inr
                -- True on the right can always be proven directly.
                apply True.intro
              case inr h49 =>
                -- Disjunctions on the left can always be decomposed.
                cases h49
                case inl h50 =>
                  -- Show the right disjunct based on <expert-advice>.
                  apply Or.inr
                  -- True on the right can always be proven directly.
                  apply True.intro
                case inr h51 =>
                  -- False on the left can always be used.
                  apply False.elim h51
        case inr h52 =>
          -- Disjunctions on the left can always be decomposed.
          cases h6
          case inl h53 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h54 =>
            -- Disjunctions on the left can always be decomposed.
            cases h54
            case inl h55 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- True on the right can always be proven directly.
              apply True.intro
            case inr h56 =>
              -- Disjunctions on the left can always be decomposed.
              cases h56
              case inl h57 =>
                -- Show the right disjunct based on <expert-advice>.
                apply Or.inr
                -- True on the right can always be proven directly.
                apply True.intro
              case inr h58 =>
                -- False on the left can always be used.
                apply False.elim h58
    case inr h59 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57047232769391918684717428111 : (((p3 → (p3 ∨ False)) ∧ (((p4 ∧ p1) ∨ False) ∨ (((p3 → (False ∧ p3)) ∧ (False ∨ p1)) ∨ ((True ∧ p1) ∨ (True ∧ (True ∨ p1)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_212849963881059115200387985540 : ((p2 → (False ∨ (False → p3))) ∧ (p3 → ((False → (True ∧ p1)) → ((True ∧ True) ∧ (((p1 ∧ p2) ∧ (p5 → (p4 ∨ False))) → (p1 ∨ p2)))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h5
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_727438422576510513248716122864 : ((((p3 ∧ (p5 ∧ p5)) ∨ ((p2 ∧ ((p1 → False) ∨ ((True ∨ p4) ∨ (((True ∨ (False → p5)) ∧ False) ∨ True)))) ∧ (p2 ∨ (p4 ∨ p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336288340617040372396136663145 : (p1 → ((((p4 ∨ (True ∨ (p3 ∧ p1))) ∨ (p3 ∨ True)) ∧ ((p5 → p5) → ((p5 ∧ p2) ∨ ((p2 → (False ∧ (True ∨ p2))) ∧ False)))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68334652336390419595209067789 : ((p3 → ((p1 ∧ (p3 ∧ (((((False ∧ True) ∧ (False ∧ False)) ∨ p5) ∨ False) → False))) → (((p4 → False) → ((p4 → p1) ∧ p2)) ∨ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53090447864174505988461132784 : (((p1 ∨ (p3 ∧ ((p1 ∨ p4) ∧ (((False ∧ p2) ∧ False) ∧ p1)))) ∧ ((p4 ∨ (True → p1)) ∨ (p5 ∨ (p5 ∨ (p2 ∨ (p1 ∨ p2)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114067181856279635277806390924 : (((((((True ∨ p3) ∧ (False ∨ p1)) ∨ False) → p4) → ((False ∧ (p4 ∧ ((False ∧ p2) ∧ p5))) ∨ p3)) ∨ ((p5 → False) ∨ True)) ∨ (False ∧ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234055914714175385589337979518 : ((p5 ∨ (p4 → p3)) → (p4 ∨ (((p3 ∧ ((p3 → ((p3 ∨ p5) ∧ (False ∧ False))) → p2)) → (True → (((p3 ∨ False) ∧ True) ∨ p5))) ∨ True))) := by
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
theorem thm_5_vars_773415404490104917751399237118 : (((False ∨ ((((True ∧ ((((True ∨ p3) ∨ (p2 ∨ (p1 → p1))) → p4) ∧ (p5 ∨ (True ∨ p5)))) → (p4 → (p2 ∨ p5))) ∧ True) ∨ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_325113012734831708649095243345 : (p5 ∨ ((p4 → p5) → ((((p2 ∧ False) → p1) → p4) → ((p2 ∨ (((p5 ∧ p5) ∧ (((p2 ∧ p5) ∧ p3) ∨ False)) ∨ (p5 ∧ p1))) ∨ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : ((p2 ∧ False) → p1) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- False on the left can always be used.
    apply False.elim h6
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h7 := h2 h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45356423428925432034669819655 : (((p4 ∧ ((p1 → (((((p5 ∨ True) ∧ p4) ∧ (((p3 ∨ False) ∧ (p2 → (p2 ∧ p4))) ∨ False)) ∨ True) ∧ p3)) ∨ (p5 → p2))) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61851118520567752078292826789 : ((p2 ∧ (((True ∧ (p1 ∨ (p2 → ((p4 → ((p4 ∨ p5) ∧ p5)) ∨ (True ∨ (p4 → p4)))))) → (True ∨ ((False → p5) ∨ p1))) → p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46889956484813307618212635905 : (((((p4 ∧ ((p5 → False) → (((p4 → p5) → False) → (p1 ∨ ((p5 ∨ (p3 → (p1 ∨ True))) → False))))) ∨ p5) ∨ True) ∨ (p3 → True)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_813564329942904627223061166269 : (((((True → ((((p4 → (p3 ∨ True)) → p4) ∨ ((p2 ∨ False) → ((True ∨ (p3 ∧ (p1 ∨ (p5 → p2)))) → True))) ∧ False)) ∧ p3) ∧ p4) → False) ∧ True) := by
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
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h6 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h7 := h4 h6
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- False on the left can always be used.
  apply False.elim h8
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_264028638228084507956605329892 : (True ∧ ((((p4 ∧ (p4 → False)) ∨ (p1 ∨ (p1 ∨ True))) ∧ True) ∧ ((((True ∨ (p2 ∧ True)) ∧ (True → (False ∧ p4))) → (p1 ∨ True)) ∨ p2))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_670455167314962669286432602201 : (((((p3 ∧ False) ∧ (p1 ∧ (p2 ∨ ((p4 ∧ (((p5 → p5) ∧ p4) ∧ True)) ∧ (False ∧ (True → (p1 ∧ p2))))))) ∨ ((p4 ∨ False) ∨ True)) ∨ False) ∧ True) := by
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
theorem thm_5_vars_151393712925086511507337055080 : (((((p3 ∧ ((True ∧ (p1 ∧ (p1 → False))) ∧ p1)) ∨ p4) ∧ (((p3 → p5) ∧ p2) ∨ p3)) ∧ (p4 ∨ True)) → (((p1 ∧ p5) → False) ∨ True)) := by
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
    let h7 := h6.left
    let h8 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Conjunctions on the left can always be decomposed.
    let h11 := h9.left
    let h12 := h9.right
    -- Conjunctions on the left can always be decomposed.
    let h13 := h12.left
    let h14 := h12.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h15 =>
      -- Conjunctions on the left can always be decomposed.
      let h16 := h15.left
      let h17 := h15.right
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h18 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h19 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h20 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h21 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h22 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h23 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h24 =>
      -- Conjunctions on the left can always be decomposed.
      let h25 := h24.left
      let h26 := h24.right
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h27 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h28 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h29 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h30 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h31 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_791927177935213881036434579985 : (((True → ((((True ∧ ((p4 → True) → (p3 → p3))) → False) ∨ ((p1 ∨ (p2 ∧ False)) → ((p3 ∧ (p3 → p1)) → p4))) ∨ (True ∨ True))) ∨ False) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157374479353348054334539671298 : (((p5 → (((p4 → (True ∨ False)) → ((p4 → p3) → False)) → (((p1 ∧ False) → True) → p5))) → p1) ∨ ((p4 → p4) ∨ (p5 → (True ∧ True)))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207159511389479374686984860207 : (((p3 → ((p5 ∧ p4) → p2)) ∧ p3) → (((p5 ∧ p5) ∧ (True → (p3 ∧ (p2 → False)))) ∨ (p2 ∨ (True ∧ ((p3 ∨ p5) ∧ (p2 ∨ True)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_737126590567666494096524705824 : ((((p3 → p4) ∧ (((((((p1 ∨ (p4 ∧ p5)) ∨ True) ∧ p5) ∧ p4) ∨ (p1 ∧ p4)) ∨ ((((p4 ∨ p4) ∨ p2) ∧ p4) ∧ p4)) ∨ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116645280883989265166574084367 : (((p2 → p4) ∧ ((True → p2) ∨ ((False ∨ (p3 → (False ∧ False))) ∧ ((p3 ∧ p3) ∨ ((p5 → (p2 ∧ (True ∨ p5))) ∨ False))))) ∨ (False → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161139101528292491903637223680 : (((p3 → True) ∧ (True → (p2 ∧ (((((p1 → (p3 ∨ p2)) → p5) → False) ∨ (True ∨ p1)) ∧ p3)))) → (p5 → (p1 ∨ ((p1 ∧ p1) → p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h5
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h8 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h9 := h4 h8
  -- We need to get the right conjuct of h9 based on <expert-advice>.
  let h10 := h9.right
  -- We need to get the right conjuct of h10 based on <expert-advice>.
  let h11 := h10.right
  -- One of the premise coincides with the conclusion.
  exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234869074842105795736861503441 : ((p5 → (p2 → p1)) → (((False ∧ p5) ∧ ((((p5 ∧ ((True ∨ p1) → p3)) → (p5 ∧ ((p2 → (p4 ∧ p4)) ∧ p5))) → False) → p5)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68186787148995666667213965988 : ((p3 → ((((((((p4 ∨ p2) → p4) ∨ ((p5 → p4) ∧ (p3 ∧ True))) ∨ p2) ∨ p2) ∧ (p2 → False)) → (False ∨ (p4 → p5))) ∨ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149521166379540105624189306045 : ((p1 ∧ (p3 ∧ ((False ∨ (p5 ∨ True)) ∧ (p2 → ((p1 ∧ p4) → (((p2 → (p2 → p1)) → p5) ∧ p2)))))) ∨ (True ∧ ((p2 ∨ False) → True))) := by
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
theorem thm_5_vars_57965958530651961718917304275 : (((p2 → (p3 → p4)) → (((p4 ∨ (p2 ∨ (p4 ∧ (((p2 ∨ ((p2 ∨ False) → True)) ∧ p2) ∧ p3)))) → p3) ∨ ((p1 → True) ∨ p5))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115251448409486546232394677548 : (((((True ∧ p4) ∧ (p1 ∧ p5)) ∨ (p1 ∧ (False ∧ p2))) ∨ (True → (((p5 ∧ p4) ∨ ((p5 → p4) ∧ (p5 → True))) ∨ p1))) ∨ (False → False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118613381664001329704798590134 : ((p4 ∨ (((((p5 ∧ p4) → p1) ∨ (p5 → ((p4 ∧ p5) → p3))) ∨ (p4 ∧ p5)) ∨ ((((p4 ∧ p4) ∧ p3) ∨ p1) ∨ True))) ∨ (False → p1)) := by
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
theorem thm_5_vars_622688999792381208920630260682 : ((((p4 ∧ ((p5 ∧ (p1 ∧ ((p4 ∨ p1) ∨ True))) ∨ (((True ∧ (p2 → p1)) → (p4 → p4)) ∨ (((p1 ∨ p3) → p5) ∧ p1)))) ∨ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63111147350450496255871160052 : ((p5 ∧ ((((((p5 ∨ False) ∨ p4) ∧ ((p2 ∨ (True ∨ True)) ∧ p2)) ∨ ((p4 ∧ (((p5 → p1) ∧ p1) ∨ p2)) → p1)) ∧ p1) → p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_698613384242870300100334650772 : (((((False ∨ (p5 ∨ p5)) ∧ (((p4 ∨ p5) → False) ∧ (p1 ∧ p3))) ∨ (p4 ∧ ((((p2 → (p3 ∨ (p2 → p2))) → p3) → False) ∨ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200352684352047955394146058199 : (((True → False) ∧ (p3 → (p1 → (p4 → p3)))) → (((p3 ∧ True) ∨ p5) → ((((False ∧ (p1 → (p1 ∨ p4))) ∨ p2) ∨ (p1 → p4)) ∧ p4))) := by
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
    let h4 := h3.left
    let h5 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h6 := h1.left
    let h7 := h1.right
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h8 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h9 := h6 h8
    -- False on the left can always be used.
    apply False.elim h9
  case inr h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h1.left
    let h12 := h1.right
    -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
    have h13 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h11, we can now drive its conclusion.
    let h14 := h11 h13
    -- False on the left can always be used.
    apply False.elim h14
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h15 =>
    -- Conjunctions on the left can always be decomposed.
    let h16 := h15.left
    let h17 := h15.right
    -- Conjunctions on the left can always be decomposed.
    let h18 := h1.left
    let h19 := h1.right
    -- We want to use the implication h18 based on <expert-advice>. So we show its premise.
    have h20 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h18, we can now drive its conclusion.
    let h21 := h18 h20
    -- False on the left can always be used.
    apply False.elim h21
  case inr h22 =>
    -- Conjunctions on the left can always be decomposed.
    let h23 := h1.left
    let h24 := h1.right
    -- We want to use the implication h23 based on <expert-advice>. So we show its premise.
    have h25 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h23, we can now drive its conclusion.
    let h26 := h23 h25
    -- False on the left can always be used.
    apply False.elim h26



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161274455423614838628665640625 : (((p5 ∨ p3) → ((p4 ∧ False) ∧ ((((p2 ∧ p1) → p2) ∨ p5) ∧ ((p1 ∨ (True → p1)) → p4)))) → ((((False ∧ p2) → p4) → False) → p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : ((False ∧ p2) → p4) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- False on the left can always be used.
    apply False.elim h5
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h7 := h2 h3
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199307692888792737656802307136 : (((((True ∨ p1) ∨ (p3 ∧ p3)) ∨ p3) ∨ False) → ((((False ∨ True) ∨ p3) → ((p1 ∨ (p3 ∧ (p5 ∨ p3))) → (p3 ∧ p5))) ∨ (p1 → True))) := by
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
          -- Implications on the right can always be decomposed.
          intro h6
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h7 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h8
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h9 =>
        -- Conjunctions on the left can always be decomposed.
        let h10 := h9.left
        let h11 := h9.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h12
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h13 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h14
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h15 =>
    -- False on the left can always be used.
    apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_243998125407894928677178077881 : ((True ∧ p1) ∨ (p4 → (((True ∨ p3) ∧ (p1 ∨ (p5 ∧ p1))) ∨ ((p5 ∨ ((p3 ∨ True) ∨ p4)) ∨ (((p5 → p3) → False) ∧ (p3 → p3)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_748855399895478520430936801392 : ((((p4 → p1) → (((True → (True → (False ∨ (((False ∧ ((p5 ∧ (p5 ∨ p2)) ∨ False)) ∧ (p1 → (p4 ∨ p3))) ∨ p1)))) ∨ False) ∨ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_522460570674233184584305512273 : ((((p4 → p4) → ((p4 ∨ (p4 ∧ ((p4 ∨ p2) ∨ (p5 → False)))) ∨ ((p4 ∨ (((p1 ∨ (p3 ∧ True)) ∧ p2) ∧ (True → p2))) → True))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_738693339723744373982371782655 : ((((p2 ∧ p1) ∨ (p1 → (((p1 → ((False ∧ (p5 ∨ (p1 ∧ True))) ∧ p4)) ∨ p3) ∨ ((p3 → ((True → (p2 ∨ p5)) → True)) ∨ False)))) ∨ False) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_106568646400224012218995733513 : ((((p4 ∨ (((False ∨ p5) → p4) → False)) ∨ False) → ((p4 ∨ p3) ∨ (((p2 ∧ (True ∧ p2)) ∧ p1) ∨ (p4 → (p5 ∨ False))))) ∧ (False → False)) := by
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h5
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h6 : ((False ∨ p5) → p4) := by
        -- Implications on the right can always be decomposed.
        intro h7
        -- Disjunctions on the left can always be decomposed.
        cases h7
        case inl h8 =>
          -- False on the left can always be used.
          apply False.elim h8
        case inr h9 =>
          -- One of the premise coincides with the conclusion.
          exact h5
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h10 := h4 h6
      -- False on the left can always be used.
      apply False.elim h10
  case inr h11 =>
    -- False on the left can always be used.
    apply False.elim h11
  -- Implications on the right can always be decomposed.
  intro h12
  -- False on the left can always be used.
  apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299124187201031824091846591900 : (False ∨ ((((((((((p5 → ((p3 ∨ p4) ∨ (p4 ∨ False))) → (p3 → p4)) ∨ p2) ∨ (p5 ∨ p3)) ∨ False) ∨ p2) ∧ p5) ∨ True) ∨ p4) ∨ p1)) := by
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
theorem thm_5_vars_595916132677558793543336619271 : ((((((p2 ∨ ((p4 ∨ p4) ∨ p4)) ∨ ((p4 ∧ False) ∨ p4)) ∨ (((p1 ∧ True) ∧ (p2 → (p4 → (p5 ∨ (False → False))))) ∨ True)) ∧ True) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_624643085616841015136881567182 : ((((p4 ∨ ((p1 ∧ p1) ∧ (((((((p3 ∨ p1) ∧ p2) → p5) ∨ ((p4 ∧ (p3 ∧ (p5 ∧ p2))) ∨ p1)) → p5) → p3) → p4))) ∨ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47413864919979103570225264103 : (((False ∧ (True ∧ ((((p3 → p2) ∧ ((p5 ∧ ((p1 ∧ (False → p5)) ∧ p4)) ∧ ((p5 → True) ∨ p4))) ∨ p4) ∧ False))) ∨ (False → p4)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_140751873571911521185131189450 : (((((True ∨ True) ∨ True) ∨ ((p5 ∧ ((p4 ∨ (p2 ∧ p4)) ∨ p5)) ∧ p3)) → ((((p2 ∧ p3) ∨ p3) ∧ True) ∨ False)) → ((p2 → p5) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149666694480039360932616830656 : ((p4 ∧ (p5 ∨ (((False → ((p5 ∧ (((p4 → p2) → p1) ∧ (True ∧ (p3 ∨ False)))) ∧ p1)) → False) ∧ p4))) ∨ (((True ∨ p3) → True) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_600884919592228895049907159196 : ((((p1 ∧ (((p5 → ((False → (p2 ∧ (p2 ∨ (p5 ∨ (p3 ∧ (p4 ∨ (p3 ∨ False))))))) → ((True → p3) → p2))) ∨ p1) ∧ p2)) ∧ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185046322662287095687047594315 : (((p4 → False) ∧ (p4 ∧ ((p1 → (p4 → (p4 ∨ p4))) → p3))) ∨ (((False ∨ (((True → p2) → p1) → p1)) ∧ p5) → ((p4 → p3) ∨ True))) := by
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
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184365407029807172603492085055 : (((p2 ∨ (p5 ∧ (p3 ∨ ((p4 ∧ p2) → (p3 ∨ True))))) → p2) ∨ (True ∨ ((False → ((p3 → p1) → p1)) ∧ ((p4 ∧ p2) ∨ (False → True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_34202552137775610789203613785 : ((True → (((((p2 ∧ (True ∧ True)) ∨ p2) ∨ ((p2 → ((p4 → p1) → ((False ∧ True) ∧ True))) ∨ False)) ∧ (True ∨ False)) ∨ (True ∨ p2))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38387128081670547553275995380 : (((((((p4 ∨ (False ∨ True)) → ((p4 ∨ p3) ∧ p3)) ∧ (p4 → p1)) ∨ (p1 ∧ True)) → (p5 ∧ ((True ∧ p2) ∧ (p5 ∧ p2)))) ∧ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118131443290181956184934860868 : ((False ∨ ((((p1 → p4) → p5) ∧ ((False ∨ p3) → ((((p2 → p2) ∨ p5) → (p3 → True)) → p1))) ∧ ((p5 ∨ p1) ∨ p3))) ∨ (False ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191838565702044480048599758344 : ((p3 ∨ ((False ∧ (p2 ∧ p3)) ∧ (p3 ∧ (p3 ∧ p5)))) ∨ (True ∨ ((((p4 → p5) ∨ ((True ∧ False) ∨ (p5 ∨ p4))) ∧ p4) → (p2 → p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58878695945401066254400754363 : (((False ∧ p1) ∨ ((((p3 ∧ p5) ∧ ((((False ∧ p4) ∧ p5) → (p2 ∨ p2)) ∧ p3)) → (((p2 ∧ False) ∨ p2) → (p1 ∨ p1))) → p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186400777134767887414193666608 : (((p5 ∧ (p5 ∨ ((p2 ∨ p2) ∨ ((False ∧ p2) → p2)))) → p1) → ((p2 → (p4 ∨ (((p3 ∧ (p4 → (p4 ∧ True))) → p5) ∧ p3))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_704392627495951009121042641629 : ((((((p2 → True) → p5) ∧ ((False → p5) ∧ (False ∨ p1))) → (((False ∨ ((p3 ∧ (p4 ∧ p5)) ∨ (p4 ∧ True))) → (False → p5)) → p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301928182124322278313404497287 : (False ∨ ((True ∨ p2) → (p2 → ((False ∧ ((((p4 → p2) ∨ (p2 → p4)) ∨ True) ∧ (p1 → p1))) ∨ ((p3 ∨ True) → (False ∨ (False ∨ True))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
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
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_77992666815666235788626128022 : (((p4 ∨ (((p4 ∧ (((p2 → p4) → p3) → (False ∧ (((p5 → p3) → p4) ∨ (False → p1))))) ∨ (p4 → True)) ∨ (p4 ∧ p2))) → False) → False) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p4 ∨ (((p4 ∧ (((p2 → p4) → p3) → (False ∧ (((p5 → p3) → p4) ∨ (False → p1))))) ∨ (p4 → True)) ∨ (p4 ∧ p2))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138776322546457694816601501305 : ((((p5 → p1) ∧ ((False ∨ ((p3 → False) ∨ ((p5 → ((p2 → False) ∧ p2)) → (p5 ∨ True)))) → (p1 ∧ False))) ∧ True) → ((p3 ∨ p5) ∧ p1)) := by
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
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h6 : (False ∨ ((p3 → False) ∨ ((p5 → ((p2 → False) ∧ p2)) → (p5 ∨ True)))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h8 := h5 h6
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- False on the left can always be used.
  apply False.elim h9
  -- Conjunctions on the left can always be decomposed.
  let h10 := h1.left
  let h11 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h12 := h10.left
  let h13 := h10.right
  -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
  have h14 : (False ∨ ((p3 → False) ∨ ((p5 → ((p2 → False) ∧ p2)) → (p5 ∨ True)))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h15
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h13, we can now drive its conclusion.
  let h16 := h13 h14
  -- We need to get the left conjuct of h16 based on <expert-advice>.
  let h17 := h16.left
  -- One of the premise coincides with the conclusion.
  exact h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338059591608906890891786969350 : (p1 → ((((p4 ∧ ((False ∨ (p1 ∧ True)) → False)) ∨ p5) ∨ p2) → (((p5 → True) → (p5 ∨ False)) → (p3 ∨ (((p2 → p5) → False) → p5))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
      let h6 := h5.left
      let h7 := h5.right
      -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
      have h8 : (False ∨ (p1 ∧ True)) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h1
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h7, we can now drive its conclusion.
      let h9 := h7 h8
      -- False on the left can always be used.
      apply False.elim h9
    case inr h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h11
      -- One of the premise coincides with the conclusion.
      exact h10
  case inr h12 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h13
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h14 : (p5 → True) := by
      -- Implications on the right can always be decomposed.
      intro h15
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h16 := h3 h14
    -- Disjunctions on the left can always be decomposed.
    cases h16
    case inl h17 =>
      -- One of the premise coincides with the conclusion.
      exact h17
    case inr h18 =>
      -- False on the left can always be used.
      apply False.elim h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173487420090912386595763464187 : ((((((p3 ∨ (p1 → p4)) → p4) → ((p5 ∧ (p4 → p4)) ∧ p3)) → p3) ∧ p2) → ((((p2 → p2) → (p4 ∨ (p2 ∧ p4))) ∨ False) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



