variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137741349435516675372447646632 : ((p1 ∨ (p5 → ((((p1 → p2) ∨ ((True ∨ (p4 → (((False ∧ (p2 → p5)) → p2) ∨ p1))) → p4)) ∧ p5) ∨ p4))) ∨ ((p5 ∧ p1) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_692620951691951516396148363762 : (((((p1 → ((((True → p4) ∨ p1) ∨ p3) ∧ p5)) ∨ (p2 ∧ (p5 ∧ p3))) ∧ ((p1 ∧ ((True → (True → p1)) → (p5 ∧ False))) ∧ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45784799950116375543042583026 : (((p1 → (((((False ∧ (p4 ∧ p5)) ∧ (p5 ∧ (p2 ∨ (p2 → (p1 ∧ p4))))) ∧ (p3 → (p5 ∨ True))) ∧ (p5 ∧ p3)) → p2)) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_731603158868490090058791220810 : ((((p1 → (p5 ∧ p2)) → (p2 ∨ (((p4 ∧ False) → True) ∧ (True → (((p5 ∨ ((p4 → p2) → True)) ∨ p5) → ((True → p3) → p3)))))) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h8 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h9 := h5 h8
      -- One of the premise coincides with the conclusion.
      exact h9
    case inr h10 =>
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h11 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h12 := h5 h11
      -- One of the premise coincides with the conclusion.
      exact h12
  case inr h13 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h14 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h15 := h5 h14
    -- One of the premise coincides with the conclusion.
    exact h15
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_731292239778214376216348914625 : ((((p4 ∨ (p4 ∧ p5)) → ((((p5 ∨ True) → (p4 → (p2 → (((p2 ∨ p5) → p1) ∨ True)))) ∨ p2) → ((True → p3) ∧ (p1 ∨ p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_83290235602609172293924061851 : ((((False ∨ ((((True ∧ False) ∨ p5) → False) ∧ ((p5 ∨ False) ∧ p1))) ∨ ((p3 ∧ p1) ∧ True)) ∧ (((False ∨ True) ∧ (p3 → p4)) → p2)) → p3) := by
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
      -- False on the left can always be used.
      apply False.elim h5
    case inr h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h11 =>
        -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
        have h12 : ((True ∧ False) ∨ p5) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h11
        -- We have shown the premise of h7, we can now drive its conclusion.
        let h13 := h7 h12
        -- False on the left can always be used.
        apply False.elim h13
      case inr h14 =>
        -- False on the left can always be used.
        apply False.elim h14
  case inr h15 =>
    -- Conjunctions on the left can always be decomposed.
    let h16 := h15.left
    let h17 := h15.right
    -- Conjunctions on the left can always be decomposed.
    let h18 := h16.left
    let h19 := h16.right
    -- One of the premise coincides with the conclusion.
    exact h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_344150505812031557826254867369 : (p2 → (False ∨ (p4 ∨ (((p5 ∧ ((p3 → p5) ∨ (p3 ∧ ((p2 ∧ (p3 ∨ (True ∨ ((p3 → p2) ∨ p1)))) ∧ (p2 ∨ p5))))) ∨ True) ∧ p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260213655547612549178861127420 : ((p2 → p2) → (p5 → (((((p4 → (p2 ∧ p5)) → (((p3 ∨ p5) ∨ (True → p4)) ∧ p3)) → False) ∧ p5) → (p3 → (False ∧ (p5 ∧ p1)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h7 : ((p4 → (p2 ∧ p5)) → (((p3 ∨ p5) ∨ (True → p4)) ∧ p3)) := by
    -- Implications on the right can always be decomposed.
    intro h8
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h9 := h5 h7
  -- False on the left can always be used.
  apply False.elim h9
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h10 := h3.left
  let h11 := h3.right
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Conjunctions on the left can always be decomposed.
  let h12 := h3.left
  let h13 := h3.right
  -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
  have h14 : ((p4 → (p2 ∧ p5)) → (((p3 ∨ p5) ∨ (True → p4)) ∧ p3)) := by
    -- Implications on the right can always be decomposed.
    intro h15
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h12, we can now drive its conclusion.
  let h16 := h12 h14
  -- False on the left can always be used.
  apply False.elim h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38390394519855400004919540765 : (((((False ∨ (((p3 ∧ (p5 ∨ False)) → True) ∧ p5)) ∨ (True → (p2 ∧ (False ∨ p5)))) → ((p5 → p3) ∧ (p5 ∧ (True ∨ p4)))) ∧ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_624157461377201173587988017671 : ((((p2 ∨ (p4 ∨ (((((p2 ∧ p5) → (((p3 → p5) ∨ (p2 ∧ False)) ∧ (p4 → (p1 ∨ (True ∨ False))))) → False) ∧ p2) ∨ p1))) ∨ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178472800656397857368876589432 : ((((((p1 → True) → (True → False)) ∧ False) ∨ p5) ∨ ((p2 → False) → False)) ∨ ((p2 ∨ ((False → p2) → True)) ∨ (p5 → ((p5 → False) ∧ p1)))) := by
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
theorem thm_5_vars_133853558702153196752534667650 : (((False ∧ (p1 ∨ (p4 ∨ ((p5 ∧ p3) → (((p1 → p5) → (p1 ∧ False)) ∧ (False ∨ (p4 ∨ (p2 ∨ True)))))))) ∧ p2) ∨ (True → (p4 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_590355745779406741059697143708 : (((((((p5 ∧ p2) ∨ p5) → (((p4 → (p2 ∨ p2)) ∨ (((True ∨ True) ∨ (p2 ∨ p3)) ∨ ((p3 → p2) ∨ p3))) ∨ p4)) → p4) ∧ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117598603975363882006986933741 : ((p2 ∧ (p2 ∨ ((p4 ∧ (p3 → ((((p5 ∨ False) ∧ p2) ∧ p4) ∨ (((((p5 ∨ False) ∧ False) ∨ p2) → False) ∧ p5)))) ∨ True))) ∨ (True ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_766690635181638617165557269883 : (((p4 ∧ (False ∨ ((p4 ∧ (True ∧ p5)) ∨ (((((True ∧ True) ∧ p5) ∧ p5) → (False ∧ p2)) → ((p5 ∨ (p2 ∨ p3)) ∨ (p4 ∧ p3)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346303975403961271531545531475 : (p3 → ((((p3 → (p2 ∧ (False → ((p2 → (((p1 ∨ ((False ∨ p1) ∧ True)) → False) ∨ p2)) ∨ (p3 ∨ p2))))) ∨ p5) → p1) ∨ (p3 ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215092728592324812331527620230 : (((False → p4) → (p3 ∧ False)) ∨ ((p5 ∧ True) → ((p5 ∨ ((p1 ∨ (p3 ∧ (p5 → (p4 ∨ False)))) ∨ p4)) ∨ ((p5 ∧ p1) → (True ∧ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199994334462787998234874188055 : ((((True → (p2 ∧ p3)) ∨ True) → (False ∧ p5)) → ((((True ∧ (((p1 ∧ ((p4 ∧ p2) → False)) → False) → p2)) ∧ (p2 ∨ p5)) → p4) ∧ p2)) := by
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
  let h5 := h3.left
  let h6 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h7 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h8 : ((True → (p2 ∧ p3)) ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h9 := h1 h8
    -- We need to get the left conjuct of h9 based on <expert-advice>.
    let h10 := h9.left
    -- False on the left can always be used.
    apply False.elim h10
  case inr h11 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h12 : ((True → (p2 ∧ p3)) ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h13 := h1 h12
    -- We need to get the left conjuct of h13 based on <expert-advice>.
    let h14 := h13.left
    -- False on the left can always be used.
    apply False.elim h14
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h15 : ((True → (p2 ∧ p3)) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h16 := h1 h15
  -- We need to get the left conjuct of h16 based on <expert-advice>.
  let h17 := h16.left
  -- False on the left can always be used.
  apply False.elim h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_353985606037409386206509322208 : (p4 → (p3 → ((((p2 → p1) ∨ False) ∧ p5) ∨ (((p1 ∧ ((((True → p4) → (p3 ∧ p5)) ∧ (p3 ∨ p4)) ∧ p3)) → (False ∧ True)) ∨ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337594345613107554083434599202 : (p1 → (((True ∨ p3) → (p4 ∨ (((True → (p2 ∧ (p4 ∧ ((p5 → (p2 ∨ False)) ∧ False)))) ∧ p2) ∨ False))) → (True ∧ ((False ∨ p4) ∧ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (True ∨ p3) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
      have h10 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h8, we can now drive its conclusion.
      let h11 := h8 h10
      -- We need to get the right conjuct of h11 based on <expert-advice>.
      let h12 := h11.right
      -- We need to get the right conjuct of h12 based on <expert-advice>.
      let h13 := h12.right
      -- We need to get the right conjuct of h13 based on <expert-advice>.
      let h14 := h13.right
      -- False on the left can always be used.
      apply False.elim h14
    case inr h15 =>
      -- False on the left can always be used.
      apply False.elim h15
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187449497767763955889474524445 : ((True ∨ ((p2 → ((p3 → (False → (True ∨ p2))) ∧ False)) ∨ p1)) → ((p1 ∨ ((p1 ∨ p2) ∨ ((False → p3) ∨ False))) ∧ (True → (False → p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h6
      -- False on the left can always be used.
      apply False.elim h6
    case inr h7 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h7
  -- Implications on the right can always be decomposed.
  intro h8
  -- Implications on the right can always be decomposed.
  intro h9
  -- False on the left can always be used.
  apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_744320598414220220215810490853 : ((((p1 ∧ p4) → (p5 ∨ ((p1 → p1) ∧ (((True ∨ p4) ∧ p4) → (((p2 ∨ p3) ∨ (True ∨ p2)) ∨ ((False → p3) ∨ (False ∨ True))))))) ∨ p2) ∧ True) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h4
  -- One of the premise coincides with the conclusion.
  exact h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h8 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h9 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_89360592286217884459942298257 : (((True → (p2 ∧ p4)) ∧ (p3 ∧ ((p3 ∨ (p4 → False)) ∨ ((True ∧ (p3 ∨ (((False ∨ p1) → (p3 ∨ (p3 ∨ p5))) → p4))) ∧ p1)))) → p2) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h8 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h9 := h2 h8
      -- We need to get the left conjuct of h9 based on <expert-advice>.
      let h10 := h9.left
      -- One of the premise coincides with the conclusion.
      exact h10
    case inr h11 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h12 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h13 := h2 h12
      -- We need to get the left conjuct of h13 based on <expert-advice>.
      let h14 := h13.left
      -- One of the premise coincides with the conclusion.
      exact h14
  case inr h15 =>
    -- Conjunctions on the left can always be decomposed.
    let h16 := h15.left
    let h17 := h15.right
    -- Conjunctions on the left can always be decomposed.
    let h18 := h16.left
    let h19 := h16.right
    -- Disjunctions on the left can always be decomposed.
    cases h19
    case inl h20 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h21 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h22 := h2 h21
      -- We need to get the left conjuct of h22 based on <expert-advice>.
      let h23 := h22.left
      -- One of the premise coincides with the conclusion.
      exact h23
    case inr h24 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h25 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h26 := h2 h25
      -- We need to get the left conjuct of h26 based on <expert-advice>.
      let h27 := h26.left
      -- One of the premise coincides with the conclusion.
      exact h27



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166334037490609718752376306253 : ((p5 ∧ (p4 ∧ (p4 → (((p1 ∨ p3) ∧ (((p5 → p4) ∧ (p1 → p1)) ∧ p3)) → p5)))) ∨ (((False → ((False ∨ True) ∧ p5)) ∧ True) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328423492059320237821139530105 : (True → (((p5 ∧ p1) ∧ (p5 → (((False ∨ False) ∨ False) ∧ ((p5 ∨ (False ∧ (False ∨ p4))) ∨ p2)))) ∨ ((p4 ∨ ((p4 ∨ p1) ∧ p4)) → p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h8 =>
      -- One of the premise coincides with the conclusion.
      exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263148523630578849831865299780 : (True ∧ (((p2 ∨ p3) → (((p2 → (p5 → p4)) → (p4 ∧ True)) ∨ ((True ∨ ((False ∨ True) → p5)) → ((p3 ∨ p1) ∨ p4)))) ∨ (True ∨ False))) := by
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
theorem thm_5_vars_767576540793042849123699496745 : (((p5 ∧ ((((True ∧ ((p4 ∨ False) ∨ ((((False → False) → False) ∧ p5) ∨ True))) ∧ p4) ∨ ((p4 ∨ ((p3 ∨ p5) ∨ p4)) → False)) ∨ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_613346468353422315413715327178 : ((((((p1 ∨ p2) ∨ (p2 → (p3 ∨ ((True ∧ p5) ∧ ((p5 → True) → (((p1 ∨ True) ∨ (p5 ∧ p4)) ∨ p2)))))) → (False ∧ p1)) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_312229046686181932288036866836 : (p2 ∨ (p1 → (((((((True → p1) → p1) ∨ (p4 → p4)) ∧ (p2 ∨ (p3 → (p2 → (False → False))))) → (p1 ∧ p4)) → (p2 ∨ p4)) ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : ((((True → p1) → p1) ∨ (p4 → p4)) ∧ (p2 ∨ (p3 → (p2 → (False → False))))) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- One of the premise coincides with the conclusion.
    exact h4
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Implications on the right can always be decomposed.
    intro h6
    -- Implications on the right can always be decomposed.
    intro h7
    -- False on the left can always be used.
    apply False.elim h7
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h8 := h2 h3
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_427551759859762860307017291735 : (((((p3 → ((((p1 ∧ ((p3 → p4) → False)) → ((((True → True) ∧ (False → p1)) ∧ True) ∧ False)) → p4) ∨ p1)) ∧ p2) ∨ (p3 ∨ True)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_185612932732964248219015426925 : ((True → (((p5 ∧ ((p5 ∧ (False → p1)) ∧ False)) → p2) → False)) ∨ ((False ∧ ((p1 ∧ (p2 ∨ p1)) ∧ (p3 ∧ p4))) → ((p5 ∧ p4) ∨ p1))) := by
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
theorem thm_5_vars_306147787817265557950442172503 : (p1 ∨ (((True → p1) ∧ p1) ∨ (((p4 ∨ (p1 → (((p3 ∨ False) ∨ p4) ∧ (False ∧ (p5 ∨ p4))))) ∨ ((False → p1) ∧ p3)) ∨ (p1 → True)))) := by
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
theorem thm_5_vars_54052593869359981068102991509 : ((((p3 ∨ (p1 → (p4 ∨ p5))) ∨ (True → (p2 → p4))) → ((p5 → (p2 ∨ (False ∨ p1))) ∧ (True ∨ (p5 → (True ∨ (p2 ∧ p4)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_84448308394963725026131642183 : (((((((p3 ∨ ((False → False) ∧ p3)) → ((p2 ∧ p3) ∧ p2)) ∨ p4) ∨ p2) ∨ True) → ((((p2 → (p2 ∧ p2)) ∨ True) ∧ p1) ∧ p4)) → p4) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((((p3 ∨ ((False → False) ∧ p3)) → ((p2 ∧ p3) ∧ p2)) ∨ p4) ∨ p2) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180390699051599396671080205166 : ((((p1 ∧ p3) → (p4 ∧ (False → ((p5 ∧ p3) ∧ p2)))) ∨ (False ∧ p3)) → ((p5 ∨ (False → ((False ∨ True) ∨ p5))) ∨ (p1 → (p3 ∧ p2)))) := by
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
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45439016161591013345041899220 : (((True ∨ (((p5 ∨ ((False ∨ p3) → ((((p2 → p2) → p1) ∧ True) ∨ (p3 → p2)))) → p2) → ((False ∨ False) ∧ (p2 ∧ p3)))) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_252968113089445903627038261665 : ((True ∧ p2) → ((p3 ∨ p1) ∨ ((((True ∧ (p2 → (p4 ∧ p1))) ∧ (True → ((False → (False ∧ p3)) → p2))) → (p2 ∧ (p1 ∧ p4))) ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h9 := h4.left
  let h10 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h11 := h9.left
  let h12 := h9.right
  -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
  have h13 : p2 := by
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h12, we can now drive its conclusion.
  let h14 := h12 h13
  -- We need to get the right conjuct of h14 based on <expert-advice>.
  let h15 := h14.right
  -- One of the premise coincides with the conclusion.
  exact h15
  -- Conjunctions on the left can always be decomposed.
  let h16 := h4.left
  let h17 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h18 := h16.left
  let h19 := h16.right
  -- We want to use the implication h19 based on <expert-advice>. So we show its premise.
  have h20 : p2 := by
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h19, we can now drive its conclusion.
  let h21 := h19 h20
  -- We need to get the left conjuct of h21 based on <expert-advice>.
  let h22 := h21.left
  -- One of the premise coincides with the conclusion.
  exact h22



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337036907057182388605615596796 : (p1 → ((((p5 → (False → ((((True → p2) ∨ False) ∧ p3) → (False ∨ ((((p4 ∨ True) ∨ False) ∨ False) ∨ p3))))) → p4) ∧ True) ∨ (p4 ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314439905681533783459353218647 : (p3 ∨ ((p2 ∨ (((p5 → True) ∨ (p4 ∨ p1)) ∧ ((p1 ∧ (False ∧ (True ∧ (p1 ∧ p2)))) ∨ (p5 ∧ p4)))) ∨ (False → ((p3 → False) ∧ p4)))) := by
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
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161999671065420586869938923715 : ((p3 → ((p1 ∨ p1) → ((((True ∨ ((p1 ∧ p3) → p3)) ∧ (p1 ∧ p3)) ∨ (p3 → p5)) → True))) → (((False ∧ p5) ∧ (True ∧ False)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_90971839555022960554970049460 : (((False → p2) ∧ (((p2 ∨ (False ∨ (True ∨ p3))) ∧ p2) ∧ ((((False ∧ p5) → p3) ∨ (p2 ∨ p3)) ∧ (p4 → (p5 ∨ (True → False)))))) → p2) := by
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
    let h9 := h5.left
    let h10 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h11 =>
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h12 =>
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- One of the premise coincides with the conclusion.
        exact h13
      case inr h14 =>
        -- One of the premise coincides with the conclusion.
        exact h7
  case inr h15 =>
    -- Disjunctions on the left can always be decomposed.
    cases h15
    case inl h16 =>
      -- False on the left can always be used.
      apply False.elim h16
    case inr h17 =>
      -- Disjunctions on the left can always be decomposed.
      cases h17
      case inl h18 =>
        -- Conjunctions on the left can always be decomposed.
        let h19 := h5.left
        let h20 := h5.right
        -- Disjunctions on the left can always be decomposed.
        cases h19
        case inl h21 =>
          -- One of the premise coincides with the conclusion.
          exact h7
        case inr h22 =>
          -- Disjunctions on the left can always be decomposed.
          cases h22
          case inl h23 =>
            -- One of the premise coincides with the conclusion.
            exact h23
          case inr h24 =>
            -- One of the premise coincides with the conclusion.
            exact h7
      case inr h25 =>
        -- Conjunctions on the left can always be decomposed.
        let h26 := h5.left
        let h27 := h5.right
        -- Disjunctions on the left can always be decomposed.
        cases h26
        case inl h28 =>
          -- One of the premise coincides with the conclusion.
          exact h7
        case inr h29 =>
          -- Disjunctions on the left can always be decomposed.
          cases h29
          case inl h30 =>
            -- One of the premise coincides with the conclusion.
            exact h30
          case inr h31 =>
            -- One of the premise coincides with the conclusion.
            exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338346114625174115312092072226 : (p1 → (((p5 ∧ (p3 ∨ p4)) ∧ p2) ∨ (p4 ∨ ((False → (p3 ∧ ((p1 → p5) ∧ p2))) ∧ (((p2 → (p1 ∨ p3)) ∧ (p2 → True)) → p1))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h2
  -- False on the left can always be used.
  apply False.elim h2
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_196390298475956320746486174671 : ((True → (((p5 ∨ p1) → (p1 → p1)) ∨ p4)) ∧ (((True ∧ p3) ∨ ((p5 → p3) ∧ (p3 → p4))) → ((p5 ∧ ((p4 → p2) ∨ p5)) ∨ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- One of the premise coincides with the conclusion.
    exact h5
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
theorem thm_5_vars_198844862122026189816013398853 : ((p1 → (p4 ∨ (p3 ∧ (p3 ∨ (p4 ∧ p5))))) ∨ ((p2 → True) ∨ (p2 → (((p1 ∨ p1) ∨ ((True ∨ ((False → False) ∧ p4)) ∨ p4)) ∨ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49221232630961257746331878146 : ((((p2 → p5) ∧ (False ∧ (((False ∨ (p3 ∨ p3)) → p5) → (False ∧ ((p5 ∨ p5) → ((False ∨ p1) ∧ True)))))) ∨ (True → (p2 ∨ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62732245389083844214317113626 : ((p4 ∧ ((p3 ∧ (p5 ∨ ((((p5 ∨ p5) ∧ (True ∨ (p2 → p1))) → (True ∨ (p2 → ((p2 ∧ p5) ∨ p1)))) ∧ p4))) ∧ (True → p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58206828524392782954979824509 : (((p4 ∧ False) ∧ (p1 ∧ (((p3 ∨ (p1 ∧ p3)) ∨ (p5 ∧ ((((False ∨ p5) ∧ ((p2 ∧ (p1 → True)) ∧ p5)) → p1) ∨ p4))) ∧ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147044962984638106786988891590 : ((((p1 → ((p5 ∨ p4) ∨ ((p5 → False) → ((True ∧ p4) ∨ p5)))) ∨ ((False → False) ∨ (p3 ∨ p5))) ∧ p2) ∨ ((p2 → p2) ∨ (False ∧ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37211529182481665967053983759 : ((((((p2 ∧ True) → p2) ∧ (False ∧ ((((p1 ∨ True) ∧ p5) ∧ (((p3 ∨ True) ∧ (p4 ∨ (p4 → p3))) → p5)) → p2))) ∧ p3) ∧ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308616807637143149059314570814 : (p2 ∨ (((False ∨ p4) ∨ (((False ∧ p5) ∨ p4) ∨ ((True ∨ ((((True ∧ False) ∧ p5) ∧ p3) ∨ ((False ∨ False) ∧ (p2 ∨ p4)))) ∨ p5))) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_702295524176095278812647464746 : (((((False ∨ (p5 ∧ (((p1 ∧ p3) → p5) ∧ True))) ∧ p4) ∨ (((p2 ∧ True) ∨ ((p4 → ((p5 → (p2 ∧ p5)) ∨ True)) → p2)) → p2)) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h6 : (p4 → ((p5 → (p2 ∧ p5)) ∨ True)) := by
      -- Implications on the right can always be decomposed.
      intro h7
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h8 := h5 h6
    -- One of the premise coincides with the conclusion.
    exact h8
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_711175622170183445239700492288 : ((((p2 ∧ (True ∨ ((p4 ∨ p2) → p3))) ∧ (p2 ∧ ((True ∧ (p5 ∧ p5)) ∧ (p1 ∨ (True ∧ ((p1 ∨ (True → p4)) ∧ (p4 ∧ p4))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_722735430326174032486520924997 : (((((p4 → True) ∧ p4) ∧ (((p2 ∨ (p4 → (p2 ∨ True))) → (p3 ∨ (((p3 ∧ (p1 ∧ p5)) ∨ True) ∧ (p3 ∨ p1)))) ∧ (False ∧ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54416396245938652653468880273 : (((((((p5 ∨ p1) ∨ p5) ∧ p4) ∧ p5) ∨ p3) ∨ ((p5 → (p5 → True)) ∨ (((p4 ∧ ((p4 ∧ False) ∧ p5)) ∨ (p2 ∧ p4)) → True))) ∨ False) := by
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
theorem thm_5_vars_312743753106041519284723024044 : (p3 ∨ (((((((p4 ∨ p1) ∨ p1) ∨ (False ∨ p2)) ∨ p3) ∧ p5) → (p2 ∨ (((p3 ∨ (p3 ∧ ((p5 ∧ p3) → p1))) → p1) → p5))) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Disjunctions on the left can always be decomposed.
        cases h6
        case inl h7 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h8
          -- One of the premise coincides with the conclusion.
          exact h3
        case inr h9 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h10
          -- One of the premise coincides with the conclusion.
          exact h3
      case inr h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h12
        -- One of the premise coincides with the conclusion.
        exact h3
    case inr h13 =>
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h14 =>
        -- False on the left can always be used.
        apply False.elim h14
      case inr h15 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h15
  case inr h16 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h17
    -- One of the premise coincides with the conclusion.
    exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304735510635388833532018727723 : (p1 ∨ (((p3 ∧ (p1 → ((p3 ∧ p2) ∧ (p3 → p2)))) → (((p5 ∨ (p3 ∧ (p3 ∧ False))) → (p5 → p3)) → (p1 → p4))) ∨ (True ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_605217282814302294731324066050 : ((((p2 → (False ∧ (((p2 ∧ (True ∨ p1)) → p4) → ((((p2 → p3) → p1) ∧ p3) ∧ ((p4 ∨ p4) → (True ∧ (p3 ∨ True))))))) ∧ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48083067308918053429957886506 : ((((p3 ∨ ((False → False) ∧ (p5 ∨ p2))) ∨ ((p5 → (p1 ∨ (p1 ∧ (p2 → (p1 → p5))))) ∧ (p1 ∧ (p2 ∨ p5)))) → (False ∧ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172003553181631742377166308718 : ((((False ∨ ((True → p2) → ((False ∨ (p5 → p2)) ∨ p5))) → p1) ∨ (p1 ∧ p3)) ∨ (((False ∨ p5) ∨ ((p1 → p4) ∨ p2)) ∨ (p2 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_262499518220743225660876453244 : (True ∧ ((p2 → ((((p5 ∨ ((False ∧ (p4 ∧ p3)) → ((False ∨ True) ∨ ((p3 → (p3 ∨ True)) ∨ p4)))) → p3) ∨ (p2 → True)) ∧ p2)) ∨ p1)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114428362435959924922810870903 : (((p3 ∧ (False ∧ ((p1 → ((True → p5) ∨ p3)) ∧ (((True ∨ (p3 ∧ False)) ∧ False) ∨ p1)))) ∨ (p2 ∧ ((True → True) ∨ p5))) ∨ (False → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67342918340195096440275272046 : ((p1 → ((((p1 → (p4 ∨ (False ∧ p2))) ∧ True) → ((((p5 ∨ False) ∨ (p3 → (p1 → True))) ∨ ((True ∧ False) → p4)) → p5)) ∨ True)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149233799604947948476568214641 : (((p5 ∧ p3) ∨ (((p1 ∨ (((((p3 ∧ p1) → False) → False) ∨ p5) → ((True ∨ p2) → p1))) ∧ p1) ∧ p5)) ∨ ((False ∨ (True ∨ p5)) ∨ p2)) := by
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
theorem thm_5_vars_317858591494627770766750341002 : (p4 ∨ (((True ∧ p3) ∨ (((((p5 → ((p3 ∧ (((p4 ∧ False) ∧ p1) → (True ∨ p1))) → p1)) ∨ (p2 ∧ p1)) → p1) → p1) ∨ True)) ∨ False)) := by
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
theorem thm_5_vars_199066634636066986033930211892 : ((((((p1 → p1) ∧ True) ∨ False) → False) ∧ True) → (((p5 ∨ p3) ∧ p2) → (((False ∧ (p5 → (p5 ∧ p1))) ∧ p1) ∧ ((True ∨ p5) ∧ False)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h1.left
    let h7 := h1.right
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h8 : (((p1 → p1) ∧ True) ∨ False) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h9
      -- One of the premise coincides with the conclusion.
      exact h9
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h10 := h6 h8
    -- False on the left can always be used.
    apply False.elim h10
  case inr h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h1.left
    let h13 := h1.right
    -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
    have h14 : (((p1 → p1) ∧ True) ∨ False) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h15
      -- One of the premise coincides with the conclusion.
      exact h15
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h12, we can now drive its conclusion.
    let h16 := h12 h14
    -- False on the left can always be used.
    apply False.elim h16
  -- Implications on the right can always be decomposed.
  intro h17
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h18 := h2.left
  let h19 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h18
  case inl h20 =>
    -- Conjunctions on the left can always be decomposed.
    let h21 := h1.left
    let h22 := h1.right
    -- One of the premise coincides with the conclusion.
    exact h20
  case inr h23 =>
    -- Conjunctions on the left can always be decomposed.
    let h24 := h1.left
    let h25 := h1.right
    -- One of the premise coincides with the conclusion.
    exact h17
  -- Conjunctions on the left can always be decomposed.
  let h26 := h2.left
  let h27 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h26
  case inl h28 =>
    -- Conjunctions on the left can always be decomposed.
    let h29 := h1.left
    let h30 := h1.right
    -- We want to use the implication h29 based on <expert-advice>. So we show its premise.
    have h31 : (((p1 → p1) ∧ True) ∨ False) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h32
      -- One of the premise coincides with the conclusion.
      exact h32
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h29, we can now drive its conclusion.
    let h33 := h29 h31
    -- False on the left can always be used.
    apply False.elim h33
  case inr h34 =>
    -- Conjunctions on the left can always be decomposed.
    let h35 := h1.left
    let h36 := h1.right
    -- We want to use the implication h35 based on <expert-advice>. So we show its premise.
    have h37 : (((p1 → p1) ∧ True) ∨ False) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h38
      -- One of the premise coincides with the conclusion.
      exact h38
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h35, we can now drive its conclusion.
    let h39 := h35 h37
    -- False on the left can always be used.
    apply False.elim h39
  -- Conjunctions on the left can always be decomposed.
  let h40 := h2.left
  let h41 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h40
  case inl h42 =>
    -- Conjunctions on the left can always be decomposed.
    let h43 := h1.left
    let h44 := h1.right
    -- We want to use the implication h43 based on <expert-advice>. So we show its premise.
    have h45 : (((p1 → p1) ∧ True) ∨ False) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h46
      -- One of the premise coincides with the conclusion.
      exact h46
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h43, we can now drive its conclusion.
    let h47 := h43 h45
    -- False on the left can always be used.
    apply False.elim h47
  case inr h48 =>
    -- Conjunctions on the left can always be decomposed.
    let h49 := h1.left
    let h50 := h1.right
    -- We want to use the implication h49 based on <expert-advice>. So we show its premise.
    have h51 : (((p1 → p1) ∧ True) ∨ False) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h52
      -- One of the premise coincides with the conclusion.
      exact h52
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h49, we can now drive its conclusion.
    let h53 := h49 h51
    -- False on the left can always be used.
    apply False.elim h53
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h54 := h2.left
  let h55 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h54
  case inl h56 =>
    -- Conjunctions on the left can always be decomposed.
    let h57 := h1.left
    let h58 := h1.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h59 =>
    -- Conjunctions on the left can always be decomposed.
    let h60 := h1.left
    let h61 := h1.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h62 := h2.left
  let h63 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h62
  case inl h64 =>
    -- Conjunctions on the left can always be decomposed.
    let h65 := h1.left
    let h66 := h1.right
    -- We want to use the implication h65 based on <expert-advice>. So we show its premise.
    have h67 : (((p1 → p1) ∧ True) ∨ False) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h68
      -- One of the premise coincides with the conclusion.
      exact h68
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h65, we can now drive its conclusion.
    let h69 := h65 h67
    -- False on the left can always be used.
    apply False.elim h69
  case inr h70 =>
    -- Conjunctions on the left can always be decomposed.
    let h71 := h1.left
    let h72 := h1.right
    -- We want to use the implication h71 based on <expert-advice>. So we show its premise.
    have h73 : (((p1 → p1) ∧ True) ∨ False) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h74
      -- One of the premise coincides with the conclusion.
      exact h74
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h71, we can now drive its conclusion.
    let h75 := h71 h73
    -- False on the left can always be used.
    apply False.elim h75



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158122333920754726139820587426 : (((False → ((p4 → p5) ∧ False)) ∧ (((((((p2 ∧ False) ∧ True) ∨ p1) ∨ p4) ∧ p5) ∨ False) ∨ True)) ∨ ((False → ((False → p5) → False)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_585551706968117609417377769075 : (((((((p3 → (p3 ∨ (p2 ∧ (False ∨ (p3 ∧ (p4 ∧ p3)))))) ∧ (((False ∧ (p4 ∧ p3)) ∧ p5) ∧ (p4 ∧ p5))) ∨ p4) ∧ p2) ∧ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245103208280476443211800122602 : ((p2 ∧ True) ∨ ((True → (False ∨ ((p1 ∨ (p1 ∨ (((p1 ∨ True) ∨ ((p5 → ((p2 → p3) ∧ True)) ∧ False)) ∨ (p1 → p1)))) ∨ p5))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_752291037764738731616694604001 : (((True ∧ (p5 → (p4 ∧ ((p4 ∨ (p2 → ((p1 ∨ False) ∧ (p4 ∧ p1)))) → (p5 → ((True ∧ ((p2 → p5) ∨ (p2 → True))) ∧ p1)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112936412484482721788950516241 : ((((p5 ∨ p2) → (((p2 → p5) ∨ (p3 → (p1 → p4))) ∨ (False ∧ ((p5 ∨ (((False ∧ True) ∨ p3) ∨ p2)) ∧ p1)))) → p3) ∨ (p5 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118799870093548377407824295554 : ((True → (((False ∨ (((p3 ∨ (((True ∨ (p3 ∨ True)) → p5) ∨ ((p4 ∨ True) ∧ True))) ∧ False) ∧ True)) ∧ (p2 ∧ p5)) ∧ p4)) ∨ (False → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263769384897777969186937221054 : (True ∧ (((((False ∨ p1) → p5) → p1) ∨ (((True → ((p3 ∧ p2) ∨ True)) ∧ p5) ∨ True)) ∧ (True → (p4 → (p4 ∨ ((p5 ∧ p1) → p2)))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134453167210341828864868262333 : (((((True → ((p1 → (((p3 ∨ p2) ∧ ((p2 ∨ False) ∨ p3)) ∧ p5)) → p2)) ∨ (False → (True ∧ True))) ∧ True) → p5) ∨ (True ∨ (p5 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_636988393906175186866332988779 : ((((((p5 ∨ ((True ∨ (p2 ∨ True)) → p4)) → ((True → p5) ∧ p3)) ∧ ((((p1 ∨ (True → p2)) → (p4 ∧ True)) → p3) → p4)) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173563241640539777447913184903 : ((((p2 ∧ p1) ∧ (p1 → ((((p5 ∧ p5) ∨ False) → (p3 ∨ p3)) → p5))) ∧ True) → ((p4 ∨ p2) → (((p4 ∨ (p2 → p4)) ∨ p1) ∧ True))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h6.left
    let h9 := h6.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h9
  case inr h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h1.left
    let h12 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h13 := h11.left
    let h14 := h11.right
    -- Conjunctions on the left can always be decomposed.
    let h15 := h13.left
    let h16 := h13.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h16
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173886851621689680327861364200 : ((((((p5 ∨ p1) ∨ True) ∧ (((p2 ∧ p5) ∨ False) → (True → p5))) ∨ True) → p3) → ((((p3 → (False ∧ (p3 ∧ False))) ∨ p4) → p5) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((((p5 ∨ p1) ∨ True) ∧ (((p2 ∧ p5) ∨ False) → (True → p5))) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_707010144105648710571789017746 : (((((p5 ∧ ((False ∧ (p1 ∨ p4)) → False)) ∨ p4) ∨ (((((p2 ∨ p5) ∨ (p2 → True)) → p3) ∨ p2) ∨ ((False ∨ False) → (p5 ∧ False)))) ∨ p4) ∧ True) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- False on the left can always be used.
    apply False.elim h2
  case inr h3 =>
    -- False on the left can always be used.
    apply False.elim h3
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h4 =>
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177337436249825299702077347891 : ((p3 ∨ ((True ∨ (((False ∨ p5) ∨ p3) ∧ (False ∨ (p5 → p1)))) ∨ p4)) ∧ ((p5 ∨ (False ∨ ((((p5 ∧ True) ∨ p3) ∨ True) ∨ p2))) ∨ p2)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_306179966706373846845849993115 : (p1 ∨ ((p3 ∧ (p3 ∧ p2)) ∨ ((p4 → False) ∨ ((False ∧ (((p2 ∧ (p5 → p3)) ∧ False) ∨ (p4 → ((True ∨ True) ∨ (p5 → False))))) → p2)))) := by
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
theorem thm_5_vars_662273836547447432890523217787 : (((((((p1 ∧ (p4 ∨ ((p4 ∧ p2) → p4))) ∧ p3) → p4) → ((p3 ∧ (((p2 → (True ∧ p3)) → p5) → False)) → p2)) → (p1 → p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_617970432100141539367955503 : ((((((p2 ∨ ((p5 → p1) ∧ (p5 ∨ (p4 ∨ ((p5 ∧ p3) ∧ (False ∧ p3)))))) → (p5 ∧ True)) ∨ p4) → p4) ∨ (p4 ∧ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256867021576868071505356370472 : ((p1 ∨ p3) → (p4 ∨ ((((p2 ∨ ((p4 → p5) ∨ (((False → p5) → (p5 ∨ ((p3 → p3) ∨ p2))) → True))) ∨ p1) ∧ p3) → (False ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h8 =>
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
  case inr h12 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h13
    -- Conjunctions on the left can always be decomposed.
    let h14 := h13.left
    let h15 := h13.right
    -- Disjunctions on the left can always be decomposed.
    cases h14
    case inl h16 =>
      -- Disjunctions on the left can always be decomposed.
      cases h16
      case inl h17 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h18 =>
        -- Disjunctions on the left can always be decomposed.
        cases h18
        case inl h19 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h20 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
    case inr h21 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67695283844790317329027252034 : ((p1 → (p3 → (p2 → (((((p3 → (((p2 ∨ p2) ∧ True) ∨ p4)) ∧ p2) → ((True → ((p2 → p2) ∧ p4)) ∨ p3)) → p4) ∨ p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56888352505327352465355146513 : (((p3 ∧ (p1 ∧ p2)) ∧ (((False ∧ True) ∨ (False ∨ (((False ∧ p2) ∨ False) ∨ p2))) → (False ∨ (p3 → (((p1 ∨ p2) ∧ False) ∧ True))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215107024513206395510222499059 : (((p2 → True) → (p4 ∧ p5)) ∨ ((p4 ∧ (True → (((False ∧ True) ∧ p4) ∨ ((False ∧ p5) ∨ (p1 ∨ p2))))) ∨ (((p5 ∨ True) ∨ p2) ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_308574406035101378642728250797 : (p2 ∨ (((((True ∨ p2) → p1) ∨ p5) ∨ ((True ∧ (p2 ∧ p3)) ∨ (((False → (p4 → (p2 ∧ True))) ∧ (p1 ∧ True)) ∨ (False ∧ p1)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309936240192064336843013427425 : (p2 ∨ ((p3 ∧ (((((p1 → (False ∨ (p2 → p3))) → (False ∧ False)) → p2) → (p5 ∨ p3)) ∧ p4)) ∨ (p2 → (p4 → (p3 → (True → p4)))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h4
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_787663265941096918753404570539 : (((p4 ∨ (p4 ∨ (((p5 ∧ ((p3 → (False ∧ p4)) ∧ p5)) ∧ (((p4 ∨ (p1 → (p2 ∨ (p3 ∨ p3)))) ∨ p1) ∧ (p3 → p4))) → p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215536917333413260405171774009 : ((p4 ∧ (True → (p5 ∧ p4))) ∨ ((p1 → (((True ∧ ((((False ∧ True) → True) → True) → p5)) ∧ p1) → (((p4 ∧ False) ∧ p3) ∨ p1))) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173221674486381267970052991987 : ((p5 ∨ (True → ((p1 ∨ (((p1 ∨ (False ∨ p4)) ∧ p5) ∨ p2)) ∧ (True ∧ p2)))) ∨ (p3 → ((p4 ∨ (p4 → ((p4 ∨ p5) ∧ p4))) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_146971520783185375560031477267 : (((((p4 ∧ (((p3 ∧ True) ∨ p1) ∧ (((((p2 → True) → True) ∨ False) ∨ p3) ∨ p3))) → p1) → p2) ∧ p4) ∨ (((p3 ∧ p1) ∨ p5) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135060933679217930654237115768 : (((((((p3 ∨ p4) → (p3 ∧ p3)) ∨ False) → (False ∧ (((p5 ∧ (p5 → p2)) → p4) ∨ p4))) → False) ∨ (p5 → p5)) ∨ ((p5 ∧ False) ∨ p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_4452672099936843392525909750 : (p2 → ((p2 → ((p2 → False) → ((False ∧ ((((p2 ∨ (p2 → (False ∧ (p3 ∨ False)))) ∧ (True ∧ p4)) ∧ p3) ∧ p1)) ∨ False))) ∨ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : p2 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117706074750648085364568332315 : ((p3 ∧ (p2 ∧ ((((p1 ∧ True) ∨ (p4 ∧ p2)) ∧ ((((p1 ∨ p3) ∨ False) → False) ∧ False)) ∨ (p2 → ((p1 ∨ p5) → p2))))) ∨ (p2 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_90919865093648893496500280404 : (((True → False) ∧ (((p2 → (p3 ∧ (p5 ∧ (p3 ∨ False)))) ∧ (((p1 → p5) ∧ p3) → (((p1 ∨ p3) ∨ p3) ∨ p4))) ∧ (p2 → p3))) → p2) := by
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
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h8 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h9 := h2 h8
  -- False on the left can always be used.
  apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149865200625960825087947332035 : ((p2 ∨ (((p1 ∧ ((p3 ∧ (False → True)) → (p1 ∧ p5))) ∧ (((p5 ∨ p1) ∧ (p1 ∧ p4)) ∧ p3)) ∨ p2)) ∨ (p3 → (False ∨ (True ∨ False)))) := by
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
theorem thm_5_vars_234075404034218558699568232502 : ((True → (p1 ∧ False)) → (((p3 → (True ∨ ((True → False) ∧ p3))) ∧ ((True ∨ ((p2 ∨ ((False ∧ p2) ∧ (p2 ∨ p2))) ∧ p4)) ∧ p3)) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303278899290247417203942511922 : (False ∨ (p5 → (p5 → (p5 ∧ ((((p1 ∨ p3) ∧ p1) ∨ p4) ∨ ((((p1 → True) ∧ p2) → ((p4 → p4) ∧ True)) → (p3 → (p4 → True)))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260666259508244877712174510810 : ((p3 → p3) → (((p2 ∧ True) → ((p1 → ((p3 ∨ (p5 ∨ False)) ∨ (p4 → (p1 → p4)))) ∧ p3)) ∨ (((False ∨ p2) ∧ (True ∨ p4)) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157485461421065298370971283934 : ((((((((p4 ∧ p4) ∧ p4) → p2) → p3) → True) ∧ (((p5 → p1) ∨ p4) → p5)) ∨ (p5 ∧ p4)) ∨ (p4 → ((p5 ∧ (p1 ∨ p1)) → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
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
    -- One of the premise coincides with the conclusion.
    exact h6



