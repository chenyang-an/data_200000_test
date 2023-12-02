variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191439167540902604844757258236 : (((p5 ∨ p2) → ((p3 → (p2 ∧ (True ∧ p1))) → p1)) ∨ (p3 → (((False → p2) → (p3 ∧ (False ∨ (True → ((True → p1) ∨ p2))))) ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116450245025501926418072248342 : (((True ∧ True) ∧ (p5 ∧ (p2 ∧ (p2 ∧ ((p5 ∨ p1) ∨ (((p2 ∨ (p4 → p5)) ∨ ((p4 ∨ p1) → True)) → (True → p2))))))) ∨ (False → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_804110282145401383228130998321 : (((p3 → ((((p2 → ((((p2 ∧ (p4 ∧ True)) ∧ p1) ∨ (p5 ∧ (p3 ∧ p3))) → p1)) ∧ False) ∨ p1) ∨ (p4 ∧ (p4 ∧ (p4 ∨ p2))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356611053813134194750273205436 : (p5 → (((((p2 ∧ p3) ∧ (p4 → p3)) ∨ p2) ∧ p2) ∨ (True ∨ (((p5 ∨ p3) ∧ (((p4 → True) → (p5 → (p2 ∧ p3))) ∨ False)) ∨ p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_170956738897658997382387525587 : ((p1 ∨ (False ∨ ((((p4 ∨ p4) → (p5 → p1)) → ((p2 → p3) → True)) ∨ p3))) ∧ ((((p5 ∨ p2) ∧ p4) ∧ (p1 ∧ (p1 → False))) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_381754798834930799585732484059 : (((((((True → (False ∨ ((p1 ∨ p2) → ((((p4 ∧ True) ∧ p3) ∨ (p5 ∨ (p4 ∧ p3))) → p5)))) ∨ (p5 → p2)) ∨ True) ∨ p5) ∨ p1) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_255206373277350018662051190682 : ((p4 ∧ p4) → (((p5 ∨ p5) ∧ ((p3 ∨ (p2 → True)) ∨ False)) → ((p4 → False) ∨ (((((p4 ∨ p1) ∧ (p2 ∧ p1)) ∨ p2) → p3) ∨ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Conjunctions on the left can always be decomposed.
        let h8 := h1.left
        let h9 := h1.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h5
      case inr h10 =>
        -- Conjunctions on the left can always be decomposed.
        let h11 := h1.left
        let h12 := h1.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h5
    case inr h13 =>
      -- False on the left can always be used.
      apply False.elim h13
  case inr h14 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h15 =>
      -- Disjunctions on the left can always be decomposed.
      cases h15
      case inl h16 =>
        -- Conjunctions on the left can always be decomposed.
        let h17 := h1.left
        let h18 := h1.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h14
      case inr h19 =>
        -- Conjunctions on the left can always be decomposed.
        let h20 := h1.left
        let h21 := h1.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h14
    case inr h22 =>
      -- False on the left can always be used.
      apply False.elim h22



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_618327176910571153820011835030 : (((((p1 ∧ ((p5 → False) ∧ True)) ∨ (((((True ∧ p2) → False) ∧ False) ∧ p5) ∧ ((p3 → (p5 ∧ ((p2 ∧ p5) → p4))) ∧ p1))) ∨ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341968288180841245610702497442 : (p2 → ((((((p4 ∨ p3) ∨ (p5 → p1)) ∧ (p4 ∨ (True ∧ p2))) ∨ ((((p1 ∧ p2) ∧ p1) ∧ p5) ∧ p4)) ∨ p5) ∨ (p1 → (p1 ∧ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215112266808983812201422660084 : (((p2 → p2) → (p4 ∨ p4)) ∨ (p3 ∨ (True ∧ ((False → p2) ∨ (True ∨ (((p4 ∨ False) ∨ p1) → (p2 ∧ (p3 → (True ∨ (p3 ∧ p3)))))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_644422803057749531462582095965 : ((((False ∨ (False ∨ ((((p1 ∧ False) ∨ ((p1 → ((p5 → p1) ∨ p2)) → (p5 ∧ p2))) ∧ ((p1 ∨ p1) → p2)) ∨ (p1 ∧ p1)))) → False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134943573113296773062771739593 : (((((p1 → (p2 → (((p1 ∧ False) ∨ p3) ∨ ((p3 ∧ False) ∨ (p5 ∧ False))))) ∧ True) → (p4 ∧ p2)) ∧ (p2 → False)) ∨ (p2 ∨ (True ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227740331156336480564169186526 : ((p1 ∧ (p1 ∨ p2)) ∨ (p2 ∨ ((p1 ∧ (((True ∨ p5) ∧ p5) ∧ ((p4 ∧ False) → p2))) ∨ ((((p5 → p1) → p1) ∨ p1) → (True ∧ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_208336805981782430054128705306 : (((p3 → p1) ∧ (p4 ∧ (p4 ∨ True))) → ((p3 ∨ p5) ∨ ((p3 ∨ (p3 ∧ (p5 → ((False → (p4 ∧ p4)) ∧ p1)))) → ((p5 → p1) ∧ p4)))) := by
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
    -- Implications on the right can always be decomposed.
    intro h7
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h8
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h9 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h10 : p3 := by
        -- One of the premise coincides with the conclusion.
        exact h9
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h11 := h2 h10
      -- One of the premise coincides with the conclusion.
      exact h11
    case inr h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h12.left
      let h14 := h12.right
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h15 : p3 := by
        -- One of the premise coincides with the conclusion.
        exact h13
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h16 := h2 h15
      -- One of the premise coincides with the conclusion.
      exact h16
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h17 =>
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h18 =>
      -- Conjunctions on the left can always be decomposed.
      let h19 := h18.left
      let h20 := h18.right
      -- One of the premise coincides with the conclusion.
      exact h6
  case inr h21 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h22
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h23
    -- Disjunctions on the left can always be decomposed.
    cases h22
    case inl h24 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h25 : p3 := by
        -- One of the premise coincides with the conclusion.
        exact h24
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h26 := h2 h25
      -- One of the premise coincides with the conclusion.
      exact h26
    case inr h27 =>
      -- Conjunctions on the left can always be decomposed.
      let h28 := h27.left
      let h29 := h27.right
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h30 : p3 := by
        -- One of the premise coincides with the conclusion.
        exact h28
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h31 := h2 h30
      -- One of the premise coincides with the conclusion.
      exact h31
    -- Disjunctions on the left can always be decomposed.
    cases h22
    case inl h32 =>
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h33 =>
      -- Conjunctions on the left can always be decomposed.
      let h34 := h33.left
      let h35 := h33.right
      -- One of the premise coincides with the conclusion.
      exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323780941679325288869555415576 : (p5 ∨ (((((p5 → p1) ∨ ((((True ∧ p2) ∨ (p5 → True)) → p5) → (p2 ∧ False))) ∨ False) ∨ True) ∨ ((p3 ∨ ((p3 → p1) ∨ p3)) ∧ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159486542410338536933683252368 : ((((((p4 → True) ∨ True) → p2) → ((p1 → (((p2 → False) ∨ False) ∨ p2)) → (p2 → p3))) ∧ p5) → ((p1 → (False ∧ (p4 ∧ p2))) ∨ True)) := by
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
theorem thm_5_vars_39460063205532391799456196971 : (((p5 ∧ (True ∧ (p5 ∨ (p4 ∧ (((p4 ∨ ((p5 → ((p2 ∧ p1) → p1)) ∨ p4)) ∨ (p2 ∨ p1)) ∧ ((p4 ∧ True) ∧ p3)))))) ∧ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_682237525015140889008857840036 : (((((True → ((p1 ∧ p4) ∨ (((p4 → p5) → ((True → p1) ∨ (True → p1))) ∧ p5))) → p1) ∧ (((False → p4) → (False ∨ True)) ∨ True)) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
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
    -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
    have h10 : (p4 → p5) := by
      -- Implications on the right can always be decomposed.
      intro h11
      -- One of the premise coincides with the conclusion.
      exact h9
    -- We have shown the premise of h8, we can now drive its conclusion.
    let h12 := h8 h10
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h13 =>
      -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
      have h14 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h13, we can now drive its conclusion.
      let h15 := h13 h14
      -- One of the premise coincides with the conclusion.
      exact h15
    case inr h16 =>
      -- We want to use the implication h16 based on <expert-advice>. So we show its premise.
      have h17 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h16, we can now drive its conclusion.
      let h18 := h16 h17
      -- One of the premise coincides with the conclusion.
      exact h18
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_624887819865172794458119011637 : ((((p5 ∨ (((p2 ∨ (p1 ∧ p1)) ∨ ((p2 → p1) ∨ p2)) → (p4 ∨ ((p3 ∧ (False ∨ p2)) → (p2 ∧ ((p1 ∨ True) ∨ p1)))))) ∨ True) ∨ False) ∧ True) := by
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
theorem thm_5_vars_645034516914807611852303062236 : ((((p3 ∨ ((((True → ((True → p2) → p2)) ∧ p1) → (p1 ∨ ((((p3 ∨ True) ∧ p3) → ((False ∧ p2) → p1)) → p3))) ∧ True)) → False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_662720694343421732733792421603 : (((((p3 ∨ (p2 → (p4 → p2))) ∨ ((((True ∧ (p3 → (p3 ∨ p5))) → (p4 → p2)) ∨ False) ∨ (p3 ∨ (True ∧ p3)))) → (p2 ∨ True)) ∨ p1) ∧ True) := by
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
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h4 =>
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
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h8 =>
        -- False on the left can always be used.
        apply False.elim h8
    case inr h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114361669100037020178534738314 : (((((p2 → p1) ∧ ((((p3 ∨ False) ∧ p4) ∨ p4) ∨ (True ∧ (True ∨ (True → p3))))) ∧ p4) ∨ ((p1 ∧ (p2 ∧ True)) → True)) ∨ (p4 → p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217838853801351076592794933276 : (((p4 ∨ (p4 → True)) → p2) → (((((p2 ∨ True) ∨ (p1 ∧ p1)) ∧ (p1 ∧ True)) ∨ (p1 ∧ p3)) ∨ ((p1 ∧ p1) ∨ (p5 → (True ∧ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51328840563029365536599436969 : (((p1 → (((((False ∧ False) → False) ∨ ((False ∨ p5) ∧ ((p5 ∨ p2) ∧ p3))) → True) → p3)) ∨ ((True ∨ (p2 ∨ p2)) ∨ (p5 → p1))) ∨ False) := by
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
theorem thm_5_vars_217987418529973547058043025847 : (((p4 ∧ p1) ∧ (False → True)) → (((((((p3 ∧ p4) ∧ False) ∨ p3) → p4) → (p4 ∧ p2)) ∧ ((((p1 ∨ p4) → p1) → p1) → True)) ∨ p1)) := by
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
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49181077844170664513571824192 : (((((p1 → False) ∨ (p2 ∨ False)) ∨ ((p4 ∧ p4) → (((p3 ∧ True) → p4) ∧ (p4 → (p1 ∧ (p1 ∧ p5)))))) ∨ (False ∧ (p2 ∨ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62339731559881045744708351943 : ((p3 ∧ (((p5 ∨ (((p1 ∧ p1) → ((p5 → ((True ∧ p5) ∧ (p5 → p3))) ∨ False)) ∨ p5)) ∧ (p3 ∨ True)) ∨ (p1 ∧ (p1 ∨ p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118661202078110805733587139954 : ((p4 ∨ (p2 ∨ (((p5 ∧ p1) ∧ (p5 ∨ (p2 ∨ (((p4 ∨ (True → False)) ∨ ((p2 ∨ p2) ∨ False)) → (False ∧ p5))))) ∧ True))) ∨ (True ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215910810097253883018225504575 : ((p3 ∨ ((p5 → p1) → p3)) ∨ (((False ∨ p2) ∨ ((p5 → (p2 ∧ p2)) → p5)) ∨ (False → ((True ∧ p1) ∨ ((p2 → True) ∨ (p3 → False)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116742496066463903926684658656 : (((p4 ∧ p3) ∨ ((((((True ∧ True) ∧ p1) ∧ True) ∧ p4) ∧ (p5 ∧ (False ∨ (p4 ∨ p4)))) ∨ ((p5 → p1) → (False ∧ p5)))) ∨ (True ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207518739963446340052061774096 : (((((p2 ∧ p5) → p4) ∧ False) → p1) → (((p4 ∧ True) ∧ (((True ∨ (p4 ∨ p1)) → p5) → ((((False ∨ p1) → p2) ∨ p5) → False))) → p4)) := by
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
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137922652177393638531219072966 : ((p4 ∨ (True ∧ (True → ((((((p4 ∧ (p2 → p2)) ∧ (p5 ∨ ((p1 ∨ p5) → p1))) → p2) ∧ True) → p3) → p4)))) ∨ (p5 ∨ (p2 → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308589338379231391489809105756 : (p2 ∨ ((((p4 ∨ p4) ∧ False) ∨ ((((((p2 → False) ∧ (p2 → True)) ∧ p2) ∧ ((p3 ∨ p2) → p5)) ∨ p1) → ((p1 ∧ p1) ∨ p2))) ∨ p3)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- Conjunctions on the left can always be decomposed.
    let h5 := h3.left
    let h6 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h9 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h9
    -- One of the premise coincides with the conclusion.
    exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117903501082824508772419356903 : ((p5 ∧ (((((p3 → p3) ∨ True) → ((p2 → p2) ∧ ((p3 → p5) ∧ p3))) ∧ True) ∧ ((((p1 ∨ p4) ∨ False) → p3) ∧ p4))) ∨ (False ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_635309899476046304216322634697 : (((((((((p3 ∧ ((p4 ∨ (True ∧ True)) ∧ (True ∨ False))) ∧ (True → p2)) ∨ False) ∧ p3) → p4) ∧ (((p5 ∧ True) ∨ True) ∧ p3)) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148655183597453972558501001309 : ((((p5 ∧ True) ∨ (((p4 → p3) ∨ p4) → p5)) ∧ (((p1 ∨ ((False ∨ p4) ∧ p3)) → p2) ∨ (p4 ∨ p4))) ∨ ((p1 ∨ True) ∨ (False ∧ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234029414242236948981379691510 : ((p5 ∨ (True → p5)) → (p4 ∨ (p1 → (((p1 → p4) ∨ (True → (False ∧ (p2 ∨ (((True ∧ p3) ∨ p5) ∧ ((p3 ∧ False) ∨ p4)))))) ∨ True)))) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231639782055235963822849406551 : (((False ∧ p2) → True) → ((((p1 ∨ ((False ∧ (False ∨ p2)) ∧ p4)) ∧ ((True → p3) → (p5 → True))) ∨ ((p4 ∧ (p3 ∨ p4)) ∧ p1)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_785366007170013912499620375934 : (((p4 ∨ ((((True ∧ (((True ∧ (True ∧ ((p1 ∨ p4) ∧ (p5 ∨ (p4 ∧ ((p5 ∨ False) ∨ p4)))))) ∨ p2) → False)) → True) → p3) ∨ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_755815990790182260487360677999 : (((p1 ∧ ((p3 → ((p4 → (False ∨ (p4 → ((p3 ∧ ((p4 → (p4 → p1)) → False)) ∧ ((False ∨ p5) ∨ (True ∧ True)))))) → p5)) ∨ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49385755702223432842028527758 : ((((((p5 → p4) ∨ ((p1 ∨ (p2 → ((p1 ∧ (True → (True ∨ p4))) ∧ p3))) ∨ (p4 → p5))) ∨ p4) ∧ p5) → (False ∨ (p4 → p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47238061922976851686146994006 : ((((((p1 → p4) ∨ (True ∨ (p4 ∧ False))) → False) → ((True ∧ p1) ∨ (((p5 ∨ p4) ∧ (p5 ∧ p5)) ∧ (p5 ∧ p5)))) ∨ (p3 ∨ p2)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p1 → p4) ∨ (True ∨ (p4 ∧ False))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55998483381816006248619627554 : ((((p3 → (p3 ∨ p3)) ∧ p2) ∨ (((p4 → ((p4 ∨ ((True → (p1 ∧ False)) → True)) → (p2 → (p2 → (p2 ∧ p3))))) ∨ p4) ∧ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157544698472041674990302812272 : ((((((p2 → p5) → ((p1 ∨ (p1 ∧ p1)) → (False ∨ (p4 ∨ p1)))) → p3) → p4) → (False ∧ p5)) ∨ ((p2 → (p2 ∧ (p2 ∨ False))) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41890880368732839804212419906 : ((((p1 → (p4 ∧ p5)) ∨ (((((p1 → (p1 ∧ p2)) → (True ∧ p4)) → p3) ∧ p2) ∨ (p2 → (p5 ∧ ((p1 ∧ p3) ∧ p2))))) ∨ True) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171421801234279404805817197041 : ((((p5 ∧ True) ∧ (p1 ∨ ((p1 ∨ ((p5 ∧ p5) ∨ (False ∧ p3))) ∧ p4))) ∧ False) ∨ ((((p2 → (p4 ∨ False)) ∨ (p3 → p4)) ∨ p5) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38357106131682247533139176367 : ((((((((p2 ∨ (False → p2)) ∨ True) ∧ p1) ∨ (((p5 ∨ p2) → p4) → p1)) ∨ p3) ∨ ((p4 → (p2 ∧ p1)) ∧ (p5 → p5))) ∧ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112354010249109771506022038560 : ((((((p3 → p2) ∨ (((((False ∧ p1) ∨ ((p2 ∨ ((p2 ∨ p2) ∧ True)) ∧ False)) ∧ p5) ∧ True) → False)) ∧ p2) ∧ p2) → p5) ∨ (p4 → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_265546369587473098918874397919 : (True ∧ (False ∨ ((p5 ∧ False) ∨ ((True → True) → (((False → (True ∨ ((p1 → ((True → False) → False)) → p2))) ∧ True) → ((p3 ∧ p4) ∨ True)))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_786631354363840453598154723335 : (((p4 ∨ ((((True → (p4 ∨ p2)) ∧ (p5 ∨ p5)) ∨ p1) → (True → (p3 ∧ ((p4 ∨ True) ∧ ((p5 → ((True ∧ p2) ∧ p5)) ∧ p3)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61799800800277785382225374769 : ((p2 ∧ ((((((p2 ∨ False) ∨ (False ∧ (((True ∨ ((p2 → p3) → p5)) ∨ p4) → p3))) ∧ p4) → (p3 ∨ (p1 ∨ p1))) ∨ p4) ∨ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64011859391094925591674667314 : ((False ∨ (((False ∨ (((p4 ∨ p5) ∧ p2) → (((((p5 ∨ p1) ∨ (p5 ∧ p4)) ∨ p4) → False) ∨ (p2 ∨ p1)))) ∨ False) ∨ (p3 → True))) ∨ p4) := by
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
theorem thm_5_vars_317817298148157624269032996759 : (p4 ∨ ((((p5 → p4) ∧ (p3 ∨ p1)) ∧ ((p4 ∨ (p2 ∨ False)) ∨ ((True ∧ (((p5 ∨ p5) ∧ True) ∨ p3)) → ((p2 ∧ p2) ∨ p5)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_600224019104855929629120550205 : (((((p1 → p5) → ((((p4 → False) ∧ p2) ∨ ((((p4 ∨ True) ∨ p5) ∨ (p1 ∧ p5)) ∧ p1)) ∧ (p1 → (p3 → (p5 ∧ p2))))) ∧ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309296768562959985945450996270 : (p2 ∨ ((((((((p1 ∨ ((p2 → True) ∧ False)) ∨ (p2 ∨ (p5 ∨ (p3 → p2)))) → (p1 ∧ p3)) → p2) → p4) ∨ True) ∧ p4) ∨ (p2 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_609234688319960656850094569945 : (((((((p5 ∨ p2) → p5) ∨ ((((p1 → p2) ∨ p5) ∨ (((p1 ∨ True) ∨ (False → p5)) → p4)) ∧ ((p5 → p2) ∧ p2))) ∨ p4) ∨ True) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_623374597108339846534540077218 : ((((False ∨ ((((p3 ∨ False) ∧ ((p1 → p4) ∨ (p3 ∧ (p3 ∨ ((p1 ∧ p2) → p5))))) ∨ ((p4 ∨ (p5 ∧ p1)) ∨ p1)) ∧ p3)) ∨ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63050323413600823298071177874 : ((p5 ∧ ((((p1 → (p5 ∨ p2)) ∧ ((p1 → (p2 ∨ p3)) ∧ p3)) ∨ (((p5 ∨ ((p3 ∨ p4) ∧ False)) ∨ (False ∧ True)) ∨ p1)) ∧ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_638165164864257337585203209284 : ((((((p4 → (False ∨ (True ∧ (p3 → p4)))) → True) → (p1 → (((p5 ∧ ((p5 ∧ p4) → (p1 ∨ p1))) → p3) → (p5 ∧ p1)))) → p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_19538928466794709495807339727 : ((((p1 → (((p1 ∨ (((False ∨ p1) ∧ False) ∨ p2)) → False) ∧ (p2 ∧ p1))) → p1) ∨ (p2 → ((True ∧ (p1 → False)) ∨ (True ∨ True)))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321207044489349580695167683070 : (p4 ∨ (p3 ∨ ((p2 ∨ p4) → (p3 ∨ ((False ∨ True) ∨ (p5 → ((False → p2) ∧ ((True ∨ ((p1 ∧ p4) → (True → p1))) ∨ (p4 ∧ p1))))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_700639444677726143899753826704 : ((((p3 → (((p3 → (True ∨ ((p4 ∧ p1) → p4))) ∨ True) ∨ p4)) → ((((p5 ∨ p3) → p4) → ((p4 ∨ (p3 ∨ p2)) ∧ p4)) ∨ True)) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_306191580145961469218527759370 : (p1 ∨ ((p3 ∨ (p4 ∨ p1)) ∨ (p3 → (p5 ∨ (True ∨ (((((p3 ∧ p4) ∧ (p2 ∧ p1)) ∨ (p3 ∧ p4)) ∨ (False → (p1 → p3))) ∧ p4)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_589530507559941937126909808260 : ((((((((p3 → p3) ∧ (((p3 → (p1 → (True ∧ True))) → (True ∨ p4)) ∧ (p2 ∧ (False → (p4 ∧ False))))) ∨ p2) → p3) → p4) ∧ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53495339465909448747159469838 : (((False ∨ ((p4 ∨ ((False → (p5 ∧ p5)) → (p1 ∨ False))) ∨ p3)) → (p5 ∨ (p1 ∧ ((((True ∧ (p5 ∨ p2)) ∨ True) ∨ p1) ∧ False)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199400515601389943004487338066 : ((((True → False) ∧ ((False ∨ p3) ∨ p2)) ∨ True) → (p4 ∨ (False ∨ (p1 → ((((False ∨ (p2 ∧ p3)) ∧ True) → ((p1 ∧ p2) ∧ p3)) ∨ p1))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- False on the left can always be used.
        apply False.elim h6
      case inr h7 =>
        -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
        have h8 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h3, we can now drive its conclusion.
        let h9 := h3 h8
        -- False on the left can always be used.
        apply False.elim h9
    case inr h10 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h11 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h12 := h3 h11
      -- False on the left can always be used.
      apply False.elim h12
  case inr h13 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h14
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_151474613837296253335048604670 : (((((((p1 → True) ∨ p1) ∨ ((p5 ∨ (p5 ∧ (p1 → False))) ∧ p4)) ∨ False) ∧ (p2 → p5)) ∨ (True ∨ p3)) → ((p1 ∧ p2) → (p3 ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h5 =>
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
        cases h9
        case inl h10 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h4
        case inr h11 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h4
      case inr h12 =>
        -- Conjunctions on the left can always be decomposed.
        let h13 := h12.left
        let h14 := h12.right
        -- Disjunctions on the left can always be decomposed.
        cases h13
        case inl h15 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h4
        case inr h16 =>
          -- Conjunctions on the left can always be decomposed.
          let h17 := h16.left
          let h18 := h16.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h4
    case inr h19 =>
      -- False on the left can always be used.
      apply False.elim h19
  case inr h20 =>
    -- Disjunctions on the left can always be decomposed.
    cases h20
    case inl h21 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h22 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h22



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53174135576362921220245474210 : (((((p1 ∧ ((p5 → (p2 → p5)) ∨ False)) ∨ (p2 ∨ p2)) → p1) ∨ (p2 ∨ (p3 → ((p2 ∨ (p1 → (p1 → p1))) → (p3 → p2))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57158759203381484033231733929 : ((((False ∧ p5) ∨ p4) ∨ ((((True ∧ (True → p5)) → ((((p4 ∨ True) ∧ p4) ∨ (p4 ∧ True)) ∨ (p3 → p2))) ∨ (p5 → p3)) ∨ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113464118048682841100522170516 : ((((((False ∧ p5) ∧ p3) → (p1 ∨ (((True ∨ (p2 → p5)) ∧ p3) ∨ ((True ∧ (p3 ∧ p4)) → True)))) → p4) ∨ (False → p4)) ∨ (p4 ∧ p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309795116577448170298497013744 : (p2 ∨ (((((p2 ∨ p5) ∧ ((p5 → p1) → p5)) ∨ (False ∨ ((p5 ∨ True) ∨ True))) ∨ (p3 → (p5 → p2))) ∨ ((p5 ∨ (True → False)) ∧ p2))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115284373474826671489773451251 : (((p4 → (p2 ∨ (((False ∧ (p4 ∧ False)) ∨ False) ∧ p1))) ∨ ((((False → ((p2 ∨ p4) ∧ True)) ∨ True) → (True ∧ p1)) → True)) ∨ (True → p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_608555215542622883662682331560 : ((((((p1 ∨ (((p4 ∨ (p1 ∧ (p2 ∧ ((((p5 ∧ p2) → (p4 ∨ (True ∧ p4))) ∨ p3) → p3)))) → False) ∨ p3)) → p4) ∨ p4) ∨ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47174115744453185143173519529 : ((((p3 ∧ ((((((p1 ∨ p4) ∧ (p4 ∨ p4)) → p2) → p3) → p1) ∧ p4)) ∨ ((((True → p5) ∧ p3) ∧ False) ∧ p4)) ∨ (True ∨ p4)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260985989664577924670575037751 : ((p4 → p1) → ((p3 ∨ True) → ((p2 ∧ (p5 ∧ p2)) ∨ ((((p1 ∨ True) → False) ∨ False) → ((p5 ∧ p2) ∨ (p2 ∨ (False ∧ (p5 ∨ False)))))))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h6 : (p1 ∨ True) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h7 := h5 h6
      -- False on the left can always be used.
      apply False.elim h7
    case inr h8 =>
      -- False on the left can always be used.
      apply False.elim h8
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h10
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
      have h12 : (p1 ∨ True) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h11, we can now drive its conclusion.
      let h13 := h11 h12
      -- False on the left can always be used.
      apply False.elim h13
    case inr h14 =>
      -- False on the left can always be used.
      apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_767490532527568032353863951811 : (((p5 ∧ ((((p1 ∧ (((True ∧ False) ∨ (((False ∨ False) ∧ p2) → (True ∨ True))) → True)) → (((p1 ∨ p5) ∧ p3) → p4)) ∨ p1) ∨ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47541591421607993020671056046 : (((p5 ∨ ((p5 ∨ (((True ∨ ((((False ∧ p4) → True) ∧ p3) ∨ (p3 ∧ p4))) ∧ (False → True)) → p1)) ∧ (p1 ∧ True))) ∨ (p4 ∨ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46353274830294394086641071947 : (((((((False → p3) ∧ p3) ∧ p4) → ((p2 ∨ p1) ∨ ((p3 → p5) ∨ p3))) → ((((p2 → p4) → p5) ∨ p2) → p1)) ∧ (p2 ∧ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193353773608900707789219808215 : ((((p4 → p4) → p1) → ((p1 ∨ p5) ∧ (p3 ∧ p5))) → (((False ∨ ((p1 → p3) ∨ (True → p5))) ∨ (p5 → p5)) ∧ (p5 ∨ (p1 → p3)))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h4 : ((p4 → p4) → p1) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h4
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- We need to get the left conjuct of h7 based on <expert-advice>.
  let h8 := h7.left
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173941426280818743612380276583 : (((((False ∧ (p1 ∨ ((False ∧ p4) ∨ p1))) ∧ p1) ∨ (p4 ∧ (True ∨ p1))) → p5) → ((((p5 ∨ ((p1 ∨ p5) ∨ p4)) ∨ True) ∧ True) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_684183078327895432675452510902 : (((((p5 ∨ (((p5 ∧ (True ∨ p5)) ∧ p4) ∧ ((True ∧ p2) → (p3 → p4)))) ∨ (p5 ∧ p5)) ∨ (((p4 ∧ p1) → (True ∧ True)) ∧ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_727906557310786330407856122932 : ((((p2 ∨ (False ∨ p1)) ∨ ((False ∨ ((p2 ∨ (p2 → (((p2 ∧ ((p3 ∧ p4) ∧ p5)) ∧ p5) ∧ p4))) ∧ (False → False))) → (p3 ∧ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179152136355632172148128895287 : ((p2 ∧ ((((((p2 → (p4 → p5)) → p5) ∧ p1) ∨ True) ∨ p2) → p1)) ∨ (p3 ∨ ((p2 ∧ (False → p4)) ∨ ((p3 → p5) ∨ (p3 ∨ True))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_196913411245402396881751641902 : (((((p5 ∧ (p5 ∧ False)) ∨ p2) ∧ False) ∨ p3) ∨ (p2 ∨ (((p5 → p3) ∨ (p4 ∨ (p2 ∧ p1))) → ((p4 → (p3 → True)) ∨ (p3 → p3))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h7
      -- Implications on the right can always be decomposed.
      intro h8
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h12
      -- Implications on the right can always be decomposed.
      intro h13
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310604380595457914022593320321 : (p2 ∨ ((((p4 ∨ p5) ∧ False) ∧ p3) ∨ ((p4 ∧ (False ∧ p1)) → (((((True ∨ p3) → (p5 ∨ (p2 ∨ p4))) → (p4 → p1)) ∧ p3) ∧ p4)))) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- False on the left can always be used.
  apply False.elim h6
  -- Conjunctions on the left can always be decomposed.
  let h8 := h1.left
  let h9 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h10 := h9.left
  let h11 := h9.right
  -- False on the left can always be used.
  apply False.elim h10
  -- Conjunctions on the left can always be decomposed.
  let h12 := h1.left
  let h13 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h14 := h13.left
  let h15 := h13.right
  -- False on the left can always be used.
  apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_182856820125615036924590212816 : ((((p2 ∧ p1) ∨ p3) ∨ (((False ∨ True) ∧ (p5 → True)) ∨ p2)) ∧ ((p3 ∧ (p1 ∨ p4)) ∨ (True ∨ ((p3 ∧ p4) ∨ ((p5 ∧ True) → p5))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180670737145218070565578411888 : ((((p5 → (p2 ∧ (p3 ∨ True))) ∨ p3) → ((True ∧ p4) → (True ∧ p1))) → (True ∧ (((False ∨ (p1 ∧ (p1 ∧ True))) ∨ False) ∨ (p1 → p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184832380971408324720236797073 : ((((p2 → p1) ∨ (p1 ∧ p1)) → ((p4 ∧ False) ∧ (p5 ∨ False))) ∨ ((p2 ∧ True) ∨ ((p2 ∧ (p2 ∨ False)) ∨ (p3 ∨ ((False ∧ p5) → p2))))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_627700574266595931235473014410 : (((((((((p3 ∨ (p5 ∧ p5)) ∧ p2) ∧ ((((p1 → p5) ∧ (p4 ∨ p5)) → False) ∨ p4)) ∨ p4) → (True ∨ (p2 ∧ p5))) ∧ p3) → p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166094875113925714979184444980 : (((False → True) → ((p2 ∨ p2) → ((p5 ∨ (True ∨ (((p1 → p1) ∨ p2) ∨ False))) ∧ p3))) ∨ (((p3 ∧ p5) → True) ∨ (p2 → (True → p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_656981808281821762529065355947 : ((((((p5 ∨ p3) → (p3 ∨ p3)) → ((True ∨ ((p5 ∨ (p5 ∨ (p5 ∨ ((False ∧ True) ∧ p5)))) → (False ∧ p1))) → p1)) ∨ (p3 ∨ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48811551524190219554133374135 : (((p3 ∧ (((False ∧ p5) ∨ ((p2 ∧ (p2 ∧ True)) → (True ∨ (p3 → (True → ((p5 ∨ p4) ∧ p2)))))) → p3)) ∧ ((p3 → False) ∨ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225121790086437270780024761017 : (((p2 ∧ p4) ∧ p5) ∨ (((((p2 ∨ p3) ∧ ((True ∨ p2) ∨ True)) ∧ False) ∨ (p5 → ((True → (p5 ∧ ((True ∨ p2) → False))) → False))) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h6 : (True ∨ p2) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h7 := h5 h6
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215474289618420590096674879551 : ((p3 ∧ (p1 → (p3 ∨ p1))) ∨ (p4 → ((((True ∨ p1) ∧ (p3 → p2)) → (((False ∧ p5) ∨ ((p4 ∧ p4) ∨ p4)) → (p2 → p2))) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  cases h3
  case inl h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- False on the left can always be used.
    apply False.elim h6
  case inr h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- Conjunctions on the left can always be decomposed.
      let h12 := h2.left
      let h13 := h2.right
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h14 =>
        -- One of the premise coincides with the conclusion.
        exact h4
      case inr h15 =>
        -- One of the premise coincides with the conclusion.
        exact h4
    case inr h16 =>
      -- Conjunctions on the left can always be decomposed.
      let h17 := h2.left
      let h18 := h2.right
      -- Disjunctions on the left can always be decomposed.
      cases h17
      case inl h19 =>
        -- One of the premise coincides with the conclusion.
        exact h4
      case inr h20 =>
        -- One of the premise coincides with the conclusion.
        exact h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208160210143761909316476665045 : (((False ∧ (False ∧ False)) → (False ∧ p4)) → (True → ((p1 ∨ (((False ∨ True) → True) → ((p4 ∨ (((p1 ∨ p1) ∨ p5) ∨ p4)) → p5))) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_783247981189358054390492518802 : (((p3 ∨ (((p5 ∧ (True → (True ∧ ((True ∨ p2) ∧ (p4 ∧ (p4 ∧ ((p5 ∨ p4) → p4))))))) ∧ p5) ∧ ((p3 ∨ (p3 ∨ p5)) ∨ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207329799608651511537524682501 : ((((False ∧ p1) ∨ (True ∨ p5)) ∨ p1) → (p3 ∨ ((p4 → ((p1 ∧ True) ∨ p3)) ∨ (p4 → (((p1 ∨ ((p5 ∨ True) ∨ p5)) → False) → p2))))) := by
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
      -- False on the left can always be used.
      apply False.elim h4
    case inr h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h8
        -- Implications on the right can always be decomposed.
        intro h9
        -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
        have h10 : (p1 ∨ ((p5 ∨ True) ∨ p5)) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h9, we can now drive its conclusion.
        let h11 := h9 h10
        -- False on the left can always be used.
        apply False.elim h11
      case inr h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h13
        -- Implications on the right can always be decomposed.
        intro h14
        -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
        have h15 : (p1 ∨ ((p5 ∨ True) ∨ p5)) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h12
        -- We have shown the premise of h14, we can now drive its conclusion.
        let h16 := h14 h15
        -- False on the left can always be used.
        apply False.elim h16
  case inr h17 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h18
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h17
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_32179490091695492649311122635 : ((p1 ∨ ((((True ∨ (False → True)) → p2) ∧ p5) ∨ ((True → (p3 ∧ True)) → ((p4 → (p1 ∨ p4)) ∧ (False → ((False ∧ p3) ∧ p5)))))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h3
  -- False on the left can always be used.
  apply False.elim h3
  -- False on the left can always be used.
  apply False.elim h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_209299322689058867537695013159 : ((True → (p1 ∧ (False ∨ (p2 → True)))) → (((((p2 ∨ (p4 → ((p1 → p5) ∨ (p1 ∧ True)))) ∨ (p4 → False)) ∧ p3) ∨ p2) ∨ (p2 → p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_124323260372625368523331691052 : (((p1 ∧ (True ∨ (True ∨ (p4 → (p4 ∨ True))))) ∧ ((p4 ∧ (((p1 → False) ∧ p2) → False)) ∨ (((p3 ∧ True) ∧ p3) → False))) → (p3 ∨ True)) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h3
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
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h13 =>
        -- Conjunctions on the left can always be decomposed.
        let h14 := h13.left
        let h15 := h13.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h16 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h17 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h18 =>
        -- Conjunctions on the left can always be decomposed.
        let h19 := h18.left
        let h20 := h18.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h21 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro



