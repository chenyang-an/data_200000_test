variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117537200514343865515038844870 : ((p2 ∧ (((((((p4 → p2) → (p3 ∨ (False ∧ p1))) → (p4 ∨ (p4 ∧ p1))) → (p3 ∨ p1)) ∨ p1) ∨ p2) → (False ∨ p4))) ∨ (False → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337489010655496936099939265479 : (p1 → ((((True ∧ ((p2 ∧ (p3 ∧ p2)) ∨ (p3 ∨ (p2 ∨ p1)))) ∧ p4) → (p5 ∨ ((False → p2) ∧ True))) ∧ (((p1 ∧ p1) → p5) ∨ p1))) := by
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
  cases h6
  case inl h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h12
    -- False on the left can always be used.
    apply False.elim h12
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h13 =>
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h14 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h15
      -- False on the left can always be used.
      apply False.elim h15
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h16 =>
      -- Disjunctions on the left can always be decomposed.
      cases h16
      case inl h17 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Implications on the right can always be decomposed.
        intro h18
        -- False on the left can always be used.
        apply False.elim h18
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h19 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Implications on the right can always be decomposed.
        intro h20
        -- False on the left can always be used.
        apply False.elim h20
        -- True on the right can always be proven directly.
        apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115157547993055906380251193338 : (((p3 → (True → (p5 → (((False → (True → p2)) ∧ p1) ∧ p2)))) → (False ∨ (p3 ∧ ((p3 ∨ False) ∧ (False ∨ (p1 ∧ False)))))) ∨ (False → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_766480825776067407781841402057 : (((p4 ∧ (p2 ∧ ((((False ∨ (p4 ∨ ((p5 → False) ∨ (p5 → ((p3 ∨ p3) ∧ p2))))) ∨ p4) ∧ (True ∨ (p5 → p1))) ∧ (p2 ∨ p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147855456502388909934858749026 : (((False → (((((p5 → ((p3 ∨ p4) ∧ True)) → p5) → ((True ∨ p2) → p5)) → (p2 ∨ p5)) ∧ True)) → p3) ∨ (p5 → (p1 → (p5 ∧ True)))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178528857442595991161074399741 : (((((p3 ∧ True) ∧ p4) → ((p3 ∧ p4) ∧ p5)) → (True → (False ∧ p1))) ∨ (True → (p5 → (p5 ∧ ((p4 ∨ False) → ((p1 ∨ False) ∨ p4)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135797113577811524007865593827 : ((((False ∨ False) → (p3 ∧ ((((p1 ∧ p4) ∧ False) ∧ True) ∨ (True ∨ p5)))) → ((p3 → (p3 → p2)) → (p4 ∧ p3))) ∨ (True ∨ (p5 ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_808010312313346938301389333009 : (((p4 → ((p5 → p2) → (p4 → (((False → p4) → (True → False)) ∧ (((p5 ∨ p2) ∧ p1) ∨ (p3 ∧ ((p5 ∧ p1) ∧ (False ∨ True)))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228607308873775974052666889572 : ((p1 ∨ (p1 → p4)) ∨ ((((p4 → True) ∧ ((p5 ∨ (True ∧ p3)) ∧ (p5 → ((p5 → p3) ∧ ((p3 ∧ p2) ∨ p2))))) → (p4 ∨ p3)) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h7 : p5 := by
      -- One of the premise coincides with the conclusion.
      exact h6
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h8 := h5 h7
    -- We need to get the left conjuct of h8 based on <expert-advice>.
    let h9 := h8.left
    -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
    have h10 : p5 := by
      -- One of the premise coincides with the conclusion.
      exact h6
    -- We have shown the premise of h9, we can now drive its conclusion.
    let h11 := h9 h10
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h11
  case inr h12 =>
    -- Conjunctions on the left can always be decomposed.
    let h13 := h12.left
    let h14 := h12.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38218447900310596431940755832 : (((((p3 ∧ (p1 → p5)) → ((((p4 → p5) → p4) ∧ (((p5 → p1) ∨ (p2 → p2)) → p1)) ∧ p4)) → (p4 ∧ (False ∨ p3))) ∧ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_224088272643362299786434039446 : ((p5 ∨ (p3 ∨ True)) ∧ ((((False ∧ True) → (p1 → False)) ∨ p4) → ((p2 ∧ p1) ∨ ((True → p5) → (p1 ∨ ((p5 ∧ p5) ∨ (p4 → p2))))))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h4 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h5 := h3 h4
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h5
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h8 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h9 := h7 h8
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47236689374777250604295612979 : (((((p4 ∧ ((p4 ∧ True) → (p3 ∧ p4))) ∧ p3) → ((True ∨ (p4 ∨ ((p1 ∧ p4) ∧ p1))) → (p1 ∨ (p5 ∧ p1)))) ∨ (False ∧ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135550886203425798627344848228 : ((((p5 ∧ p4) ∨ (p4 ∧ ((p5 ∨ (p4 → p3)) ∨ (((p3 ∧ p1) ∧ p3) ∨ True)))) ∧ ((p2 → (p4 ∧ p5)) → p2)) ∨ ((p5 ∧ True) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314291958742291160639107752564 : (p3 ∨ (((p5 ∧ (((((False ∧ ((p5 → (p3 → p5)) ∧ p2)) ∨ (p1 ∨ p1)) → (p2 ∨ p1)) ∧ p5) → p3)) ∧ p4) → (p3 ∨ (p2 ∧ p1)))) := by
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
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h6 : ((((False ∧ ((p5 → (p3 → p5)) ∧ p2)) ∨ (p1 ∨ p1)) → (p2 ∨ p1)) ∧ p5) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h7
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- False on the left can always be used.
      apply False.elim h9
    case inr h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h12
      case inr h13 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h13
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h14 := h5 h6
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_599115036450059176263253154957 : (((((False → p4) ∧ (((p2 ∧ p5) → ((False → p3) ∨ p2)) → (p2 → (((p2 → (p4 ∧ (p3 ∧ (True ∧ p1)))) ∧ p2) → p4)))) ∧ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259902552437262248383149426874 : ((p1 → p4) → (p3 ∨ ((((p5 → (p3 ∨ False)) ∧ p5) ∨ ((p4 ∨ (p1 ∧ ((p2 ∧ p1) ∨ (p2 → (p5 ∨ p4))))) ∨ (p3 → True))) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308329658231691057239249851502 : (p2 ∨ (((((p1 ∧ p2) ∨ (((p5 ∧ (((((((p4 → True) → p3) ∨ False) ∧ p3) ∨ True) → False) → True)) ∧ p5) → p4)) ∧ False) ∧ p1) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43367718163821019803159240307 : ((((((((p1 → False) ∧ (p5 ∧ (p1 → p2))) ∨ (False ∧ (p1 ∧ p2))) ∧ (p2 ∨ ((p5 → True) ∨ p5))) → (p1 ∧ p4)) ∨ p3) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_655096997295797108386712343042 : (((((p1 ∨ ((((p3 ∨ (False → (p1 → p3))) ∧ (p3 ∨ ((p2 → (p1 ∨ True)) ∨ p4))) ∨ p4) ∧ (p3 → p5))) → p2) ∨ (p5 ∨ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138252633690236567952550947632 : ((p2 → (True ∧ ((p3 ∧ ((p5 ∧ ((p3 ∧ p4) ∨ (((p3 ∨ p3) ∨ (p1 ∨ p2)) ∨ (False ∧ p5)))) ∨ p1)) ∨ True))) ∨ ((True ∨ p3) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217169667625840393611272604545 : ((((p2 ∧ p3) → True) ∨ True) → ((p5 → (((p4 ∨ ((p5 → (p2 ∨ p3)) → p4)) ∨ p5) ∧ (((True → (p5 ∨ p3)) ∧ p5) ∨ p4))) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h4
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h6
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h6
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h7
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h6
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207281059976384079205303491703 : (((((p2 ∨ False) → p1) → True) ∨ p2) → ((False ∨ p2) → ((((True ∧ False) ∧ (p5 ∨ True)) ∧ p5) ∨ (p2 ∨ ((p5 → p2) ∨ (False ∧ p1)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191157849154498201577356071434 : ((((p5 → p4) → p3) ∨ ((p3 → (True ∨ p4)) ∧ p1)) ∨ (p3 → (p4 → ((((p2 ∧ (True ∨ p3)) ∨ True) ∨ p2) → (p3 ∧ (p5 → p4)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- One of the premise coincides with the conclusion.
        exact h1
      case inr h9 =>
        -- One of the premise coincides with the conclusion.
        exact h1
    case inr h10 =>
      -- One of the premise coincides with the conclusion.
      exact h1
  case inr h11 =>
    -- One of the premise coincides with the conclusion.
    exact h1
  -- Implications on the right can always be decomposed.
  intro h12
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h13 =>
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h14 =>
      -- Conjunctions on the left can always be decomposed.
      let h15 := h14.left
      let h16 := h14.right
      -- Disjunctions on the left can always be decomposed.
      cases h16
      case inl h17 =>
        -- One of the premise coincides with the conclusion.
        exact h2
      case inr h18 =>
        -- One of the premise coincides with the conclusion.
        exact h2
    case inr h19 =>
      -- One of the premise coincides with the conclusion.
      exact h2
  case inr h20 =>
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_618126211877962261353416717495 : (((((p5 ∧ ((p4 ∨ p5) ∨ p1)) ∧ ((p5 ∧ False) ∧ (p5 ∧ ((((False → (p4 ∧ p1)) ∧ (p1 → (p1 ∧ p3))) → p2) ∧ p3)))) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_786515536379504683392963600663 : (((p4 ∨ ((p4 ∧ ((((p5 ∧ p1) ∨ p4) ∧ (False ∨ p2)) → (p4 ∧ p5))) → (((False ∨ (p4 → True)) → p2) ∧ (p1 ∧ (p1 → False))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_747232147334812840703204395697 : ((((p5 ∨ p1) → (p3 ∨ (((((p1 → False) ∨ (p1 ∧ True)) ∨ (True ∨ ((p3 ∧ False) ∧ p5))) ∨ (True → (False → p5))) ∨ (p2 ∨ p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219708756554196040642450883475 : ((p1 → ((p3 ∨ p5) → p5)) → ((((p1 ∨ (((True → p5) ∨ p5) ∨ ((p5 ∨ p1) ∨ (p2 ∧ ((p5 → p3) ∨ p1))))) → p4) ∧ p3) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_654469318177018225837388788705 : ((((((p4 ∨ p5) ∨ (((((False ∧ False) ∨ False) ∨ p3) → p4) → ((((p1 ∧ (p5 → True)) ∨ True) ∨ False) ∧ False))) ∨ False) ∨ (p3 ∨ True)) ∨ False) ∧ True) := by
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
theorem thm_5_vars_111347088514732018763326054836 : (((p4 ∧ ((p2 → ((True → ((((p1 ∧ p3) ∨ p4) ∧ ((p5 → (p4 → False)) ∨ (True ∧ p5))) ∧ p1)) ∨ p4)) ∧ False)) ∧ p2) ∨ (p5 → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356767478470472958310756153670 : (p5 → ((((p2 ∨ p5) ∨ p5) → (p1 ∧ False)) → (p2 ∧ ((((False ∧ p3) → ((((False ∧ p5) ∧ True) → p5) ∨ (False ∧ True))) → p4) ∧ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : ((p2 ∨ p5) ∨ p5) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- False on the left can always be used.
  apply False.elim h5
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h6
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h7 : ((p2 ∨ p5) ∨ p5) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h8 := h2 h7
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- False on the left can always be used.
  apply False.elim h9
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h10 : ((p2 ∨ p5) ∨ p5) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h11 := h2 h10
  -- We need to get the right conjuct of h11 based on <expert-advice>.
  let h12 := h11.right
  -- False on the left can always be used.
  apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152674913670328549402393953959 : (((p5 → p3) ∧ (p3 ∨ (((p1 → (p5 ∧ p4)) → p4) ∧ (True → ((True ∧ ((p4 → p1) ∧ p3)) ∧ p1))))) → (((p3 ∨ p5) ∧ p4) ∨ True)) := by
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
theorem thm_5_vars_681457694835062481216515922812 : ((((p4 ∨ (((p5 ∧ (((True ∨ p4) → p2) ∧ p2)) ∨ p2) ∨ (p1 → (p2 ∨ ((p4 → p2) → True))))) → (p1 ∨ (p3 ∨ (True → p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_777161269394418249790589221340 : (((p1 ∨ ((p4 → (((((p4 → True) ∨ p1) ∧ (p2 ∨ (((True → p4) ∧ (p5 → p3)) ∨ (True ∨ p3)))) ∧ True) ∨ p2)) → (True ∧ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_734845705271982672994513232856 : ((((p2 ∨ p2) ∧ ((((True → ((((((p4 ∨ ((True ∧ p5) ∨ False)) ∨ p3) ∨ p4) → p4) → False) → p2)) ∧ (True ∨ p2)) ∧ p5) → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186331860222031928478312483178 : (((((True ∧ (p3 ∨ p5)) → p1) ∨ (p3 ∧ (False → p2))) → True) → (p2 → (((((p3 → p4) → (True → p2)) ∧ p2) → (p5 ∧ p5)) ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338126710319050693815854873327 : (p1 → ((((True → (p3 → (p3 → p2))) → False) → p2) ∨ (((p1 → ((False ∧ p4) → ((p2 → False) ∨ p3))) → (True → (False ∨ p5))) ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164936412927692325171225426693 : ((((p3 ∨ ((p5 ∨ (((p1 ∧ p3) ∧ p5) → ((p1 → p4) → p5))) ∨ p2)) ∨ p1) → p2) ∨ (p1 ∨ ((p2 ∨ (p5 ∧ p3)) ∨ (False → p1)))) := by
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
theorem thm_5_vars_622984500013045144839634288806 : ((((p5 ∧ ((p1 → (p4 ∨ p4)) ∨ ((p3 ∨ (p3 ∨ ((True ∨ (p1 → p1)) → True))) → ((p1 → (p5 ∧ (True ∧ True))) ∧ False)))) ∨ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328524104504088616886260691448 : (True → ((((p4 → p5) ∧ (p2 ∨ p3)) ∧ ((p5 → (p1 ∧ (False ∨ (p5 ∨ False)))) → p4)) ∨ (((True → False) ∧ (False → p3)) → (p3 ∨ p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h5 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h5
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190036633763635486267975444223 : (((((p1 → ((True ∧ p4) ∨ p3)) ∨ p1) ∨ p5) ∧ p3) ∨ (p2 ∨ (((p4 → True) ∨ p5) ∨ (p2 ∧ (((p4 ∨ p4) ∨ (p4 → True)) ∨ p5))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342846706143693685326120774413 : (p2 → (((p4 ∧ ((p3 → p5) ∧ p1)) ∧ p4) ∨ (p1 ∨ ((p3 ∨ (p1 → (((((True → True) → p4) ∨ False) → p2) ∨ True))) ∧ (p2 ∨ p2))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181530005208500082234072550484 : ((True → (((p1 → p1) → (p1 ∧ p4)) ∨ (((p5 ∧ p1) ∨ p2) ∧ p1))) → (p1 ∨ (False ∨ (((p4 → ((False → p4) → p1)) ∧ p4) ∨ p3)))) := by
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
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h5 : (p1 → p1) := by
      -- Implications on the right can always be decomposed.
      intro h6
      -- One of the premise coincides with the conclusion.
      exact h6
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h7 := h4 h5
    -- We need to get the left conjuct of h7 based on <expert-advice>.
    let h8 := h7.left
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h12.left
      let h14 := h12.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h11
    case inr h15 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48964605597923205934336509598 : ((((((((p3 ∨ (((p2 → p1) ∧ (True → p2)) ∨ p2)) ∨ p3) → ((p3 → False) → False)) → False) ∨ p3) ∨ True) ∨ (p3 → (p5 → p3))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246518770558824740755611138417 : ((p5 ∧ p1) ∨ (((((p4 → (p4 ∧ (p3 ∨ p4))) → (p3 ∧ p1)) → False) ∨ p4) ∨ (((p5 ∧ (p5 ∨ ((p5 → p3) ∧ p2))) ∧ p1) → p5))) := by
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
  let h4 := h2.left
  let h5 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191109596732471313411563610390 : (((p3 ∧ (p1 ∨ p5)) ∧ ((p2 ∨ (p1 ∨ p3)) ∨ p2)) ∨ (p1 ∨ (((p2 ∨ p4) ∧ (p2 ∨ p5)) → (False ∨ (((p2 ∧ p1) → True) ∨ p2))))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h10
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232017343742742243818796457503 : (((p3 ∨ True) → False) → (((p1 ∧ (((False ∨ False) ∧ True) → False)) → ((p1 → (((p5 → p3) ∨ p5) ∧ ((p3 ∧ p4) ∨ False))) → False)) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p3 ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_196669914831676471513679480808 : ((((p2 ∨ (p4 ∧ (p4 ∧ False))) ∧ p5) ∧ p2) ∨ (False → (((p5 ∨ (p2 → p2)) → (p2 → ((False ∨ p4) ∨ True))) → (p5 ∨ (p3 ∨ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259130638883444163770388242831 : ((False → True) → (((p3 → p5) → ((p4 → (((p4 ∧ p2) → (True ∨ True)) → (((p2 ∧ p2) ∧ (False ∨ (False ∧ p3))) ∧ False))) → p3)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_97642167776211885141497475283 : ((p3 ∨ ((((p5 ∨ p2) → p3) ∧ (((p5 → ((p4 ∧ p4) ∧ True)) ∨ ((p1 ∨ (False ∨ True)) ∨ (p2 ∨ p5))) ∧ p2)) ∧ (True → p5))) → p3) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
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
    cases h8
    case inl h10 =>
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h11 : (p5 ∨ p2) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h9
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h12 := h6 h11
      -- One of the premise coincides with the conclusion.
      exact h12
    case inr h13 =>
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h14 =>
        -- Disjunctions on the left can always be decomposed.
        cases h14
        case inl h15 =>
          -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
          have h16 : (p5 ∨ p2) := by
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h9
          -- We have shown the premise of h6, we can now drive its conclusion.
          let h17 := h6 h16
          -- One of the premise coincides with the conclusion.
          exact h17
        case inr h18 =>
          -- Disjunctions on the left can always be decomposed.
          cases h18
          case inl h19 =>
            -- False on the left can always be used.
            apply False.elim h19
          case inr h20 =>
            -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
            have h21 : (p5 ∨ p2) := by
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- One of the premise coincides with the conclusion.
              exact h9
            -- We have shown the premise of h6, we can now drive its conclusion.
            let h22 := h6 h21
            -- One of the premise coincides with the conclusion.
            exact h22
      case inr h23 =>
        -- Disjunctions on the left can always be decomposed.
        cases h23
        case inl h24 =>
          -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
          have h25 : (p5 ∨ p2) := by
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h9
          -- We have shown the premise of h6, we can now drive its conclusion.
          let h26 := h6 h25
          -- One of the premise coincides with the conclusion.
          exact h26
        case inr h27 =>
          -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
          have h28 : (p5 ∨ p2) := by
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h27
          -- We have shown the premise of h6, we can now drive its conclusion.
          let h29 := h6 h28
          -- One of the premise coincides with the conclusion.
          exact h29



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42329860766371473069099062703 : (((p3 ∧ (((p3 ∧ (p1 ∨ (True → (((p4 → False) ∧ (p1 ∨ (False ∧ p5))) ∨ p1)))) ∨ ((p4 ∧ False) ∨ (p2 ∨ p5))) ∧ False)) ∨ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_89243839599185618264007600684 : (((p2 ∧ (p4 ∨ p1)) ∧ ((((True → p2) → False) ∧ p3) ∧ ((((p4 ∨ p1) ∨ True) → p4) → (((True ∧ True) ∧ p5) ∨ (p1 ∨ p4))))) → p5) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h9 := h7.left
    let h10 := h7.right
    -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
    have h11 : (True → p2) := by
      -- Implications on the right can always be decomposed.
      intro h12
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h9, we can now drive its conclusion.
    let h13 := h9 h11
    -- False on the left can always be used.
    apply False.elim h13
  case inr h14 =>
    -- Conjunctions on the left can always be decomposed.
    let h15 := h3.left
    let h16 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h17 := h15.left
    let h18 := h15.right
    -- We want to use the implication h17 based on <expert-advice>. So we show its premise.
    have h19 : (True → p2) := by
      -- Implications on the right can always be decomposed.
      intro h20
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h17, we can now drive its conclusion.
    let h21 := h17 h19
    -- False on the left can always be used.
    apply False.elim h21



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38990148198257598349716910810 : ((((True ∨ False) ∧ ((((p4 ∨ p4) → (p3 → False)) ∧ p1) ∧ (((True ∧ (p2 → p3)) ∨ (p4 → (p5 ∧ (p1 → True)))) → p4))) ∧ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_124708503356286985364708390109 : (((((p1 ∨ True) → False) ∧ p5) ∧ (p4 ∧ ((p5 ∧ (True → ((p4 ∨ (True ∧ True)) → ((p4 ∧ p5) ∨ (p3 ∨ p1))))) ∧ p5))) → (p1 ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h3.left
  let h7 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h7.left
  let h9 := h7.right
  -- Conjunctions on the left can always be decomposed.
  let h10 := h8.left
  let h11 := h8.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h12 : (p1 ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h13 := h4 h12
  -- False on the left can always be used.
  apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_618985892081040386106013028919 : ((((((p1 ∧ p3) ∨ False) ∨ (p3 → ((((p1 ∨ p2) → p3) → False) → ((p2 → p2) ∧ (p2 ∨ ((False ∨ (p3 → True)) → p5)))))) ∨ False) ∨ p3) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h3
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : ((p1 ∨ p2) → p3) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h7 =>
      -- One of the premise coincides with the conclusion.
      exact h1
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h8 := h2 h4
  -- False on the left can always be used.
  apply False.elim h8
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_103138396288334676609762128798 : ((((p4 ∨ p5) ∧ (p1 ∨ (((p3 ∧ (((((p3 ∧ (True ∨ True)) ∧ p5) ∧ p2) → (p4 ∧ False)) ∧ p1)) ∧ True) ∧ True))) ∨ True) ∧ (p1 → True)) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185271226157270942290767739319 : ((p1 ∧ (p3 ∨ ((p3 ∨ (p2 ∧ True)) ∧ ((p3 ∧ p5) → False)))) ∨ ((((True ∧ (p1 → (p3 → ((False → p4) ∨ False)))) ∧ p4) ∧ p3) → p3)) := by
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
  let h6 := h4.left
  let h7 := h4.right
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341588583742805043959530125700 : (p2 → ((((p1 → (p5 ∧ p1)) → ((p5 → ((False ∨ (p4 ∨ False)) → (p4 ∨ p2))) → p1)) ∨ (p1 → ((p1 ∨ p3) → p2))) ∧ (p2 ∧ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h5 =>
    -- One of the premise coincides with the conclusion.
    exact h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48587899795816257044198579010 : ((((((((p5 → p4) ∧ (False ∨ (False ∧ p3))) → p3) ∧ ((p5 ∨ p2) → False)) ∨ (p3 → p5)) ∧ (p4 → p5)) ∧ ((p5 → p1) ∨ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_654776708153349421696044290407 : (((((((p3 ∨ p2) ∧ (True ∨ (((True → (p4 → (False ∧ p4))) ∧ (p2 ∧ False)) ∨ ((p2 ∨ p3) ∧ False)))) → False) → False) ∨ (p2 ∨ True)) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_352674762924883991410200791932 : (p4 → ((p1 ∨ p2) ∨ (False ∨ ((p2 ∧ (((((p2 → p3) ∨ p5) → p3) ∧ ((True → p4) ∨ p3)) ∧ (False → (p1 → (p4 ∧ p1))))) ∨ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_673914360126769236167488075238 : (((((True → p5) → (p2 ∧ ((True ∧ p4) ∨ (False → (p5 → (p2 → (p1 ∨ (((p5 → p5) ∧ p1) ∨ True)))))))) → ((p5 ∨ p4) ∨ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_327860767943998695312162097688 : (True → (((False ∧ (p1 ∨ p1)) ∨ (True → ((((p3 → p5) ∧ (p2 ∨ p2)) ∧ True) ∨ (p2 → (p1 ∧ ((False → p2) ∧ False)))))) ∨ (True ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158958996631398449437402674280 : ((p2 ∨ (p1 ∨ (((p3 ∧ p5) → p1) ∧ ((p1 ∨ p2) ∨ ((True ∧ p2) ∧ ((p3 ∧ True) → p5)))))) ∨ (p1 → (((p3 ∧ p5) → p3) ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_226460425141352226710483122314 : (((p1 → p4) ∨ p5) ∨ ((((p3 ∧ (p1 ∧ p1)) ∧ p1) ∨ p4) → (p4 → ((p5 → (((p2 ∧ p2) → (True → True)) → p4)) ∨ (p2 → p5))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h10
    -- Implications on the right can always be decomposed.
    intro h11
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h12 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h13
    -- Implications on the right can always be decomposed.
    intro h14
    -- One of the premise coincides with the conclusion.
    exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_352628439657990696608845944367 : (p4 → ((False ∧ p1) ∨ ((p1 ∧ (((((p3 ∧ False) → p2) ∧ (p4 ∧ p5)) ∧ (((p5 ∧ p3) ∧ True) → ((p3 → False) ∨ p4))) ∧ p2)) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_878935547641022606998602910851 : ((((p5 ∧ ((((p1 ∧ (((p1 → p1) ∧ p1) → ((p4 ∧ (True ∨ (p3 ∨ False))) ∧ (True ∧ p4)))) ∨ True) → p3) ∧ p4)) ∧ (p3 → p3)) → p3) ∧ True) := by
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
  let h6 := h5.left
  let h7 := h5.right
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h8 : ((p1 ∧ (((p1 → p1) ∧ p1) → ((p4 ∧ (True ∨ (p3 ∨ False))) ∧ (True ∧ p4)))) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h9 := h6 h8
  -- One of the premise coincides with the conclusion.
  exact h9
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_348147027908264486317212947711 : (p3 → ((p4 ∧ p2) → ((p5 ∨ ((p1 → p4) → ((True ∨ (p1 → (True → p3))) → p5))) ∨ (p2 ∧ ((True ∧ ((p4 ∧ False) ∧ True)) → False))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h7.left
  let h9 := h7.right
  -- Conjunctions on the left can always be decomposed.
  let h10 := h8.left
  let h11 := h8.right
  -- False on the left can always be used.
  apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_95779342730158545806159451484 : ((p5 ∧ (True → ((((True → (p4 → p2)) → (p5 ∧ (p3 ∨ (p1 → ((p3 → False) ∧ p5))))) ∧ (p5 ∨ (False → False))) ∧ (False ∧ True)))) → p4) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- We need to get the left conjuct of h6 based on <expert-advice>.
  let h7 := h6.left
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47003212600116254764183875556 : (((((True ∧ True) ∧ (p3 → (((True → False) ∨ ((p2 ∨ (p2 ∧ False)) → p2)) ∨ (p3 → ((p2 ∨ False) ∨ p1))))) → p1) ∨ (p5 ∨ True)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165753338132334700837060347467 : (((p5 ∧ ((False ∧ p1) ∨ False)) ∨ (p1 ∨ ((p5 → (p5 → (p4 → (p2 ∧ True)))) ∨ p2))) ∨ ((p4 ∧ (False → ((p1 ∧ p3) ∨ False))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198355627114493466128363433077 : ((p2 ∧ (True ∨ ((p4 ∨ True) ∧ (p5 ∧ True)))) ∨ ((p1 ∧ (((p3 → p3) ∨ True) → (False ∧ (p4 ∧ p5)))) ∨ (((True ∨ p4) ∨ p3) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137042583740714311786111294496 : (((True → p4) → (p4 → ((p1 → ((p2 ∧ ((p1 → True) → p2)) ∧ (((p2 → p2) → p1) ∨ True))) ∨ (p5 ∨ True)))) ∨ ((p2 → True) ∧ p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_767514171097340093293276094090 : (((p5 ∧ ((((p5 ∨ (((p3 → p1) ∨ p1) → (p3 ∧ ((((False ∧ p5) ∨ p1) → (p4 ∨ p2)) → p4)))) → (p4 → p3)) → p5) ∨ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165910350556357376932415996146 : (((p3 → (True ∧ p4)) → (p1 ∧ ((((True ∨ p4) ∨ p5) ∧ p1) → ((p1 → True) → p4)))) ∨ ((p3 → p5) ∨ (((p1 ∧ True) ∧ p1) → p1))) := by
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
  let h4 := h2.left
  let h5 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299440483005419653116122805679 : (False ∨ ((p1 ∨ ((((p3 → ((False ∨ (p2 ∧ (p3 ∧ (p5 → (((False → True) ∧ p3) ∧ p1))))) ∧ p1)) ∧ p4) ∨ True) ∨ (p4 → False))) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113481581780343493329154178569 : ((((((True → ((True ∨ False) ∧ False)) ∨ (p1 ∨ (True ∧ False))) → ((p3 ∨ p2) ∧ (p2 ∨ p4))) ∨ (p3 → p1)) ∨ (True ∧ True)) ∨ (True ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_126423581649574951412547749238 : ((p1 ∧ (p5 → (((False ∧ ((True ∨ (False ∧ False)) ∧ (((((p1 ∧ p3) ∧ p3) → (p1 → p1)) → p2) → p4))) ∨ p2) → p2))) → (p4 ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248768538568570892813080560278 : ((p3 ∨ p3) ∨ (((True ∧ (p1 ∧ p1)) ∨ (p5 ∨ (False → True))) ∨ (p4 ∨ (((((p5 ∧ True) ∧ p1) ∧ False) → True) → (p1 ∧ (p4 ∨ p3)))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_599724523136530957659505794727 : (((((p3 → p2) ∨ ((p4 → ((p1 → p5) → (((True → (p5 → True)) → p1) → p5))) ∧ ((((p3 ∧ p3) ∨ False) ∧ p3) ∧ True))) ∧ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56997988574245513194928115434 : (((True → (False ∧ p1)) ∧ (p5 ∧ (((p1 → (((False ∧ p4) ∧ (False ∧ (p4 → (p1 ∨ p3)))) → (p2 → p5))) ∧ (p3 ∨ p5)) ∨ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_76279647773546569936466951596 : (((((((False ∨ False) ∧ (((((p4 → p1) → (True → (False ∨ False))) ∨ p5) ∧ p5) ∧ p1)) → (p3 ∧ p5)) → False) ∨ (p2 → True)) → False) → p2) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((((False ∨ False) ∧ (((((p4 → p1) → (True → (False ∨ False))) ∨ p5) ∧ p5) ∧ p1)) → (p3 ∧ p5)) → False) ∨ (p2 → True)) := by
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
theorem thm_5_vars_226277767178787889114764866397 : (((p4 ∨ False) ∨ p2) ∨ ((False ∨ (False ∨ ((((p3 → False) ∧ False) ∨ (((p4 → p1) ∧ True) ∨ ((False → True) ∧ (False → True)))) ∨ False))) ∨ p3)) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263974611753233733181161351333 : (True ∧ (((((((True → p4) ∨ p2) ∨ (p5 → False)) → p2) ∧ p4) → p1) ∨ (p3 → ((p1 ∨ (True ∧ (False → (p5 ∨ True)))) ∨ (False ∨ p5))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_636681095772354370820543318375 : (((((((False ∧ (False ∧ (p3 ∧ p4))) ∨ p1) ∨ (p2 → ((False ∨ p1) ∧ False))) ∨ (((p1 ∨ ((p4 ∧ False) → p2)) → p1) → False)) → p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165446834700553718599153240938 : (((((True ∧ (True → (p3 → (p4 → False)))) ∨ p3) ∨ p4) ∧ (p1 → (p3 ∨ (False ∧ p3)))) ∨ ((p1 ∧ (False ∨ False)) → (p1 → (p3 ∧ p3)))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- False on the left can always be used.
    apply False.elim h6
  -- Conjunctions on the left can always be decomposed.
  let h7 := h1.left
  let h8 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h9 =>
    -- False on the left can always be used.
    apply False.elim h9
  case inr h10 =>
    -- False on the left can always be used.
    apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205665255822269420484527332315 : (((p1 ∨ p2) ∨ (p4 ∧ (True ∧ p5))) ∨ ((p5 ∧ p1) → (False ∨ (p5 → (((p2 ∧ (False ∧ (True ∨ (p5 ∨ p3)))) → p5) → (p4 ∨ True)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_779354169503558171004011042086 : (((p2 ∨ ((p5 → ((((p2 ∧ p3) → (True ∧ ((p4 ∨ p2) ∧ p1))) ∧ ((p5 ∨ p3) ∨ (False ∨ p2))) ∧ ((p2 → p3) → p4))) ∧ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_194607142110924859657213677868 : ((((p1 ∨ ((True ∨ p4) ∨ False)) ∨ True) ∨ p2) ∧ ((p3 → p3) ∧ (((((((p2 ∧ (False ∧ p5)) ∨ p4) ∨ p4) → p1) → p3) ∧ False) ∨ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_621181583275839328105650369775 : ((((True ∧ ((p3 ∨ (((((p2 ∨ False) ∨ False) ∧ p1) ∨ ((p4 ∨ ((p1 → (True ∨ p3)) ∧ (p4 ∨ p5))) → p4)) ∧ p4)) ∧ p2)) ∨ True) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_346642075559508270371098117550 : (p3 → ((p5 ∨ (p5 → (((((((p1 ∨ (p2 → ((p5 → p5) ∧ False))) → True) → True) → p4) → p1) ∨ p5) → p2))) ∨ ((p1 ∧ True) → p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59025938577268511683540203022 : (((p4 ∧ True) ∨ ((((False ∨ (((True → False) ∧ p3) ∧ (p1 ∧ False))) ∨ ((True → p4) ∧ p2)) ∧ p1) ∨ ((True ∨ (p5 → p3)) ∨ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_788328858318188781741110383357 : (((p5 ∨ (((p1 ∧ (False ∧ ((p5 ∧ ((p3 ∧ p5) ∨ False)) ∨ ((p2 → (p2 ∨ (p2 ∨ ((p2 ∨ p1) ∧ p1)))) → p1)))) ∨ True) ∨ p1)) ∨ p5) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_92877054724650480558001934523 : ((True ∧ ((True → ((p2 → ((p1 ∨ p1) → ((p4 ∨ ((False → (((True ∨ p3) ∨ p1) ∨ (False ∨ p1))) ∧ True)) ∧ True))) ∧ p1)) ∧ p2)) → p1) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h6 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h7 := h4 h6
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56642111863245583576981802401 : ((((False ∨ p1) ∧ p1) ∧ ((((((p5 → p2) → ((p4 → p2) → p4)) ∧ ((p1 → (p2 → p3)) → (p4 → True))) ∨ p2) ∧ p1) → p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47127863030585820498522247706 : ((((((True ∨ p5) ∧ ((p3 ∨ p4) → p1)) ∧ (((p1 ∨ p4) → (p4 → (p3 ∨ p4))) ∨ True)) → (True ∧ (p5 → False))) ∨ (False ∧ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_262411867784659402463552571400 : (True ∧ ((False ∧ ((((p4 ∨ p4) → p3) ∧ ((p2 → ((False → p4) ∧ p2)) → (True → p2))) ∧ (p3 → (((p4 ∧ True) ∧ p5) ∧ p3)))) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64137861875052880377108813622 : ((False ∨ (((True → False) ∨ p2) ∧ (((p5 ∧ ((p3 → True) ∨ ((((p2 → (True → False)) ∧ p4) → p5) ∧ p3))) → (p5 → p1)) → p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116163900232246767023778784773 : (((p5 ∨ (p1 ∨ p5)) ∧ (p2 → ((p3 → (p2 → (p3 → p5))) → ((p2 ∧ ((p1 ∨ ((p3 ∨ False) ∨ True)) ∨ p1)) ∨ p1)))) ∨ (True → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231686574633801844019000276809 : (((p1 ∧ p3) → p1) → ((((False ∧ p5) ∨ p1) → (((True ∨ ((True ∧ p5) ∨ p3)) → ((p1 ∧ p3) ∧ False)) ∨ p1)) ∨ (p4 → (p1 ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_588319737540824498595802392872 : ((((((p4 → ((p1 ∨ p4) ∨ False)) ∧ (((p3 → ((p4 ∨ ((p2 → p3) → p4)) ∧ p3)) ∨ (False → (p5 ∧ p4))) ∧ p5)) ∨ p5) ∧ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



