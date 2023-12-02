variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172992921790279189465687751759 : ((p5 ∧ ((True ∨ (True ∨ ((p3 ∧ (p5 ∧ ((False ∨ p5) ∨ p2))) → True))) → p5)) ∨ (True ∨ ((p5 ∨ p3) ∨ (p1 ∨ ((True → p1) ∧ p2))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65926015815132823844185626151 : ((p4 ∨ (p5 ∧ ((p2 ∨ False) → ((False ∧ (p4 ∨ (p5 ∧ p2))) ∧ (((((p5 ∧ (True → p3)) ∨ p1) ∨ False) ∨ True) ∧ (p1 → p4)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184578282984498842792552300299 : (((p1 ∧ (((p2 ∨ (p3 ∨ True)) ∧ p3) ∧ True)) → (False ∨ p5)) ∨ ((p2 → (True ∧ False)) ∨ (p2 → (((p1 ∨ (p4 → p2)) → p2) ∨ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_591046076745803416264076805234 : (((((p5 → (((p5 ∨ ((((p1 ∨ True) ∨ p4) ∨ p5) ∧ ((((True ∨ p5) → False) → p1) ∨ (p5 ∧ p3)))) → p3) ∧ True)) → p3) ∧ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308386680280094684038844432322 : (p2 ∨ ((((p5 ∨ (p1 → (p2 ∧ (True ∨ (True ∧ (True ∧ True)))))) → ((((False ∨ ((True → p1) ∧ p5)) ∨ p4) ∨ True) ∨ p2)) ∨ p2) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186117089169340473191378782211 : (((((p4 ∨ p4) ∧ (p1 ∨ p3)) ∧ ((p4 ∨ False) → p2)) ∨ p1) → ((True ∧ (p3 ∨ ((((p2 → (p1 ∧ p2)) ∧ p1) ∧ False) ∨ True))) ∨ p4)) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h7
      case inr h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h7
    case inr h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h10
      case inr h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h10
  case inr h13 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_579729293955180873784823247929 : (((p4 → (((p3 → (True ∨ ((p5 ∨ (((True ∧ (p4 → p1)) ∨ (False ∧ False)) ∧ p3)) ∧ True))) → (p5 → (False ∧ (True ∨ False)))) ∨ p4)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167635357498535408490395918164 : (((((p4 ∨ (((True ∨ p2) ∨ (p1 ∨ p2)) ∧ True)) → True) → (p1 ∧ p3)) → (p1 ∧ False)) → ((((p2 → False) ∨ (True ∨ True)) ∧ p3) → p3)) := by
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
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h8 =>
      -- One of the premise coincides with the conclusion.
      exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_922655301160057039166992547609 : ((((True ∨ (p4 → ((p4 ∧ True) ∨ (((p2 ∨ p1) ∧ p1) ∧ (p1 ∧ False))))) → ((((False → (p4 ∨ (p3 → p3))) ∨ p5) ∧ p5) ∧ False)) → p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (True ∨ (p4 → ((p4 ∧ True) ∨ (((p2 ∨ p1) ∧ p1) ∧ (p1 ∧ False))))) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- False on the left can always be used.
  apply False.elim h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_262246709160821464182013130563 : (True ∧ (((p5 ∨ (((True ∨ True) → (p5 → ((((p2 ∨ p1) ∧ ((True ∨ (p4 → p4)) → p1)) ∨ True) → True))) ∧ p1)) → (p3 ∨ p3)) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248338613397131455915728143862 : ((p2 ∨ p3) ∨ (((False ∨ (True ∧ p4)) → ((False → ((False ∧ p5) → ((p4 ∨ p2) → p5))) ∨ True)) → (p1 ∨ (((p3 ∨ p3) ∨ True) ∨ p1)))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228104269040502317081386626722 : ((p4 ∧ (p3 ∨ False)) ∨ (True → ((((True ∧ False) ∨ (p1 ∧ p1)) ∨ (((p3 → ((p4 ∧ p2) → False)) → False) → True)) ∨ (p4 → (p5 ∨ p2))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323795044955313739128483135164 : (p5 ∨ ((((p4 → (p4 ∨ (p4 ∨ (p5 ∨ True)))) ∧ p3) → ((p4 → (p5 ∨ p1)) → (False ∨ p5))) ∨ (p2 ∨ (p2 ∨ (p1 → (p1 ∧ p1)))))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_143043291664699028480892830560 : ((False → ((p1 ∧ (p1 ∧ (p4 → (((p5 ∧ p1) ∧ (False → ((p4 ∨ p1) ∨ True))) ∧ (False → (True → p2)))))) ∨ p3)) → ((True ∧ p2) → p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_657245942718508730987879058783 : (((((p1 ∨ (True ∨ True)) → (((p2 ∧ False) ∨ (p3 → (p5 ∧ (((p2 ∧ p3) → p1) → p1)))) ∧ (p4 ∧ (p3 ∨ p4)))) ∨ (p2 → p2)) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135192194733243226937827112689 : (((((p5 → ((True → True) → False)) ∨ (((p5 ∨ p2) → (p4 ∨ (p5 ∨ p1))) → (p1 ∨ p3))) → p2) → (p2 ∧ p4)) ∨ (True ∨ (p5 ∧ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206123823587173490213178020266 : ((p4 ∧ ((p4 ∧ p2) ∨ (p4 ∧ p4))) ∨ ((False ∧ (p5 → ((p3 ∧ ((False ∧ (True ∨ p3)) → (p2 ∨ p5))) ∨ p3))) → ((p5 ∧ True) → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322705122357582338848190971776 : (p5 ∨ (((((((p4 ∧ p5) → (True → ((p3 ∧ ((p1 ∧ p3) ∧ (False → p1))) ∨ p5))) ∧ (p4 ∨ p2)) → (p3 → p5)) ∨ True) → False) → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((((p4 ∧ p5) → (True → ((p3 ∧ ((p1 ∧ p3) ∧ (False → p1))) ∨ p5))) ∧ (p4 ∨ p2)) → (p3 → p5)) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66069434812930410029912802583 : ((p5 ∨ ((((False ∨ p1) → False) ∧ (p2 ∧ ((((((True ∨ p2) → p1) ∨ ((True ∧ (p1 ∨ False)) ∨ p2)) ∨ p3) ∧ False) ∨ p2))) ∨ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111746685736742281150131541029 : ((((True → ((((False → p3) ∨ p2) → (((True ∧ p1) ∨ (p1 → (p4 ∨ ((p2 ∧ p3) ∧ p2)))) ∧ p5)) ∧ True)) → p2) ∨ p5) ∨ (False → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_777516205861049140292934039171 : (((p1 ∨ (((((False ∧ p4) ∨ True) ∨ (False ∧ (p3 → (False ∨ p1)))) → (True ∨ False)) → (True → ((p2 ∨ (p5 ∧ p1)) ∨ (False ∨ True))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_641194800130758428058966121128 : (((((p3 ∨ True) ∨ ((p1 → p3) ∧ ((p4 ∨ (p1 → ((((p4 ∨ (p1 → True)) ∨ p1) ∧ ((False → p4) ∧ p2)) → False))) ∨ False))) → p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_668185972462124362480350183977 : ((((p1 → ((p3 ∨ False) ∨ (p2 ∨ (p2 → (((True → ((p4 ∨ (p3 ∨ p2)) ∧ p4)) ∨ p1) → (p5 → p4)))))) ∧ (False ∧ (p3 ∧ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51083908648884648163931564519 : (((p5 → (p2 ∨ ((p4 ∨ ((False ∨ p2) ∨ (False ∨ False))) → (p2 ∧ (False ∧ (p4 → p1)))))) ∧ ((p1 → True) ∧ (p5 ∧ (p1 ∧ p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63074635077615040861916344634 : ((p5 ∧ ((((p4 ∧ (((False → (((True → ((p5 → (p4 ∨ p2)) → (True ∨ p1))) ∧ p4) ∧ p3)) → p2) → False)) → p5) ∨ p5) ∨ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_316610727939541857281183486281 : (p3 ∨ (p4 ∨ ((((p5 → p4) → p2) ∨ ((((True ∧ p1) ∧ p5) ∨ (False → ((p3 ∨ ((p4 ∧ p4) ∧ p1)) → p5))) ∧ (True ∨ False))) ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- False on the left can always be used.
    apply False.elim h1
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- False on the left can always be used.
    apply False.elim h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_727426711662243398279987097179 : ((((p3 ∧ (p2 ∧ p4)) ∨ (((p5 ∨ p3) ∧ ((True → p5) → ((True ∧ False) ∨ (False ∧ (False ∧ (p2 ∨ ((p1 → p3) ∨ p5))))))) ∧ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165298396651359169611106325802 : ((((p4 → p4) ∧ (p1 ∧ ((((p1 ∧ False) ∧ (p1 ∨ p1)) ∧ p5) → p5))) → (p5 ∧ p3)) ∨ (((False ∧ p1) ∨ (True ∨ p1)) ∨ (p3 → p1))) := by
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
theorem thm_5_vars_731634209768516386288594029399 : ((((p1 → (False → True)) → ((((False → p1) → (False ∧ (((True ∧ (((p2 ∧ False) ∧ p3) ∧ (p1 ∨ p2))) → p3) ∨ p4))) → p3) ∧ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_670053033702020560290306692469 : (((((((True → ((p4 → p5) ∧ True)) ∨ p4) ∧ p5) → (((p2 ∨ ((True ∨ (p1 → p1)) → p3)) ∨ p5) ∧ p5)) ∨ (True ∧ (True ∨ True))) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_318864639669109247346554662488 : (p4 ∨ (((((True → (p3 ∨ (True ∧ p4))) → (p2 ∨ ((((False ∨ p4) ∨ True) → False) ∧ p2))) ∨ False) ∨ (True ∨ True)) ∨ (p2 → (p5 → p5)))) := by
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
theorem thm_5_vars_117029440992204847864042536125 : (((p2 ∨ p3) → ((False ∨ p5) ∨ ((p5 ∧ (((p2 → p3) ∧ (p3 ∨ p1)) ∧ (p2 ∧ ((p3 ∨ (p3 → p1)) ∧ False)))) ∧ p1))) ∨ (True ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190763682640796184648174826674 : (((((p1 ∧ (False ∧ p3)) ∧ p1) ∧ True) ∨ (p1 → False)) ∨ (((p3 ∨ p3) ∨ ((p2 ∧ ((True → False) → ((p4 → p4) → p1))) ∨ p5)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249483570447348058098935059838 : ((p5 ∨ p1) ∨ ((((((p4 ∨ (False ∧ ((p1 → p4) ∧ p4))) ∨ ((True ∨ p2) ∧ ((p4 → False) ∨ p4))) ∨ False) ∨ False) ∨ True) ∨ (p1 ∧ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213525843026062891840283155756 : (((p5 → (p4 ∨ True)) ∧ p2) ∨ (((((((p3 ∧ p3) ∧ (p3 ∨ (True ∨ (True ∨ True)))) ∨ (p5 ∧ p1)) ∧ p1) ∨ p3) ∨ (False → p1)) ∨ p3)) := by
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
theorem thm_5_vars_671892030560987787044376027054 : (((((True → (((((((p5 → p3) ∧ False) → p1) ∧ p3) → p4) ∧ (p4 ∨ ((False → p3) ∧ p1))) → p3)) ∧ p4) → ((p2 ∨ p5) → p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197881497533041862740115109203 : ((((False → p4) ∨ p3) → ((p5 → p1) ∨ p2)) ∨ ((False → (p2 ∧ False)) ∨ (p2 ∧ ((p1 ∧ ((False ∧ (p1 → True)) ∨ p2)) → (p5 → p1))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171463755322656529182996605294 : (((False ∨ (((((True ∧ False) → False) ∧ p5) ∨ ((p2 → p2) ∧ p4)) ∨ p2)) ∧ p1) ∨ ((True ∧ (p1 → ((True ∨ (p5 ∨ False)) ∨ False))) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150807410575864485487706956434 : (((((p1 ∧ (True ∨ p2)) ∨ (True ∨ (p4 ∧ (p3 → (p4 ∨ (p4 ∧ (p5 ∨ False))))))) ∨ (p3 ∧ p5)) ∨ p4) → (p4 ∨ ((p1 → p3) ∨ True))) := by
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
        -- Conjunctions on the left can always be decomposed.
        let h5 := h4.left
        let h6 := h4.right
        -- Disjunctions on the left can always be decomposed.
        cases h6
        case inl h7 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h8 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h9 =>
        -- Disjunctions on the left can always be decomposed.
        cases h9
        case inl h10 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h11 =>
          -- Conjunctions on the left can always be decomposed.
          let h12 := h11.left
          let h13 := h11.right
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h12
    case inr h14 =>
      -- Conjunctions on the left can always be decomposed.
      let h15 := h14.left
      let h16 := h14.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h17 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_355606005553997552617556899737 : (p5 → (((False ∨ p1) ∨ ((((p4 ∧ p4) ∨ (((p5 → (False ∨ (p3 ∧ False))) ∨ ((False → p3) → p5)) ∨ p2)) ∧ True) ∨ False)) ∨ (False → p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323712159551449588478143183965 : (p5 ∨ (((((p3 ∧ ((p1 ∧ p1) → p1)) ∧ ((p4 ∧ p3) ∨ p2)) ∧ p3) ∧ (((p1 ∧ True) ∧ p3) ∧ True)) → (False ∨ (False ∨ (False → p1))))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- Conjunctions on the left can always be decomposed.
    let h13 := h3.left
    let h14 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h15 := h13.left
    let h16 := h13.right
    -- Conjunctions on the left can always be decomposed.
    let h17 := h15.left
    let h18 := h15.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h19
    -- False on the left can always be used.
    apply False.elim h19
  case inr h20 =>
    -- Conjunctions on the left can always be decomposed.
    let h21 := h3.left
    let h22 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h23 := h21.left
    let h24 := h21.right
    -- Conjunctions on the left can always be decomposed.
    let h25 := h23.left
    let h26 := h23.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h27
    -- False on the left can always be used.
    apply False.elim h27



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113733308793016776688858871306 : ((((p3 → (((p1 → (((p5 ∧ True) → True) ∧ ((p5 ∨ p2) ∧ p3))) ∨ False) ∨ False)) → (p1 ∧ (False → p3))) → (False ∨ p2)) ∨ (p5 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_196716259910056857912204434110 : ((((((False ∧ p1) ∨ p2) → False) → p3) ∧ p2) ∨ ((p1 ∨ (True ∨ (p4 → (((p4 → True) → ((p4 ∨ p2) → (p5 ∧ p4))) → p4)))) ∨ p1)) := by
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
theorem thm_5_vars_46685301418232477006236955816 : (((p2 ∨ (((False → p4) → p3) ∨ (p1 → ((p1 ∧ ((p4 ∧ p3) → (p4 ∨ ((True ∨ p3) ∧ (p5 ∨ p1))))) ∨ p5)))) ∧ (p3 ∨ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_151426397414105277256700839470 : (((p3 ∧ (p4 ∨ (True → (False ∨ ((p2 ∨ (True ∨ p4)) ∧ (p1 → (p2 ∨ (p3 ∧ p4)))))))) ∧ (p1 → True)) → ((p1 → p2) ∨ (True → True))) := by
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
theorem thm_5_vars_151188623641718827258740882085 : ((((((p1 ∧ (True → (p2 ∨ p3))) ∨ True) ∧ p3) ∨ (((False ∧ (p4 ∨ True)) → True) ∨ (False ∨ False))) → p2) → (p3 ∨ ((True → p3) ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((((p1 ∧ (True → (p2 ∨ p3))) ∨ True) ∧ p3) ∨ (((False ∧ (p4 ∨ True)) → True) ∨ (False ∨ False))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41852693883739586359157241932 : (((((False ∧ p2) ∧ p2) ∨ (p5 ∧ (((True ∨ ((((p3 ∨ p5) ∧ p4) → p4) → ((p1 → False) → p3))) → p3) ∧ (p2 → p4)))) ∨ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_611453161719641485386631545413 : (((((p2 ∧ (((p3 ∨ (p5 ∧ p5)) ∨ p5) ∨ ((True ∧ True) ∧ ((p5 ∨ p4) ∧ (p1 → (((True → p3) ∧ True) ∨ p5)))))) → p1) ∨ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53802580077113338231723721136 : (((((p5 ∧ p4) → ((p2 ∧ p3) ∧ (p1 ∧ p4))) → p3) ∨ (((p5 → (p4 → p4)) → p2) ∧ (p3 ∨ (((True ∧ p1) → p3) → p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351952648612879573680003308327 : (p4 → ((False → (p3 → ((p5 ∧ (p5 ∨ (p4 ∨ p3))) ∨ p3))) → ((p4 → (((p4 → p2) ∧ p3) → p1)) → ((p1 → (False ∧ p5)) ∨ True)))) := by
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
theorem thm_5_vars_734794038563448542430233202035 : ((((p2 ∨ False) ∧ (p3 ∨ (p2 ∧ (((False → (True ∨ (((((p4 ∧ p1) → (False ∨ p2)) ∨ p5) ∨ (p4 ∧ p2)) ∨ p3))) ∧ p3) ∨ p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_90919607089975667237528084519 : (((True → False) ∧ (((False → p3) ∧ (p1 ∧ ((((p5 ∧ ((True → ((p2 ∨ p2) → (False ∨ p4))) ∨ True)) → p2) → p1) → p4))) → False)) → False) := by
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
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135526950545383257208557042939 : (((((p2 ∨ ((True ∧ (p3 ∨ ((False ∨ False) ∧ p5))) → (p2 ∧ p1))) ∨ p3) → p3) ∧ (((True ∧ p2) ∧ p2) → True)) ∨ ((p3 ∨ p2) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_216843659919259593777898956027 : (((p5 ∧ (p4 ∨ p4)) ∧ p4) → (((p1 → p4) ∧ p2) → (((p4 → (p1 ∧ True)) ∨ (((p2 ∨ False) → True) ∧ (p3 ∨ (p1 ∧ p2)))) ∨ True))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42229933355404313529600596958 : (((False ∧ ((True ∧ (((p4 → False) ∨ False) ∨ (p3 ∧ (p4 → p4)))) ∨ ((((p5 ∨ True) ∧ False) ∧ True) ∧ (p2 → (False ∨ p3))))) ∨ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112518189103109003205913981705 : (((((((p5 ∨ ((((p2 ∧ (False ∧ p5)) ∧ True) ∨ p5) ∧ True)) ∨ ((True → p5) → (True ∨ p2))) ∧ p4) → False) → False) → p2) ∨ (True ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305374325998637592583260788474 : (p1 ∨ (((False ∨ (p1 ∧ ((True ∧ p1) ∧ (p3 ∧ p5)))) ∨ (p2 → ((p3 ∧ p5) → True))) ∧ (((False ∨ ((True ∨ p4) ∧ True)) ∨ p2) ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_682402462921680604538640526069 : (((((p3 ∨ (p1 → (p5 → (False ∨ (((p5 ∨ (p2 ∧ False)) ∧ False) → p1))))) → (p1 ∨ p5)) ∧ (True ∨ (((p4 ∧ p4) ∧ p1) → p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_142470944202022454326065823284 : ((p5 ∧ (((p5 → ((p5 ∧ (p5 ∨ p1)) ∧ p1)) ∧ p3) ∨ (False ∧ (p5 ∧ ((True → True) ∧ (True ∧ (True ∨ p5))))))) → ((p5 ∨ p4) → p1)) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
      have h9 : p5 := by
        -- One of the premise coincides with the conclusion.
        exact h4
      -- We have shown the premise of h7, we can now drive its conclusion.
      let h10 := h7 h9
      -- We need to get the right conjuct of h10 based on <expert-advice>.
      let h11 := h10.right
      -- One of the premise coincides with the conclusion.
      exact h11
    case inr h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h12.left
      let h14 := h12.right
      -- False on the left can always be used.
      apply False.elim h13
  case inr h15 =>
    -- Conjunctions on the left can always be decomposed.
    let h16 := h1.left
    let h17 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h17
    case inl h18 =>
      -- Conjunctions on the left can always be decomposed.
      let h19 := h18.left
      let h20 := h18.right
      -- We want to use the implication h19 based on <expert-advice>. So we show its premise.
      have h21 : p5 := by
        -- One of the premise coincides with the conclusion.
        exact h16
      -- We have shown the premise of h19, we can now drive its conclusion.
      let h22 := h19 h21
      -- We need to get the right conjuct of h22 based on <expert-advice>.
      let h23 := h22.right
      -- One of the premise coincides with the conclusion.
      exact h23
    case inr h24 =>
      -- Conjunctions on the left can always be decomposed.
      let h25 := h24.left
      let h26 := h24.right
      -- False on the left can always be used.
      apply False.elim h25



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147057270554358494209203059494 : ((((((p3 ∧ ((False ∨ p3) ∧ p4)) ∧ p1) ∨ (True ∨ p1)) → (p3 ∨ (False ∨ (p4 ∨ (p4 ∨ p3))))) ∧ p5) ∨ (False → ((p2 → p3) ∧ p2))) := by
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
theorem thm_5_vars_69116986788819770379560207281 : ((p5 → ((((True ∧ (p1 ∧ ((True ∨ p5) ∨ p2))) → p5) → (p5 → ((p2 → p1) ∨ ((p5 ∨ p1) → (p2 ∧ p4))))) ∨ (p4 ∨ True))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323514848552452634042352463472 : (p5 ∨ ((True ∧ ((((p3 ∨ (False → False)) ∧ p2) ∧ False) ∧ ((True ∨ p5) ∧ (((p4 ∧ p2) → (p3 ∧ p5)) → p5)))) ∨ ((False → p2) ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_353714172497919505040534966711 : (p4 → (True → (((((False ∧ p2) → ((True ∧ (p1 ∨ ((True ∧ p1) ∨ ((True → False) ∧ ((False ∨ p1) ∧ p1))))) ∧ p2)) ∧ p5) → False) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117096278669632184087016272300 : (((p1 → p4) → (((p4 ∧ ((((((p1 → p3) → p4) ∨ p5) ∨ False) ∧ (p4 ∨ p5)) → (p1 ∧ False))) ∨ (True ∨ p4)) ∨ p2)) ∨ (p4 ∧ p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_304999997165822792200544841919 : (p1 ∨ ((((p2 ∧ (p2 ∨ ((p2 ∨ p4) ∨ ((p5 ∧ ((True ∧ p3) ∧ p3)) → False)))) ∨ False) ∨ (p4 ∨ (True ∧ p1))) ∨ ((False ∨ False) → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- False on the left can always be used.
    apply False.elim h2
  case inr h3 =>
    -- False on the left can always be used.
    apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39219679624882663179433708576 : (((True ∧ ((p3 → (p2 → p1)) ∨ (((p2 ∨ ((p5 ∨ False) ∨ (p4 ∨ p1))) ∧ p3) → ((p4 ∧ (False → (p5 → False))) ∨ False)))) ∧ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_327851253996957086422462038517 : (True → (((((p5 ∧ (False ∨ True)) ∧ p2) → p5) ∧ (True → ((p5 → ((p1 ∨ (p4 ∧ p5)) ∧ (p4 → p5))) → (p3 ∨ p1)))) ∨ (True ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_624735478483217665216448561829 : ((((p4 ∨ (p4 → ((p4 → ((p4 → ((p3 ∨ p5) → (p3 ∧ (p5 ∨ (p3 → p5))))) ∧ p4)) ∨ (p2 ∨ (p4 ∨ (p3 ∧ p1)))))) ∨ False) ∨ p3) ∧ True) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_789603026194105974313318488311 : (((p5 ∨ ((p4 → ((p4 → (p4 → (False ∧ p2))) ∨ p5)) ∨ ((p1 → ((p1 ∧ True) → (p4 ∧ (False ∨ ((p5 → p2) → p5))))) → p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_610892167360111641192889015273 : ((((((((True ∧ False) ∧ True) → (p2 → (p5 ∧ ((p2 → p1) ∨ p4)))) ∨ ((p3 ∧ (p5 ∧ p3)) ∨ ((p3 ∧ True) ∧ p1))) → p4) ∨ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137242748108101070125387500294 : ((p1 ∧ ((((p5 ∧ p1) → (True ∧ ((False ∧ p4) → p1))) ∨ (p1 → p5)) ∧ ((((True → p5) ∨ p2) → p4) ∨ p5))) ∨ ((p5 ∧ False) → False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149449308999716176766628793481 : ((False ∧ ((((p5 ∧ p1) ∧ (p5 → (p2 ∨ True))) ∧ ((p4 ∨ ((p1 ∧ False) ∨ p2)) ∨ (p3 ∧ True))) → p3)) ∨ (True ∨ (p5 ∧ (p1 ∨ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43682448361511386540802730986 : (((((p2 ∧ (((p3 ∧ ((p4 → (p3 ∨ p1)) ∧ p3)) ∨ True) ∨ True)) → (False ∧ ((p5 ∨ (p5 ∧ p1)) ∨ (False ∨ p5)))) → p1) → p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324085369023365971365478501199 : (p5 ∨ (((p2 ∨ (p2 ∨ p2)) → (((False ∨ p5) ∧ False) ∨ (p4 ∨ True))) ∨ (((p4 ∨ True) ∨ p4) ∧ (((False ∧ (False → False)) ∨ p2) → True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_355564614761936149092604534463 : (p5 → (((p4 ∧ (((p1 → p2) ∨ ((p3 → (((p3 → True) ∧ True) → p1)) ∨ p2)) ∨ ((True → True) → p4))) ∨ (False → p3)) ∨ (p2 ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2459733804893306461620238019 : ((((False ∧ (False ∧ p4)) ∧ False) ∧ (p2 ∧ (False → False))) ∨ ((p5 → ((p2 ∨ ((((p2 ∨ p4) → False) ∨ p3) ∧ True)) → p1)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134316718166165600606631436955 : (((False ∧ (p5 ∨ (((((p3 ∧ ((p5 ∧ p1) ∧ p1)) ∨ (p5 → p5)) ∨ ((True → p3) ∨ p3)) ∧ p3) ∧ False))) ∨ True) ∨ ((True ∨ True) ∧ True)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159259304757249690440219947352 : ((p3 → (p4 ∨ ((p2 ∨ (p1 ∨ (False ∨ ((True → (p5 → p4)) ∧ (p2 ∨ (p3 ∧ p2)))))) ∧ False))) ∨ ((True → False) → (p4 ∨ (p4 → p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_786970005626193026975190349671 : (((p4 ∨ ((p4 ∧ p1) ∧ (p5 ∧ ((False → ((((p5 ∧ (p2 → (p2 ∨ p4))) ∧ p4) ∧ (p5 → p4)) → ((p2 ∨ False) → p3))) ∧ p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_724114247990271964125552343728 : ((((p2 ∧ (p4 ∧ True)) ∧ (((p3 ∧ (p5 → p5)) ∨ (((p5 ∧ p1) → p3) ∨ True)) → ((False ∧ ((p4 ∧ (p4 → p2)) → True)) ∧ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46312809043327287428237764522 : (((((p2 → (False ∧ True)) ∨ (p3 → (p3 ∨ (p5 → (p1 → ((p2 → p1) ∨ False)))))) ∧ (p5 ∨ (False ∧ (p3 → p3)))) ∧ (p5 ∧ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42161454728294494426979074927 : ((((p3 → p2) → (((p2 → (((p1 → p3) ∧ ((p1 ∧ p4) ∨ p1)) ∧ ((True ∨ p4) ∨ False))) ∨ ((p3 → False) ∧ p3)) ∨ True)) ∨ True) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192524144062418603902998066081 : ((((False → False) → (p3 ∨ ((False ∧ p5) → p2))) ∨ p2) → ((p4 ∨ ((p3 ∨ ((True → ((p5 ∨ p4) ∧ p4)) ∧ p2)) ∧ (p3 ∧ False))) ∨ True)) := by
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
theorem thm_5_vars_355631171016718488642750443548 : (p5 → ((p4 ∨ (p5 ∧ (p4 ∧ (True ∧ ((((p5 → (False ∧ p2)) ∨ True) → (False → (p2 ∧ p2))) → (p5 → (p5 → p1))))))) ∨ (True ∧ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64171509683744921864219734018 : ((False ∨ ((p2 ∨ p4) ∨ (False ∧ (p4 → (((True → ((p3 ∨ p4) ∧ ((False ∨ ((p4 ∨ p3) ∨ (p1 ∨ p5))) ∧ p2))) → p2) → p5))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67767329682367983811539897340 : ((p2 → ((((((p2 → p3) ∨ p1) ∨ p2) ∨ p2) ∧ ((p1 ∨ (p2 → ((p2 → False) ∨ (True ∨ (p5 ∨ p5))))) → (p1 ∧ False))) ∨ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245415907346479920975665848158 : ((p2 ∧ p4) ∨ ((p4 ∨ ((p1 ∧ (((p3 ∧ (((p1 ∧ p1) ∧ True) → p1)) → p5) ∧ ((True ∧ p1) → True))) ∧ (p1 → p1))) ∨ (False → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225763578781188776798823551730 : (((p5 → False) ∧ True) ∨ ((p1 ∨ (((((p1 ∧ (p3 ∧ False)) → (p3 ∧ p5)) ∧ ((p1 ∧ p5) ∨ p3)) ∧ ((p1 ∨ p4) → True)) ∨ True)) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136026170237364903330625809977 : (((((p1 → p1) → (p2 → p2)) ∧ (p2 → (p2 ∨ p2))) → (p1 → (((p1 → p4) → p5) ∧ ((p2 ∨ p4) ∧ True)))) ∨ ((p1 ∧ p4) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50928504193599401837044960250 : ((((p1 ∧ ((p4 ∧ (False ∧ (((p3 ∧ p1) ∧ p1) ∧ p5))) → p5)) ∨ (p3 ∧ (p4 ∧ p4))) ∧ ((((p4 → False) ∧ p1) ∧ p1) ∧ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112133341357470157465706326211 : (((False ∧ (((p4 ∧ p4) ∧ ((((False ∧ True) → p4) ∨ p1) ∧ (p3 ∧ (p1 ∧ True)))) ∨ (True → (p1 → (p2 ∧ p2))))) ∨ True) ∨ (False → p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314784776101653381493943547058 : (p3 ∨ ((p1 ∧ ((p1 → ((((p4 ∧ False) → p5) ∧ (False → True)) ∧ p3)) → True)) → (p1 → ((p1 ∨ True) → (p1 → (True → (p5 ∨ p1))))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h5
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h1.left
    let h8 := h1.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h1.left
    let h11 := h1.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263080323126808351437073748757 : (True ∧ ((((((p5 → ((p2 ∧ True) ∨ p4)) → p3) → (((p5 → True) ∨ p5) ∧ (False ∧ p5))) ∨ ((p4 → True) → p3)) ∨ p1) ∨ (False → p4))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149883813941919391575217847468 : ((p2 ∨ (((((p3 → p4) → p4) ∨ True) → p1) → ((p2 → (False ∨ (p2 ∨ (p4 → (True ∧ p2))))) → p1))) ∨ (((p2 ∨ p5) → p2) ∧ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : (((p3 → p4) → p4) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114278551858136523774244985045 : ((((p4 ∧ (p5 ∧ (((p2 → False) ∧ True) → (False ∧ (False ∧ (True ∨ (False ∨ p4))))))) ∨ p1) ∧ (p3 → (False ∧ (p1 → p5)))) ∨ (p3 → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_709714919894213586581539863916 : ((((True → ((p2 ∨ (p4 ∨ p1)) ∧ (False ∧ p5))) → ((p3 ∧ ((p5 ∧ p5) → ((p1 ∧ (False ∧ (p3 → p3))) ∨ p4))) ∧ (p5 → False))) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
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
  -- Implications on the right can always be decomposed.
  intro h6
  -- Conjunctions on the left can always be decomposed.
  let h7 := h6.left
  let h8 := h6.right
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h9 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h10 := h1 h9
  -- We need to get the right conjuct of h10 based on <expert-advice>.
  let h11 := h10.right
  -- We need to get the left conjuct of h11 based on <expert-advice>.
  let h12 := h11.left
  -- False on the left can always be used.
  apply False.elim h12
  -- Implications on the right can always be decomposed.
  intro h13
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h14 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h15 := h1 h14
  -- We need to get the right conjuct of h15 based on <expert-advice>.
  let h16 := h15.right
  -- We need to get the left conjuct of h16 based on <expert-advice>.
  let h17 := h16.left
  -- False on the left can always be used.
  apply False.elim h17
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_344787977241223372147788164342 : (p2 → (p4 → (((False ∨ ((p1 ∧ (False ∨ p5)) ∧ p4)) ∨ ((p3 → ((p2 → (p2 ∧ (p5 → p1))) ∧ False)) → False)) ∨ ((p2 ∨ p2) ∧ p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49186261156173690601388457609 : (((((p1 ∨ True) ∨ (p1 ∨ False)) → (((((p2 → (p2 → p4)) → (p4 ∨ (p1 → p5))) ∨ True) → p3) ∨ p2)) ∨ (p1 ∨ (True ∨ p4))) ∨ p4) := by
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
theorem thm_5_vars_218626333352425966686073055000 : ((True ∧ ((True ∨ p2) ∧ p4)) → (((p5 ∨ (p5 ∨ (False ∧ ((True ∨ p3) ∨ (True ∨ (p2 ∨ p3)))))) ∨ ((True ∨ (p3 ∧ p2)) ∨ True)) ∨ p5)) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h7 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47497346073542884158483565569 : (((p1 ∨ (((((p5 ∧ (True → (p1 ∧ (p4 ∧ p1)))) ∨ ((False ∨ p2) ∨ False)) → p1) → (False ∨ p5)) ∧ (False ∧ p1))) ∨ (p2 ∨ True)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



