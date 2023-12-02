variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_122156752526390459888405016499 : ((((((p1 ∧ (p5 ∧ p5)) ∨ ((p3 ∨ (p3 ∨ False)) → p3)) ∨ ((p3 ∧ ((p3 ∧ p5) ∧ p4)) → p1)) → p2) ∧ (p3 → p3)) → (p4 ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (((p1 ∧ (p5 ∧ p5)) ∨ ((p3 ∨ (p3 ∨ False)) → p3)) ∨ ((p3 ∧ ((p3 ∧ p5) ∧ p4)) → p1)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- One of the premise coincides with the conclusion.
        exact h8
      case inr h9 =>
        -- False on the left can always be used.
        apply False.elim h9
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h10 := h2 h4
  -- One of the premise coincides with the conclusion.
  exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256683874545503200540081888873 : ((p1 ∨ False) → (p3 ∨ (((True ∨ (p4 ∧ (((p4 ∨ p4) ∧ p5) → p5))) ∧ ((p4 → p5) → ((p5 ∧ p3) ∧ ((False ∧ True) → p4)))) ∨ True))) := by
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
    -- False on the left can always be used.
    apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_144427475630987598930914846533 : ((((True → ((((p5 → p3) ∨ p5) ∨ (p2 ∨ ((p4 → True) ∨ False))) ∨ (p1 ∨ p1))) ∨ p3) ∧ (True → True)) ∧ (((p2 → p4) → p1) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115197602990337974703321725343 : ((((p2 → p1) ∧ (True → (p1 → ((True ∨ p5) → p3)))) ∧ (((False ∧ (p4 ∨ (p2 ∨ p5))) ∨ p3) ∨ ((p1 → True) → True))) ∨ (False ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62660702803189440753612047470 : ((p4 ∧ (((False ∨ ((p4 ∨ (((p5 ∨ p4) ∧ p2) → (False ∨ p1))) ∧ ((p2 → (p2 ∨ p1)) ∨ False))) → (p3 ∧ (p3 ∧ p1))) ∨ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_151081887180480009961911415719 : ((((p3 ∧ (((True ∨ False) → (p5 → p1)) ∧ ((p3 ∨ (False → ((p5 ∨ p3) → False))) → False))) ∨ p5) → p5) → ((True → p4) ∨ (False ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_203874851599940216688350751531 : ((p1 → (((p5 ∨ p2) ∧ p1) ∨ True)) ∧ (p4 → (p5 → (((p4 → (((True → True) ∧ (p1 → (p3 ∧ p5))) → False)) ∨ (p5 ∨ p4)) ∨ p4)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_606353751314975121429881715176 : (((((((((p5 ∧ p1) ∨ p3) ∧ (((False ∧ ((p2 → False) ∨ p1)) ∨ (p1 ∧ True)) ∨ (p2 → p3))) ∨ (False ∧ p2)) ∨ p1) ∧ False) ∨ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187436277113978229050621282198 : ((p5 ∧ (p4 ∧ (((p1 ∨ p1) ∧ p2) ∨ (p1 ∧ (p1 ∨ p3))))) → (((((p2 ∧ (False ∨ p2)) ∧ p3) ∨ ((p5 → True) → p5)) ∨ True) ∨ p4)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h9 =>
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
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h14 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h15 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_125770959087922240091389861819 : (((True → p4) ∨ ((False ∨ p4) → (p2 ∨ ((p1 ∧ True) ∧ (p4 → ((p3 → ((p1 ∧ p3) → ((p2 ∧ p5) → p3))) ∧ p2)))))) → (p4 → p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h4 =>
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_348196816879637415510441968639 : (p3 → ((True → p1) → (((True → (True ∧ (p4 ∧ p1))) ∧ ((p1 ∨ True) → ((p1 → p1) ∨ p3))) → (p5 → ((p2 ∧ (p3 ∨ p2)) ∨ p4))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h7 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h8 := h5 h7
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- We need to get the left conjuct of h9 based on <expert-advice>.
  let h10 := h9.left
  -- One of the premise coincides with the conclusion.
  exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_738493358813020870175455831954 : ((((p1 ∧ p3) ∨ (p2 ∨ (((False → p4) ∨ ((p3 ∧ p3) → ((p3 ∨ (p5 ∧ p2)) → (p5 ∨ p5)))) → (((p2 → p1) ∧ p4) ∧ p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61379990372673114658711687114 : ((p1 ∧ (((False ∨ (False → ((p1 ∧ ((((p2 ∧ p5) → (p2 ∧ False)) ∧ (False → ((True ∧ p2) → False))) → p1)) → True))) → p3) ∨ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_809793455884196420585189109988 : (((p5 → (((True ∧ False) ∨ (((p2 → ((False ∧ (p3 ∨ p1)) ∧ p1)) ∧ ((p3 ∨ p5) → p3)) ∧ ((p3 → p2) → p3))) ∨ (p3 ∨ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43091454998251941341054218203 : ((((((((p1 → p1) ∨ ((p4 → ((p1 ∨ p1) → (p2 → p3))) → p4)) ∧ (p4 ∨ p5)) ∨ (p4 → p2)) → (p3 ∧ p1)) ∧ p5) → p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_80915212176395193172356304593 : ((((((((True ∨ ((False ∧ (p3 → p4)) → (False → p1))) ∧ (p2 ∨ p5)) → p1) ∧ p5) ∨ (p2 ∨ p1)) → False) ∧ ((False → p2) ∧ p1)) → p5) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h6 : (((((True ∨ ((False ∧ (p3 → p4)) → (False → p1))) ∧ (p2 ∨ p5)) → p1) ∧ p5) ∨ (p2 ∨ p1)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h7 := h2 h6
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178565533621165943032717078444 : ((((True ∨ p5) ∧ ((p4 ∧ p4) → p5)) ∧ (((p5 ∧ p5) ∧ True) ∨ False)) ∨ ((True → ((p3 ∨ (True ∨ p2)) ∨ ((p1 → p3) ∧ p2))) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_748715458080258243853532379622 : ((((p3 → p4) → (((p1 → ((p1 → True) → p5)) ∧ p5) → ((p2 ∧ ((p3 ∧ p4) ∨ (p3 ∧ (p1 ∨ (p4 ∧ p1))))) ∨ (p4 ∨ p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47354463809100943947872302602 : ((((p2 ∧ True) ∨ ((((p5 → (((p3 ∨ p3) → (p3 ∨ p1)) → True)) → p4) ∨ ((p1 ∨ (False → p4)) ∨ p1)) ∨ p4)) ∨ (p4 ∧ p2)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_262283925312353518709668550552 : (True ∧ ((((((p4 ∨ (p5 ∧ (((p4 ∨ (p1 ∧ True)) ∧ True) ∨ p2))) ∨ p5) ∨ p4) ∨ p5) ∨ (True ∧ (((p3 → True) ∧ False) → p2))) ∨ p2)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_131403600376571897126669053526 : (((((True ∧ p1) ∧ False) ∨ False) ∨ ((p5 ∨ (True → (p5 ∧ (((p2 ∧ p1) → p4) ∧ False)))) → (True → (False ∨ p5)))) ∧ ((False → True) ∨ p3)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h5 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h6 := h4 h5
    -- We need to get the right conjuct of h6 based on <expert-advice>.
    let h7 := h6.right
    -- We need to get the right conjuct of h7 based on <expert-advice>.
    let h8 := h7.right
    -- False on the left can always be used.
    apply False.elim h8
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h9
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_732682151934147664802134966027 : ((((p1 ∧ p3) ∧ ((((p5 → (False ∨ (p2 ∧ (p3 → ((False ∧ (p5 → p1)) ∧ (p3 ∧ False)))))) ∧ p1) → ((p3 → p1) → True)) → p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116718905466744388358207969066 : (((p2 ∧ p2) ∨ ((False → ((p4 ∨ ((p3 → ((p3 ∧ p4) ∧ p1)) ∧ p3)) → (False ∧ p5))) → (p2 → (p5 ∧ (p4 → p2))))) ∨ (True ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57160137384889163267404133610 : ((((p1 ∧ p1) ∨ p1) ∨ ((p1 ∨ ((((p5 ∨ p3) ∨ p1) → True) ∧ False)) ∧ (False ∧ (((p1 ∨ ((p5 ∨ p1) ∨ True)) ∧ False) ∨ False)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63961262094204099181874045827 : ((False ∨ ((((((True → p5) → p4) ∧ (((False ∨ p4) ∨ True) ∧ (p5 ∨ p5))) ∨ ((p1 → (p3 ∧ (p2 → p2))) → p4)) ∧ p1) → p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53881361802645822948493234901 : ((((p4 ∧ True) → (p2 ∨ (p5 ∧ ((p1 ∧ True) ∨ p1)))) ∨ (p2 → (p5 ∨ ((p4 ∨ (True → p2)) ∨ ((p3 ∧ (p1 → False)) ∧ p4))))) ∨ p5) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45396265222412388715076369297 : (((p5 ∧ ((((p1 → (False ∧ p2)) → ((p3 ∧ (p2 ∨ p5)) ∧ ((True → False) ∧ p1))) ∨ ((p4 → p3) ∧ p3)) → (False ∧ p1))) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41832346540213983366625215658 : ((((False ∧ (p3 → p5)) ∧ (True → (((p5 ∧ (p2 → (p3 ∧ (p5 → ((((p2 ∧ p4) ∧ p4) ∧ p1) ∨ p3))))) ∧ p1) ∧ p3))) ∨ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1945657411047728582073105502 : (((((((((p1 ∧ True) → p3) ∧ (p1 → False)) ∧ p4) ∧ ((p4 ∨ False) ∧ p5)) → p2) ∨ True) → p5) ∨ (((p2 ∧ p4) → False) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57897165919711693677064992274 : (((p3 ∨ (p5 ∨ p3)) → (p1 ∨ (((True ∧ ((p1 ∧ p5) → (True → (p1 ∧ p4)))) ∨ ((True ∨ p3) ∨ (p1 ∨ (p3 ∨ p3)))) → p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_252797049439118056963299768466 : ((True ∧ True) → (p2 ∨ (p4 → (p1 ∨ (p1 → ((p3 ∨ (p5 ∧ ((False ∧ (((False ∧ True) ∧ p3) ∧ ((p2 ∧ True) ∧ p1))) ∨ p1))) ∨ p4)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h5
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56474280547585108693239042988 : ((((True → p4) → (p1 → p2)) → (True → (((p4 ∨ p2) ∨ (False ∨ ((((p4 ∧ p1) ∨ p1) ∧ ((p4 → p3) ∨ True)) ∨ p3))) ∧ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172106194177990878165276934778 : (((False → (((True → (False → p1)) → (p1 ∨ p1)) ∨ (False ∨ p5))) → (p2 ∧ p4)) ∨ ((True → p1) ∨ ((p5 → ((True → p5) ∨ p5)) ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_353387204272912007175271393781 : (p4 → (False ∨ (True ∧ (((True → (((p5 ∨ p5) ∨ ((False ∨ p3) ∧ True)) → p1)) → (((p3 ∨ (True → p3)) ∧ p2) ∧ False)) ∨ (True ∨ p2))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
theorem thm_5_vars_775253852773166838896316210362 : (((False ∨ ((True → False) → (p2 ∨ (((p4 → (p3 ∧ (((p3 ∨ False) → (p2 ∧ (p1 ∨ p1))) → (p3 ∨ (p2 ∨ False))))) → p4) ∧ True)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197335638468112213030263016806 : ((((p4 → p4) → ((False → p5) ∧ p5)) → False) ∨ (p2 ∨ (p2 ∨ ((((False → p5) → p5) ∧ (((p3 ∧ (True ∨ False)) → p2) ∧ p5)) ∨ True)))) := by
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
theorem thm_5_vars_605537014717127121822428245976 : ((((p3 → (p5 ∨ ((True ∧ (p4 ∧ False)) ∨ (((False ∨ (p2 ∨ p1)) ∨ p5) ∨ ((p1 ∨ ((p1 ∧ p4) ∨ (p5 → p2))) ∨ p5))))) ∧ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218107493476313605443701092943 : (((p1 → False) ∧ (p5 → p2)) → (p4 ∨ ((p4 ∨ (p2 → (((p1 → (True ∧ ((p5 ∨ False) → p2))) → (p1 ∧ p4)) ∨ (p4 → p2)))) ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h5
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148049058889294784142401505015 : (((p4 ∧ ((p5 ∧ (False → False)) → ((((p5 ∧ ((p1 → p3) → p1)) → True) ∨ p1) → p1))) ∨ (p3 → p2)) ∨ (p4 → ((True ∧ False) → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_708949596733587773257078415261 : (((((((False ∨ p2) ∨ True) ∧ False) → (p5 ∧ False)) → ((p5 → p2) ∧ (p4 ∨ (p4 ∨ (((((p5 ∨ True) ∧ False) → p3) ∧ True) ∨ False))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_777501269734889896132867077217 : (((p1 ∨ ((True ∧ ((((p1 → p2) ∧ p1) ∨ False) → (((p5 → p1) → p4) → p3))) ∨ (((p2 ∧ p4) → p1) ∨ (False → (p2 ∧ p4))))) ∨ False) ∧ True) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40817140638875809848809215620 : ((((p4 ∨ ((p3 ∨ ((p4 → ((p2 ∧ p3) → False)) → True)) → ((p5 → p2) → ((True ∧ (p4 ∨ False)) → (p5 → True))))) → p3) ∨ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_792558301274055944969448464588 : (((True → (((((True → False) → p3) → (p4 ∧ False)) ∧ True) ∨ (((False → (False ∨ (((p4 → (False ∧ False)) → False) ∨ p2))) ∨ p1) → p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173319721029736377697086165036 : ((p2 → ((p1 ∧ ((False ∧ ((p1 ∧ ((False → p3) ∧ p1)) → p3)) → True)) ∨ False)) ∨ (p3 → ((p3 ∧ (((False → p4) → False) ∨ p1)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147947173456137796671750324143 : ((((p3 ∨ p1) → (((p2 ∧ p5) ∨ p5) → (p4 ∨ ((p1 ∨ True) ∨ (False ∧ (True → False)))))) ∧ (True → True)) ∨ (((p4 → p2) ∧ p3) ∧ p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h7
  case inr h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h10
  -- Implications on the right can always be decomposed.
  intro h11
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225957498332292955286602496230 : (((p3 ∧ True) ∨ p2) ∨ ((((p5 ∧ (p1 → (((False ∨ p5) ∧ p4) ∧ p5))) → p3) ∨ p3) → ((p2 ∧ ((p5 ∨ p1) ∨ p2)) → (p4 → p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h8 =>
        -- One of the premise coincides with the conclusion.
        exact h3
      case inr h9 =>
        -- One of the premise coincides with the conclusion.
        exact h3
    case inr h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h11 =>
        -- One of the premise coincides with the conclusion.
        exact h3
      case inr h12 =>
        -- One of the premise coincides with the conclusion.
        exact h3
  case inr h13 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h14 =>
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h15 =>
      -- One of the premise coincides with the conclusion.
      exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338620863931025014383291669422 : (p1 → ((p4 ∨ (False → p4)) → ((((True → ((p4 → p5) ∨ (p2 ∨ ((p5 ∨ p5) ∧ False)))) → p2) → (False ∧ p2)) ∨ ((p1 ∨ False) ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_142758759763535699814149180001 : ((p2 ∨ (p2 ∨ (p2 ∧ (p1 ∧ (((True → False) → ((p5 → (p2 → (True ∧ (False ∧ p1)))) → p1)) ∨ (p1 ∧ p2)))))) → ((False ∧ p3) ∨ p2)) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h6
      case inr h11 =>
        -- Conjunctions on the left can always be decomposed.
        let h12 := h11.left
        let h13 := h11.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_634628055800793786860584358763 : (((((True → (((((p5 → p4) ∨ p4) → ((((p1 → False) → (p4 ∧ p1)) ∧ p3) ∧ p3)) ∨ True) ∧ False)) ∧ ((False ∧ False) ∨ p4)) → False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54302252835038665331500571120 : ((((p3 ∨ p3) ∨ ((p2 ∧ (p4 ∨ True)) ∨ p2)) ∧ ((((((True ∧ (p2 → p5)) ∨ (p1 ∧ p4)) → p4) ∧ False) ∨ p2) ∧ (p4 ∧ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_201760613190299426083821143757 : ((((p5 ∨ (p4 ∧ p4)) ∨ False) ∨ True) ∧ (((p3 ∨ ((p2 ∧ p5) ∨ False)) ∨ ((p4 → (p3 ∨ (p2 ∨ p5))) ∨ (p4 ∨ True))) ∨ (p2 ∧ p4))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
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
theorem thm_5_vars_178249339183962206464191092291 : (((((p5 ∧ p2) ∧ (((p2 ∧ p5) → p4) ∧ p2)) ∨ p5) ∧ (p5 → p3)) ∨ ((p5 ∨ True) ∨ (((p1 → p3) → True) → (p1 → (True → p1))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_713306535651842261249737249318 : ((((p5 ∨ ((True ∨ (p1 ∧ False)) → p1)) ∨ (((p3 ∧ (p3 ∧ p5)) ∧ ((p1 ∨ (True → p4)) ∨ ((p4 ∨ p1) → True))) ∨ (False → p2))) ∨ p2) ∧ True) := by
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
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_792871127173291495440581395779 : (((True → (((p1 → p4) ∨ True) → (((p3 ∨ True) ∨ False) → ((p4 ∧ (p3 → (((p4 ∧ p1) ∨ (p4 ∨ p1)) → p5))) ∨ (p4 ∧ True))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164572754965427929036783739186 : (((((p1 ∧ p2) ∧ p3) ∨ (False ∨ ((p5 → ((p2 ∧ True) → p5)) → (False → p3)))) ∧ p1) ∨ ((False → (p5 → (p2 ∨ True))) ∨ (p5 ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135866681624581499904614907138 : ((((((p4 ∧ ((p3 ∧ False) → p4)) ∨ p1) → p4) → (p5 ∧ p2)) ∨ (True → (((p4 → p3) ∧ (p4 ∨ True)) → p5))) ∨ ((p1 ∧ p3) → p1)) := by
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
theorem thm_5_vars_190119261987661362429768058609 : ((((True ∧ (True ∧ p1)) ∨ (p5 ∧ (p3 ∨ True))) ∧ False) ∨ ((((p1 → p3) ∨ ((p4 ∧ (p4 ∨ p4)) → (True ∨ p3))) ∧ p3) ∨ (False → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_589243537708349176185679929286 : ((((((((p5 ∧ True) → (p5 ∨ p2)) ∧ (((False ∧ p1) → ((p2 ∧ (True ∨ (p5 → True))) ∨ p5)) → (p4 → p2))) ∧ True) → p5) ∧ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158634749578918111806984834466 : ((p1 ∧ ((p1 ∧ (((p4 ∧ ((p4 ∧ (((True ∧ False) ∨ False) → p1)) ∨ p5)) ∧ True) ∧ p4)) ∨ True)) ∨ (p1 → (True ∧ ((True ∧ p1) ∨ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40540867405835860955842219974 : ((((p4 ∨ (((((p3 → p4) ∧ p4) → (True → p3)) → ((True → False) → (((p1 → p4) ∨ p3) ∨ p1))) ∨ (p4 ∨ p2))) ∨ p1) ∨ p3) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_153612461988797167643027506115 : ((p1 → ((((p5 → (p2 ∧ ((p5 → True) ∧ p3))) → ((p4 ∧ p1) ∨ True)) ∨ ((p1 ∧ p4) → p1)) ∧ True)) → (p3 ∨ ((p2 ∨ p5) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354383924579153180319539326058 : (p5 → ((((p1 → (p3 ∨ p5)) ∧ p1) → (((p2 ∧ (p1 ∧ ((p4 ∨ p2) ∧ (((p4 ∧ p5) ∧ False) ∨ p4)))) ∨ p2) ∨ (True ∨ p2))) ∧ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118469757970242691524400901145 : ((p3 ∨ ((((((True → p4) ∨ p3) → p5) → (p2 ∨ (p4 ∨ p1))) → ((False ∧ False) ∧ (p1 → ((p2 ∧ p4) ∧ p3)))) → p3)) ∨ (p2 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_216042244768713740480131718651 : ((p5 ∨ ((p3 → p4) → p3)) ∨ (p2 ∨ ((((False → (False ∨ True)) ∧ (True ∨ True)) ∨ ((((p5 ∧ p2) ∨ True) ∨ p1) ∨ (p5 ∧ False))) ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_53613692872631177694313143308 : ((((True ∨ ((p3 → (p5 → False)) ∨ p1)) ∨ (p2 ∧ True)) ∧ ((p2 → ((p1 ∧ (True ∨ (((p1 → False) ∧ p4) → p5))) → p3)) ∨ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300351886288737778839675401653 : (False ∨ (((((((((p5 ∧ (p4 ∧ (p2 → p4))) ∧ (p5 ∧ True)) ∧ p1) ∨ True) ∧ p1) ∧ (p2 ∧ True)) ∧ False) ∧ p5) ∨ (p2 → (True ∨ p1)))) := by
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
theorem thm_5_vars_337092279045091087215630446432 : (p1 → (((True → (((True ∧ p4) ∨ ((p5 ∨ True) ∨ p5)) ∨ p3)) ∧ (p3 ∧ ((p1 ∧ (False ∨ p5)) ∧ (p1 ∨ (p5 ∨ p1))))) ∨ (p1 ∧ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_714745592697120184758185455814 : ((((True ∧ (False ∨ ((True → False) ∨ p5))) → ((((False → ((p4 → True) → p4)) ∧ p3) ∨ p2) ∨ ((p3 ∧ ((p5 ∧ False) ∨ p3)) ∨ p5))) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h7 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h8 := h6 h7
      -- False on the left can always be used.
      apply False.elim h8
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h9
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_262437144609946935083929283712 : (True ∧ ((p4 ∧ (p1 → ((((p3 ∨ p1) ∧ ((((p1 ∧ (False → p4)) → p1) → p3) ∧ True)) ∧ (p3 ∨ (p1 → True))) ∧ (p5 → True)))) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231448005545579293412802598936 : (((p2 → p2) ∨ p5) → (((p3 ∨ (False ∧ p4)) ∧ (p1 ∧ (((p4 → (True → True)) ∧ ((p3 ∨ True) ∨ p4)) ∨ p5))) → ((False ∧ p5) ∨ p1))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- Disjunctions on the left can always be decomposed.
        cases h11
        case inl h12 =>
          -- Disjunctions on the left can always be decomposed.
          cases h1
          case inl h13 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h6
          case inr h14 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h6
        case inr h15 =>
          -- Disjunctions on the left can always be decomposed.
          cases h1
          case inl h16 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h6
          case inr h17 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h6
      case inr h18 =>
        -- Disjunctions on the left can always be decomposed.
        cases h1
        case inl h19 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h6
        case inr h20 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h6
    case inr h21 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h22 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h6
      case inr h23 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h6
  case inr h24 =>
    -- Conjunctions on the left can always be decomposed.
    let h25 := h24.left
    let h26 := h24.right
    -- False on the left can always be used.
    apply False.elim h25



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55845893916490184788877763692 : (((p2 ∧ ((p4 ∨ False) ∧ p5)) ∧ ((((p4 → ((p5 ∧ p4) ∧ p2)) → p5) → p2) ∨ (((p5 ∨ ((True ∧ p3) ∧ p1)) ∨ p2) ∧ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118488268859899195247698603390 : ((p3 ∨ ((((False ∧ ((False ∨ (((True → (p4 ∧ p2)) → p5) ∨ (p5 ∨ p4))) ∧ p4)) → p2) ∧ p4) → ((p2 ∨ True) ∨ False))) ∨ (p5 ∨ p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248848518792482182692129712150 : ((p3 ∨ p4) ∨ (p1 ∨ (((p4 ∧ p3) ∨ True) ∨ (((p1 ∧ (((p2 ∨ ((p2 → p4) ∨ p3)) ∧ (p3 ∧ p3)) ∨ p4)) ∨ (p3 ∨ p1)) ∧ p1)))) := by
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
theorem thm_5_vars_159789436034026372892537338574 : (((True ∧ (p5 ∨ (True → ((p3 ∧ p4) ∧ ((p5 → p1) ∨ ((p5 → p2) ∨ (p2 ∧ False))))))) ∨ p2) → (p2 ∨ ((p2 ∨ (p5 → p1)) → True))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h10
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178089156750462237481955874327 : (((((p3 ∧ p5) ∨ (p4 → (p3 ∧ ((False ∧ p4) ∧ p1)))) → p4) → False) ∨ (p1 → ((((p3 ∨ p2) → (True ∧ p4)) → False) ∨ (True ∨ p3)))) := by
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
theorem thm_5_vars_264626081259694393157083234730 : (True ∧ (((p1 ∨ p3) → p3) → (((((p1 ∨ (True ∧ (((p3 ∨ (p3 → p2)) ∧ p5) → p5))) → p5) → p5) → p4) → (p4 ∨ (p4 → p2))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (((p1 ∨ (True ∧ (((p3 ∨ (p3 → p2)) ∧ p5) → p5))) → p5) → p5) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h5 : (p1 ∨ (True ∧ (((p3 ∨ (p3 → p2)) ∧ p5) → p5))) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- Implications on the right can always be decomposed.
      intro h6
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h9 =>
        -- One of the premise coincides with the conclusion.
        exact h8
      case inr h10 =>
        -- One of the premise coincides with the conclusion.
        exact h8
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h11 := h4 h5
    -- One of the premise coincides with the conclusion.
    exact h11
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h12 := h2 h3
  -- One of the premise coincides with the conclusion.
  exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52038949244839910994388198305 : (((p5 ∨ (False ∧ (((p4 → (p1 ∧ (((p4 ∧ p3) → p4) ∧ p2))) ∨ p4) ∧ p5))) ∨ ((p4 ∨ ((p5 ∨ False) ∧ p5)) ∨ (True ∨ p2))) ∨ False) := by
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
theorem thm_5_vars_164738078689637106221733370905 : ((((((p3 ∨ p1) → (True ∧ p3)) → (((p2 → p1) → p3) → False)) ∧ (p3 ∨ p5)) ∨ False) ∨ ((True ∨ ((p2 → p1) → p4)) ∧ (p5 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166492996529986089316479322533 : ((p3 ∨ ((True ∨ p1) → (p3 ∨ ((p5 → p4) ∧ (((p5 ∨ (False → p5)) → p4) ∨ p2))))) ∨ ((True ∨ p3) ∨ (p1 ∧ (True ∨ (p2 ∨ False))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48230568422584352556737487796 : (((True ∧ (True ∨ ((p3 ∧ (p4 ∨ p4)) ∨ ((p2 → p4) → ((p3 ∧ ((p1 → p5) → True)) → (p4 → (p1 ∨ p4))))))) → (False ∨ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156808026144287443746044021672 : (((False ∨ (((p5 ∨ p4) ∧ (p3 → (p5 ∧ p1))) ∨ (((p2 ∨ (p2 ∧ p3)) ∧ p4) ∧ p2))) ∧ p2) ∨ (p5 → (((p2 ∧ False) ∨ p5) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_746290373327084999151109904358 : ((((p1 ∨ p5) → (p1 → (p2 ∨ (p3 → (((p1 ∨ False) ∧ ((p5 ∧ p3) ∧ (p1 → (p5 ∧ p5)))) ∨ (((p3 → False) ∨ p5) → p5)))))) ∨ False) ∧ True) := by
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
    -- Implications on the right can always be decomposed.
    intro h4
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h7 : p3 := by
        -- One of the premise coincides with the conclusion.
        exact h4
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h8 := h6 h7
      -- False on the left can always be used.
      apply False.elim h8
    case inr h9 =>
      -- One of the premise coincides with the conclusion.
      exact h9
  case inr h10 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h11
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
      exact h14
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135579289196820721385674148594 : ((((p2 ∨ (True ∧ ((p3 → (((p1 → p1) ∧ (False ∧ p4)) ∨ p2)) → p1))) ∨ p2) ∨ ((p3 ∧ p5) → (False → p4))) ∨ ((p4 → p2) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40791163556326927994896760268 : ((((p4 ∧ (((((((p4 → False) ∧ (p1 ∨ p3)) ∨ True) → True) → p4) ∧ p3) ∨ ((p5 → (p4 ∧ False)) ∧ (False → p3)))) → p5) ∨ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63983507960805439185313967651 : ((False ∨ (((p5 ∨ (p2 ∨ p1)) ∧ (((p2 ∨ p3) ∨ (((p4 ∨ p4) ∨ (p2 ∧ (p1 ∧ ((p2 ∧ p5) ∨ False)))) ∧ p1)) → p2)) → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_807094311364766051854643290686 : (((p4 → (((p4 ∨ ((((p2 → p2) ∧ p1) ∧ (False ∧ (True ∧ p5))) ∨ (p3 ∨ p5))) → (p1 ∧ p3)) ∨ (((False → True) ∧ p1) → p1))) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  exact h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300061040421950077240633695731 : (False ∨ (((((True → ((p4 → p3) ∨ True)) → (((p4 ∨ (p2 ∧ (p4 ∧ (p4 ∨ (p4 ∨ p5))))) ∧ True) ∨ False)) ∧ p1) ∨ True) ∨ (p3 ∧ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_35387757632864168485096291204 : ((p2 → (((p4 ∧ ((((p3 ∧ (p1 ∨ ((p2 ∧ p3) ∧ p3))) ∨ p4) ∨ p3) ∧ (((p3 ∨ (p5 ∧ p3)) ∨ p2) → p1))) ∧ p5) ∨ True)) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199038067267899013376365138775 : (((((p2 ∨ (p2 ∨ p5)) ∨ p2) ∨ False) ∧ p2) → ((((p4 ∨ ((p3 → True) ∧ True)) → ((p5 → (p1 ∨ p5)) ∨ p4)) ∧ False) ∨ (p5 ∨ p2))) := by
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
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h3
      case inr h7 =>
        -- Disjunctions on the left can always be decomposed.
        cases h7
        case inl h8 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h3
        case inr h9 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h9
    case inr h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
  case inr h11 =>
    -- False on the left can always be used.
    apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_325812095651695174153881873806 : (p5 ∨ (p3 ∨ ((((((True ∨ ((p4 ∧ (p2 ∧ (p5 ∨ False))) ∧ p4)) ∨ p1) → p5) ∨ p3) ∨ (False → False)) ∨ (False → (p2 → (p1 → True)))))) := by
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
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_175062188180874221538480530025 : ((p2 ∧ (p2 ∨ (((p3 ∧ (p3 ∨ p4)) ∧ ((p4 ∧ p5) ∨ p1)) ∧ (p5 ∧ True)))) → ((p4 → ((((p4 → False) → False) ∧ False) ∨ p3)) ∨ True)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h8 := h6.left
    let h9 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h8.left
    let h11 := h8.right
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h13 =>
        -- Conjunctions on the left can always be decomposed.
        let h14 := h13.left
        let h15 := h13.right
        -- Conjunctions on the left can always be decomposed.
        let h16 := h7.left
        let h17 := h7.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h18 =>
        -- Conjunctions on the left can always be decomposed.
        let h19 := h7.left
        let h20 := h7.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h21 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h22 =>
        -- Conjunctions on the left can always be decomposed.
        let h23 := h22.left
        let h24 := h22.right
        -- Conjunctions on the left can always be decomposed.
        let h25 := h7.left
        let h26 := h7.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h27 =>
        -- Conjunctions on the left can always be decomposed.
        let h28 := h7.left
        let h29 := h7.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185219449079870827496820802857 : ((False ∧ ((((((p4 ∨ p5) ∧ p1) → p3) ∧ p2) → False) ∨ True)) ∨ ((((p4 ∧ False) ∨ p1) ∧ ((p1 ∨ p3) ∧ (p5 ∧ p2))) ∨ (p3 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_266164619257303562199040479497 : (True ∧ (p3 → (p2 ∨ (((p2 ∧ p5) ∨ ((False ∨ ((((p3 ∧ p5) ∧ (((p2 → False) → False) → p2)) ∧ p2) → True)) ∨ p3)) ∧ (p1 ∨ p3))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232994318608309998210508518422 : ((p3 ∧ (p4 → p5)) → ((((False ∨ (p2 ∧ ((p2 ∧ ((p3 → p1) ∨ (p2 → p3))) ∨ True))) ∨ p3) ∧ ((True ∧ p1) ∨ p2)) → (p4 ∨ p3))) := by
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
    cases h5
    case inl h6 =>
      -- False on the left can always be used.
      apply False.elim h6
    case inr h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Conjunctions on the left can always be decomposed.
        let h11 := h10.left
        let h12 := h10.right
        -- Disjunctions on the left can always be decomposed.
        cases h12
        case inl h13 =>
          -- Disjunctions on the left can always be decomposed.
          cases h4
          case inl h14 =>
            -- Conjunctions on the left can always be decomposed.
            let h15 := h14.left
            let h16 := h14.right
            -- Conjunctions on the left can always be decomposed.
            let h17 := h1.left
            let h18 := h1.right
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h17
          case inr h19 =>
            -- Conjunctions on the left can always be decomposed.
            let h20 := h1.left
            let h21 := h1.right
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h20
        case inr h22 =>
          -- Disjunctions on the left can always be decomposed.
          cases h4
          case inl h23 =>
            -- Conjunctions on the left can always be decomposed.
            let h24 := h23.left
            let h25 := h23.right
            -- Conjunctions on the left can always be decomposed.
            let h26 := h1.left
            let h27 := h1.right
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h26
          case inr h28 =>
            -- Conjunctions on the left can always be decomposed.
            let h29 := h1.left
            let h30 := h1.right
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h29
      case inr h31 =>
        -- Disjunctions on the left can always be decomposed.
        cases h4
        case inl h32 =>
          -- Conjunctions on the left can always be decomposed.
          let h33 := h32.left
          let h34 := h32.right
          -- Conjunctions on the left can always be decomposed.
          let h35 := h1.left
          let h36 := h1.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h35
        case inr h37 =>
          -- Conjunctions on the left can always be decomposed.
          let h38 := h1.left
          let h39 := h1.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h38
  case inr h40 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h41 =>
      -- Conjunctions on the left can always be decomposed.
      let h42 := h41.left
      let h43 := h41.right
      -- Conjunctions on the left can always be decomposed.
      let h44 := h1.left
      let h45 := h1.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h44
    case inr h46 =>
      -- Conjunctions on the left can always be decomposed.
      let h47 := h1.left
      let h48 := h1.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h47



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_81167320178181315808360185855 : (((p2 ∧ (((p1 → False) → (p5 → ((((p2 ∧ (p5 ∨ (p3 ∧ True))) ∧ p3) ∧ p5) → True))) → (p4 ∧ False))) ∧ ((p2 → p5) → p2)) → p5) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h6 : ((p1 → False) → (p5 → ((((p2 ∧ (p5 ∨ (p3 ∧ True))) ∧ p3) ∧ p5) → True))) := by
    -- Implications on the right can always be decomposed.
    intro h7
    -- Implications on the right can always be decomposed.
    intro h8
    -- Implications on the right can always be decomposed.
    intro h9
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h10 := h5 h6
  -- We need to get the right conjuct of h10 based on <expert-advice>.
  let h11 := h10.right
  -- False on the left can always be used.
  apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_69309169801125791005093095457 : ((p5 → (p2 ∧ ((((p1 ∨ p3) ∨ True) ∧ (p2 ∨ p1)) → (((p2 ∧ True) → (((p3 ∧ (False → (p1 ∧ p4))) ∨ p2) → p5)) → p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172415087339542655874524622266 : (((((True ∨ p5) ∧ p3) → p3) ∧ ((True → (p2 ∨ ((p3 ∧ True) ∨ p3))) ∧ p1)) ∨ (True ∧ ((p2 ∨ (p1 ∨ p2)) → (True → (p2 ∨ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
    exact h3
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h6 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148658919839566019918835142370 : (((p2 ∧ ((p3 → ((p4 ∧ p3) → False)) → p4)) ∧ ((p4 ∧ (p5 ∧ p3)) ∨ ((True ∧ p2) ∧ (p3 ∧ p4)))) ∨ (p4 ∨ ((True ∧ p3) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62568544055449856925482950745 : ((p3 ∧ (True → (((p3 → p5) → (((p2 ∧ (p1 ∧ p2)) → (False ∨ (False ∧ p3))) ∨ (False ∧ p3))) ∨ ((p1 ∨ True) → (p3 → p3))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184374190374530456607413434668 : (((p5 ∨ ((p3 ∧ (p1 → p1)) → ((False ∨ True) → False))) → p5) ∨ (p1 ∨ (p3 → ((p5 ∧ p5) → ((((p2 → p1) ∧ p2) ∧ p5) ∨ p3))))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



