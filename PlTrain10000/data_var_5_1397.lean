variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_85412903339736206806172953466 : ((((p3 ∨ p4) ∨ ((((p3 ∧ p3) → False) ∨ p4) → (p3 → True))) ∧ ((p5 ∨ ((((p1 ∧ p3) ∧ True) → p3) ∨ True)) → (p3 ∧ False))) → p1) := by
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
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h6 : (p5 ∨ ((((p1 ∧ p3) ∧ True) → p3) ∨ True)) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h7 := h3 h6
      -- We need to get the right conjuct of h7 based on <expert-advice>.
      let h8 := h7.right
      -- False on the left can always be used.
      apply False.elim h8
    case inr h9 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h10 : (p5 ∨ ((((p1 ∧ p3) ∧ True) → p3) ∨ True)) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h11 := h3 h10
      -- We need to get the right conjuct of h11 based on <expert-advice>.
      let h12 := h11.right
      -- False on the left can always be used.
      apply False.elim h12
  case inr h13 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h14 : (p5 ∨ ((((p1 ∧ p3) ∧ True) → p3) ∨ True)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h15 := h3 h14
    -- We need to get the right conjuct of h15 based on <expert-advice>.
    let h16 := h15.right
    -- False on the left can always be used.
    apply False.elim h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49048404283662849614954233115 : (((((((((False ∨ p4) ∨ (p1 ∨ (p3 ∨ p4))) ∧ p5) → p3) → ((p4 ∨ True) → p5)) ∨ p5) ∧ (False ∧ p4)) ∨ (p1 ∨ (True ∧ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_720531463542393656084251793326 : (((((p1 → (True ∨ p2)) ∨ p2) → (True ∧ ((p1 ∧ p4) ∧ (((True ∨ (False → p1)) ∨ p2) → ((((p5 ∧ p4) → p3) ∧ p2) → p5))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350261544411736368562537275762 : (p4 → ((p2 ∧ (((p2 ∨ (p5 ∨ (p1 ∧ p2))) ∧ p4) ∧ ((p4 ∧ p5) ∨ (p4 ∨ ((((False ∨ True) ∨ p3) ∧ p1) ∨ (p1 ∨ p5)))))) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341763277643725932718390079833 : (p2 → ((p5 ∨ ((p2 ∨ (True → p3)) ∧ ((p1 ∧ ((p4 ∧ (p5 ∨ True)) ∨ (p2 → ((False ∨ False) → p4)))) ∨ (p3 ∧ p2)))) ∨ (p1 ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47314421218671893337766135475 : ((((p4 ∨ (False ∧ p3)) ∨ (p4 → ((True → p1) ∨ (((p2 ∨ False) → p5) ∨ (((p1 → (p1 ∨ p5)) → p3) ∨ p1))))) ∨ (False ∨ True)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_737014741881813334130454341645 : ((((p3 → p1) ∧ (((((p4 → p3) ∨ False) ∨ p4) ∧ ((p4 → ((p3 → (p2 → (True ∨ p3))) ∨ p4)) → (False ∨ p2))) ∧ (p2 ∨ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165243813773671054855500809431 : (((False ∨ ((p1 ∧ (True ∧ (p2 ∨ (p3 ∧ (p5 → False))))) → (p5 ∨ p5))) ∨ (p2 ∨ True)) ∨ (((p4 ∨ p5) ∨ p4) → ((p1 ∨ p1) ∨ p3))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217189748123435127737302116639 : ((((p1 ∨ True) → False) ∨ p4) → (p5 → (((p2 → False) ∨ p4) ∧ (((p5 → (p2 ∨ (p5 ∧ False))) ∨ (p4 → (True ∨ p2))) ∨ (p3 → p1))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h4 : (p1 ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h5 := h3 h4
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h6
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h7 =>
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h8 : (p1 ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h9 := h7 h8
    -- False on the left can always be used.
    apply False.elim h9
  case inr h10 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h11
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116606035109272776157589346024 : (((True → False) ∧ (p1 ∧ (p2 ∨ ((p4 ∧ p2) ∧ ((((True ∧ p5) → ((((p3 ∧ p1) ∨ p1) ∧ p1) → False)) ∨ True) ∧ p2))))) ∨ (False → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347019705533821786308996321847 : (p3 → (((p2 ∨ False) ∧ ((p5 → ((p2 → p2) ∨ (p4 ∧ True))) → ((p4 ∨ p5) ∧ p1))) ∨ (((True ∧ (False → (p2 ∨ False))) ∧ False) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_627013288119503420669566859078 : (((((((p2 ∨ ((False ∨ (((p1 ∨ (p4 → False)) → ((p4 ∧ p2) → True)) ∨ p2)) ∨ p4)) ∧ (p1 → (p1 ∧ p2))) ∧ p5) ∧ p5) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_476505962579093011409689192026 : (((((True ∨ p3) ∧ ((p1 → (p3 ∨ False)) ∧ (False ∨ p5))) ∨ ((((False → p4) ∨ (p3 → (True ∧ p3))) → False) ∨ ((p4 ∧ False) → p4))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  apply False.elim h3
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225068423838029366480911676757 : (((p1 ∧ p2) ∧ p1) ∨ ((p2 ∨ p5) → (((False → (((((True → (p1 → p1)) ∧ p3) → False) → p2) → p3)) → p3) ∨ ((p5 ∨ True) ∨ False)))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_504384464301955651959309251438 : ((((True ∨ (True ∨ p5)) → ((((((p5 → (p1 ∨ True)) ∧ True) → False) → ((p3 → (p4 → (True ∨ True))) → False)) → False) ∨ (True ∨ p5))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_196816732236727717890791127186 : (((True ∧ (p3 ∨ ((p3 → p2) ∧ p3))) ∧ p1) ∨ (False ∨ (((((p4 ∧ (False → (p4 ∨ p1))) → (p2 ∧ p4)) → (True ∨ p4)) → False) → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p4 ∧ (False → (p4 ∨ p1))) → (p2 ∧ p4)) → (True ∨ p4)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_656350974463541686355255800186 : (((((((p4 ∨ (((p1 ∧ p2) ∧ (p3 ∨ p4)) → p4)) ∨ True) → p1) → (p1 → (p2 → (p4 ∧ (p5 ∨ (p2 ∧ p1)))))) ∨ (p3 → p3)) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_146523985314255736945101943781 : ((p4 ∨ (p1 → (((((p5 → (((p4 ∧ p4) ∨ (False ∧ p1)) ∨ True)) ∧ p4) → (p3 ∧ p5)) ∨ p1) ∨ p5))) ∧ (p5 → ((p4 → True) ∧ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149133011299118057832119115253 : (((p3 ∧ p5) ∧ ((p4 ∨ (((p5 ∨ (p2 → p4)) ∧ True) → (p2 → p4))) ∨ (((False ∨ p3) ∧ False) → p4))) ∨ (p4 ∨ ((True ∧ p2) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56209393866481606842940819726 : (((False ∨ (p3 → (p3 → p1))) ∨ ((((True ∨ p1) ∨ False) ∧ (p2 ∨ p4)) → ((p1 → ((p4 ∧ (p2 ∧ (True → p2))) ∨ p2)) ∨ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190906533254805763591678173985 : (((True → (p3 ∨ ((True → p3) → p4))) → (p4 → False)) ∨ ((p3 ∨ ((p4 → p4) ∨ (True → (False ∧ ((p4 ∨ True) ∧ True))))) ∨ (p2 ∧ p5))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257183311914174833598683460816 : ((p2 ∨ p2) → (((((((p3 ∧ (p4 ∧ p3)) ∧ p2) ∨ (((True → p1) ∧ p5) → (p2 ∨ ((True ∨ p2) ∧ p4)))) ∨ p4) ∨ p3) ∧ True) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h6
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115271947963070080274965419659 : (((p5 ∧ (p1 ∨ (((p3 ∨ (p5 → False)) → p5) ∧ p1))) ∨ (False ∨ ((False ∨ True) ∧ (((p1 ∧ p3) ∧ True) ∧ (p1 ∧ p5))))) ∨ (p1 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_261502699567174899537596999047 : ((p5 → p3) → (((p3 → (((p3 ∧ (((p2 ∨ (True → p1)) ∧ False) ∧ p4)) ∨ ((p4 → (False → p3)) ∧ p3)) ∨ p4)) → (p5 ∨ p3)) → p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (p3 → (((p3 ∧ (((p2 ∨ (True → p1)) ∧ False) ∧ p4)) ∨ ((p4 → (False → p3)) ∧ p3)) ∨ p4)) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h5
    -- Implications on the right can always be decomposed.
    intro h6
    -- False on the left can always be used.
    apply False.elim h6
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h7 := h2 h3
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h9 : p5 := by
      -- One of the premise coincides with the conclusion.
      exact h8
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h10 := h1 h9
    -- One of the premise coincides with the conclusion.
    exact h10
  case inr h11 =>
    -- One of the premise coincides with the conclusion.
    exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_713977110015381832887081167528 : (((((p5 → ((p2 → p1) ∧ p5)) ∨ p1) → ((p3 ∧ p1) ∨ ((p4 ∨ False) ∧ (((False ∨ p2) ∨ True) → (p1 ∨ ((True ∨ True) ∨ p2)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321771131079036727314527182646 : (p4 ∨ (p5 → (p5 → (p2 ∨ (((p1 ∨ (p4 ∨ p4)) ∧ p5) ∨ (((False ∧ True) ∨ (((p3 → p1) → True) ∨ (True ∨ p1))) ∨ (p1 ∧ p1))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_124237821051632442271365606083 : ((((((True → (True ∧ p3)) ∧ p2) → True) → (p1 → True)) → ((((p5 ∧ p4) ∧ p4) ∨ (((p4 ∨ p1) → p4) → p5)) ∧ False)) → (False ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((((True → (True ∧ p3)) ∧ p2) → True) → (p1 → True)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h2
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156674382132710514870600401639 : ((((p3 → ((p4 ∨ p5) ∨ ((((True ∨ True) ∨ p3) ∧ (False → p1)) ∧ p5))) ∧ (False → p3)) ∧ p2) ∨ ((p3 ∨ ((p2 ∨ False) → p2)) ∨ p4)) := by
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
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- False on the left can always be used.
    apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160477818096336048005590547394 : (((p2 ∨ ((p1 → True) ∧ ((p2 ∧ p5) ∨ (((False ∧ p3) ∧ p5) → True)))) → ((True ∧ p3) ∧ p5)) → (p5 ∧ (((p2 ∨ p3) ∨ False) ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p2 ∨ ((p1 → True) ∧ ((p2 ∧ p5) ∨ (((False ∧ p3) ∧ p5) → True)))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h2
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- One of the premise coincides with the conclusion.
  exact h6
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h7 : (p2 ∨ ((p1 → True) ∧ ((p2 ∧ p5) ∨ (((False ∧ p3) ∧ p5) → True)))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h8
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h10 := h1 h7
  -- We need to get the left conjuct of h10 based on <expert-advice>.
  let h11 := h10.left
  -- We need to get the right conjuct of h11 based on <expert-advice>.
  let h12 := h11.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184045400689860592212719357414 : (((((p1 ∨ ((p4 ∧ p3) ∧ p3)) ∧ p1) ∧ (p4 ∨ p1)) ∨ True) ∨ ((p1 → ((p4 ∨ False) ∧ ((p1 → True) ∧ (p5 ∧ p1)))) ∨ (p5 → p4))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171627434382693316946685723426 : (((((True ∨ True) → p2) → ((p4 → (((p5 ∨ True) → True) → p3)) ∨ p5)) ∨ True) ∨ ((p4 ∨ False) ∨ (p2 ∧ (((False → False) ∨ p5) ∧ False)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_668626339432482541587337782397 : (((((False ∨ (((p4 ∧ (((p4 ∧ p4) ∨ (False → (p4 → ((p4 ∧ p2) → p4)))) ∨ True)) ∨ p5) ∨ p4)) ∧ p1) ∨ (p2 ∨ (p3 ∧ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259374812757553927760856388124 : ((False → p3) → ((p1 → ((False ∧ ((p3 ∨ True) ∧ (p1 → p1))) ∨ (True ∧ ((p4 ∨ (p5 → (p1 → (p3 ∧ False)))) ∨ (p3 ∧ True))))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_175449322723392121567232319603 : ((p1 → (p2 ∧ ((p2 ∧ (True → (p3 → p5))) → (((p5 → p2) → True) ∧ p3)))) → ((((True ∨ True) → p2) ∧ (True ∨ p3)) → (p5 → p2))) := by
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
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h7 : (True ∨ True) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h8 := h4 h7
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h10 : (True ∨ True) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h11 := h4 h10
    -- One of the premise coincides with the conclusion.
    exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_251680195554304373839647033007 : ((p3 → p2) ∨ ((p2 ∧ (((p3 ∨ False) → (p2 ∨ (True → False))) ∧ ((True ∧ p3) ∨ p1))) → (((((p4 → p2) → p1) ∨ p1) ∨ p1) → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
      -- Conjunctions on the left can always be decomposed.
      let h5 := h1.left
      let h6 := h1.right
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Conjunctions on the left can always be decomposed.
        let h10 := h9.left
        let h11 := h9.right
        -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
        have h12 : (p4 → p2) := by
          -- Implications on the right can always be decomposed.
          intro h13
          -- One of the premise coincides with the conclusion.
          exact h5
        -- We have shown the premise of h4, we can now drive its conclusion.
        let h14 := h4 h12
        -- One of the premise coincides with the conclusion.
        exact h14
      case inr h15 =>
        -- One of the premise coincides with the conclusion.
        exact h15
    case inr h16 =>
      -- Conjunctions on the left can always be decomposed.
      let h17 := h1.left
      let h18 := h1.right
      -- Conjunctions on the left can always be decomposed.
      let h19 := h18.left
      let h20 := h18.right
      -- Disjunctions on the left can always be decomposed.
      cases h20
      case inl h21 =>
        -- Conjunctions on the left can always be decomposed.
        let h22 := h21.left
        let h23 := h21.right
        -- One of the premise coincides with the conclusion.
        exact h16
      case inr h24 =>
        -- One of the premise coincides with the conclusion.
        exact h24
  case inr h25 =>
    -- Conjunctions on the left can always be decomposed.
    let h26 := h1.left
    let h27 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h28 := h27.left
    let h29 := h27.right
    -- Disjunctions on the left can always be decomposed.
    cases h29
    case inl h30 =>
      -- Conjunctions on the left can always be decomposed.
      let h31 := h30.left
      let h32 := h30.right
      -- One of the premise coincides with the conclusion.
      exact h25
    case inr h33 =>
      -- One of the premise coincides with the conclusion.
      exact h33



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_588683127923503743555531894942 : (((((p2 ∧ ((((((p1 → p2) ∨ False) ∧ (False → True)) → p2) ∨ (p5 ∧ ((p5 → p1) → ((p4 → p1) ∧ p5)))) ∨ True)) ∨ p4) ∧ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_723153044671307552264027352273 : (((((True → p1) ∨ p2) ∧ ((((((((False ∧ (False ∨ p5)) → True) → p4) → ((p5 ∧ False) ∧ True)) → (p1 ∨ False)) → p3) → p5) ∧ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_621158741212021294687452224450 : (((((p5 → p5) → (p1 ∨ ((p3 ∨ (p2 ∧ (p3 ∧ (False ∧ (False ∨ p2))))) ∨ (((False ∧ (p2 ∧ (False ∧ False))) → True) ∧ True)))) ∨ p5) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66201135237769213223540800753 : ((p5 ∨ ((((((p2 ∧ False) ∧ True) ∧ (p2 → (p4 → p1))) ∧ (True → p3)) → p4) ∧ (False ∧ ((p1 ∨ p1) → (p4 ∧ (True ∨ p1)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234080088640572219883869242260 : ((True → (p1 ∧ p5)) → (p4 → (((((p1 ∧ (p5 ∨ (p4 → (False ∨ p2)))) → p3) → (p3 ∨ ((p2 ∧ p2) ∧ False))) → (p3 → p5)) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41932702890593154423038787711 : ((((True → (p3 ∨ p4)) → (p1 → ((False ∨ (p5 → True)) ∧ ((((p4 → (p4 ∨ p2)) → p5) ∨ p4) ∨ ((p5 → p1) ∨ p2))))) ∨ p5) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h4
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_683352153965357876951663501405 : ((((p4 ∨ (p4 → (p3 ∧ (((((True ∨ False) ∨ (True → p5)) ∧ p4) → (p2 → p4)) → p2)))) ∧ ((False ∧ p1) ∧ (p3 ∧ (True ∨ True)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_692648043869601753220303869524 : (((((p4 ∨ ((True ∧ (p2 → (True ∧ True))) → p4)) → (False → (p1 ∨ p5))) ∧ (p5 ∧ (((p1 ∨ ((p1 ∧ p4) ∧ p3)) ∧ p1) ∧ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135365959379112169862276076363 : (((((((((False ∧ False) ∨ (p1 → True)) ∨ True) ∨ ((p2 → p3) ∧ True)) ∨ True) ∧ False) ∧ p5) ∨ (True ∧ (p4 ∧ p5))) ∨ (True ∨ (True → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187500714687017666917542229096 : ((False ∨ (False → (((p3 ∧ ((p4 ∧ p2) ∨ p3)) ∧ False) → p2))) → ((p4 ∨ p5) ∨ (((True → (p3 ∨ p1)) ∧ p5) ∨ (p1 ∨ (p1 ∨ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- False on the left can always be used.
    apply False.elim h2
  case inr h3 =>
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
theorem thm_5_vars_239599028845971688479308364602 : ((p3 ∨ True) ∧ ((p4 → (p3 ∧ (p3 ∧ (False ∨ (False ∧ False))))) → ((p4 ∨ False) ∨ (p2 → (p2 ∧ ((p4 → False) ∨ ((True → p5) ∧ p1))))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h4 : p4 := by
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h4
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- False on the left can always be used.
    apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171841537279548025309228249807 : ((((p4 ∧ True) ∧ ((p3 → p3) ∧ (((p3 ∧ (p1 ∧ p2)) → True) → p2))) → False) ∨ (((p5 ∨ (p3 ∨ True)) ∧ p5) ∨ (p1 ∨ (True ∨ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356170926432359995444151426895 : (p5 → ((p4 ∨ (((p1 → ((p5 ∧ (p1 → p2)) ∧ ((False ∨ p1) ∨ (p3 → True)))) ∨ p5) → False)) ∨ ((p2 → ((p4 → p3) → p2)) ∧ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_302588824680035150374040517237 : (False ∨ (p1 ∨ (((p3 → p3) ∨ p2) → (p4 ∨ (((((p5 ∧ ((p1 ∧ p3) ∨ (p1 → p1))) → ((p2 ∨ True) ∨ p2)) ∨ False) ∧ p5) ∨ True))))) := by
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
theorem thm_5_vars_320022716033813909576721918398 : (p4 ∨ (((p3 ∧ p1) ∨ p2) ∨ ((p2 ∧ (p5 → (p3 → p1))) ∨ (((p5 → (((True ∨ False) ∧ p5) ∧ (p2 → p3))) → (p3 ∧ True)) ∨ True)))) := by
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
theorem thm_5_vars_608306088844122557965395629037 : ((((((((((False ∨ (p2 ∧ (p1 ∧ True))) → (p1 → p2)) ∨ True) → p2) ∨ (p4 ∨ (((True → p5) → True) → True))) ∨ p1) ∨ True) ∨ p1) ∨ p1) ∧ True) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159507306705426516776325892677 : ((((True → False) ∧ ((p2 ∧ (p3 → p5)) → ((p5 ∧ (((p1 ∨ False) ∨ p5) ∧ p5)) ∧ p5))) ∧ p5) → (((p4 → p1) → p5) ∧ (False ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- One of the premise coincides with the conclusion.
  exact h4
  -- Conjunctions on the left can always be decomposed.
  let h7 := h1.left
  let h8 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h9 := h7.left
  let h10 := h7.right
  -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
  have h11 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h9, we can now drive its conclusion.
  let h12 := h9 h11
  -- False on the left can always be used.
  apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_801488250208407877759587108095 : (((p2 → ((((p3 ∧ p4) ∨ (p5 ∨ (p4 ∨ p3))) ∨ p2) ∨ (p4 ∧ (False → ((p1 → (False → ((p4 → p5) ∧ (p5 ∧ p3)))) → False))))) ∨ p4) ∧ True) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148718509926485703723045392124 : ((((p5 ∨ False) → (((p1 → p3) ∨ p2) → True)) → ((p4 ∧ True) ∧ (p4 ∨ (p5 ∧ ((False → p2) ∧ p5))))) ∨ ((p2 ∧ (p5 ∧ p1)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218783519660071704201544677276 : ((p1 ∧ ((p5 ∨ True) → False)) → (p2 ∧ ((p3 ∧ (p5 ∧ (False ∧ p4))) ∨ ((((p4 → ((p5 ∨ p3) → False)) → p1) → (p4 ∨ p4)) ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : (p5 ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- False on the left can always be used.
  apply False.elim h5
  -- Conjunctions on the left can always be decomposed.
  let h6 := h1.left
  let h7 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198357891600632786950354808701 : ((p2 ∧ (p3 ∨ (((True ∧ p3) ∧ p1) ∧ p3))) ∨ (((False → (((p5 ∨ False) ∧ False) ∧ p3)) → ((True ∧ ((False → p5) ∨ False)) ∨ p5)) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_444815310308493264844435246088 : ((((True → (p5 ∧ ((((p5 ∨ p5) ∧ p5) → (p4 ∧ (p3 → False))) ∧ ((True ∨ False) ∧ (True ∨ (p5 → p3)))))) ∨ (True ∨ (p4 ∧ p1))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191424107348266164966615326447 : (((p1 ∨ p1) → ((((True → False) ∧ p3) ∧ p5) ∨ p1)) ∨ ((p5 → True) ∨ ((((((p1 → (True ∨ p3)) ∧ True) ∧ p1) ∧ p4) → p1) ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134088734830928058004311394837 : (((((p4 → p3) ∧ ((((((p1 ∧ p1) ∨ (((p1 ∨ False) ∧ p1) → p4)) ∨ p2) ∧ p3) ∧ p1) → p1)) → p1) ∨ p1) ∨ ((p2 ∧ p5) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351405609849825527029882542033 : (p4 → (((((p1 ∧ (p5 ∨ False)) ∧ False) ∧ (p4 ∨ (False ∧ p5))) ∧ ((p5 → p1) ∧ ((p2 ∧ True) → p4))) ∨ ((False ∧ (p3 ∧ p5)) → p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_792987769536189939918933272 : (((p4 → p3) → (p1 ∨ (True ∧ ((((True ∧ p2) ∧ (((True ∧ True) ∨ p2) ∨ (p2 → p2))) ∨ (True ∧ (p2 ∧ p2))) ∧ p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219078949743928214739171555755 : ((p5 ∧ (p1 → (p5 → p3))) → ((((p5 → (p1 ∨ ((p2 ∧ (p2 ∧ True)) → p5))) ∧ p5) ∧ p5) → ((p3 ∧ (True ∨ (p1 → p2))) ∨ p5))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h7 := h1.left
  let h8 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_774404106894892746307132496021 : (((False ∨ ((p2 ∧ (((p5 → ((p4 ∧ (p4 → (False ∧ p4))) ∨ (p5 → (False → False)))) ∧ p1) → p4)) → ((True → False) ∨ (p5 → p2)))) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45932583192953021421703971845 : (((p4 → (p3 → ((p5 → (p5 → False)) → (((((p3 ∧ (p4 → p4)) ∨ p5) ∧ (True → (p1 ∨ (True ∨ p4)))) → p4) ∨ p3)))) → p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63164381372598902033900259949 : ((p5 ∧ (((p2 → (((p5 ∨ p3) ∧ ((False ∧ (p5 → (True → p3))) → p5)) ∧ p1)) ∧ ((p5 → p2) ∨ (p2 ∧ False))) ∨ (p3 → True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_353432586965687718428813586194 : (p4 → (p1 ∨ ((((p2 → p2) ∨ (((p5 ∨ p1) ∧ p2) ∧ (False ∨ p2))) ∧ (p2 ∨ p1)) → (((True → p3) → p1) ∨ ((p5 ∨ p2) ∨ p5))))) := by
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
    cases h4
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h7 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h8
      -- One of the premise coincides with the conclusion.
      exact h7
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Conjunctions on the left can always be decomposed.
    let h12 := h10.left
    let h13 := h10.right
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h14 =>
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h15 =>
        -- False on the left can always be used.
        apply False.elim h15
      case inr h16 =>
        -- Disjunctions on the left can always be decomposed.
        cases h4
        case inl h17 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h14
        case inr h18 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h14
    case inr h19 =>
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h20 =>
        -- False on the left can always be used.
        apply False.elim h20
      case inr h21 =>
        -- Disjunctions on the left can always be decomposed.
        cases h4
        case inl h22 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h22
        case inr h23 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h21



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173212979790030016263827341598 : ((p5 ∨ ((p3 ∧ p5) ∧ (p3 ∨ ((((p1 ∨ p2) ∧ (p4 ∧ p4)) → p4) → p2)))) ∨ ((False ∧ (p1 ∨ ((True ∧ p2) ∨ (p5 ∨ p2)))) → p5)) := by
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
theorem thm_5_vars_659257804725194424213249386503 : ((((p4 → (False ∨ ((p2 → ((p5 → ((p2 ∨ (p2 → p3)) ∧ ((p1 → p1) ∨ (False ∧ (False ∨ p3))))) ∨ p1)) → p5))) ∨ (p3 → p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307352766662775435932477889318 : (p1 ∨ (p3 ∨ (p2 → ((((p4 ∨ (p5 ∧ p4)) ∧ p1) ∨ p2) → (((p3 ∧ (p4 → (True → True))) → (False ∨ p4)) → (p4 → (False ∨ p2))))))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1
  case inr h12 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61513427630316604146993554164 : ((p1 ∧ (((((((p1 ∨ p3) → ((p1 ∨ p5) → p3)) ∨ (True → False)) ∧ p1) ∨ p3) ∧ p2) ∧ (p4 ∧ ((p4 ∨ (p3 ∨ p2)) ∧ p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_715740786838526240532915413624 : ((((((p2 ∧ p2) ∨ p4) ∨ p3) ∧ (p4 ∨ ((p5 ∧ ((p4 ∧ (p2 ∧ p1)) ∧ p3)) ∨ (((p3 → (p2 ∨ (p1 ∧ True))) ∧ p3) ∨ False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160784799221185403618821705230 : ((((True ∨ (p2 ∧ (p5 → p5))) ∧ p2) ∨ ((p5 → p4) ∨ (((p1 → p5) ∨ (False ∧ p3)) ∨ False))) → (((True → False) ∧ (p2 → True)) → p5)) := by
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
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h9 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h10 := h3 h9
      -- False on the left can always be used.
      apply False.elim h10
    case inr h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h14 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h15 := h3 h14
      -- False on the left can always be used.
      apply False.elim h15
  case inr h16 =>
    -- Disjunctions on the left can always be decomposed.
    cases h16
    case inl h17 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h18 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h19 := h3 h18
      -- False on the left can always be used.
      apply False.elim h19
    case inr h20 =>
      -- Disjunctions on the left can always be decomposed.
      cases h20
      case inl h21 =>
        -- Disjunctions on the left can always be decomposed.
        cases h21
        case inl h22 =>
          -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
          have h23 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h3, we can now drive its conclusion.
          let h24 := h3 h23
          -- False on the left can always be used.
          apply False.elim h24
        case inr h25 =>
          -- Conjunctions on the left can always be decomposed.
          let h26 := h25.left
          let h27 := h25.right
          -- False on the left can always be used.
          apply False.elim h26
      case inr h28 =>
        -- False on the left can always be used.
        apply False.elim h28



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249021395180007848104437464633 : ((p4 ∨ False) ∨ ((p5 → p4) ∨ (((True → (p5 ∨ False)) ∨ True) ∨ ((True → p5) ∨ ((p5 ∧ False) ∨ (p1 → (True → (p4 → (True ∧ p3))))))))) := by
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
theorem thm_5_vars_327830866161484930505918540100 : (True → ((((((p2 ∧ p4) ∨ (p2 ∨ ((p3 ∧ p5) → p2))) ∧ p1) ∧ (((p1 ∨ False) → p4) ∧ False)) ∧ ((p2 → False) → False)) ∨ (p3 ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206003480148390579058395868402 : ((p1 ∧ (p1 → ((False ∧ p5) ∨ p1))) ∨ ((p2 ∨ (p1 ∨ (((True ∨ (p4 → p4)) ∨ p2) ∧ ((((True ∧ False) ∧ p5) → False) → True)))) ∨ False)) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218777348256816156597096156839 : ((p1 ∧ ((False ∧ False) → p5)) → ((p4 ∧ (p1 ∧ (p2 → False))) ∨ ((((False → p1) ∧ (True ∨ ((p2 ∧ True) ∨ p5))) ∧ (p2 ∨ p2)) → p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h10 =>
      -- One of the premise coincides with the conclusion.
      exact h10
    case inr h11 =>
      -- One of the premise coincides with the conclusion.
      exact h11
  case inr h12 =>
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h13 =>
      -- Conjunctions on the left can always be decomposed.
      let h14 := h13.left
      let h15 := h13.right
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h16 =>
        -- One of the premise coincides with the conclusion.
        exact h16
      case inr h17 =>
        -- One of the premise coincides with the conclusion.
        exact h17
    case inr h18 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h19 =>
        -- One of the premise coincides with the conclusion.
        exact h19
      case inr h20 =>
        -- One of the premise coincides with the conclusion.
        exact h20



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49173286648649050114584450818 : ((((((p3 ∧ p1) → p5) ∧ p3) ∧ (p3 ∧ (p5 ∧ ((((p3 ∨ (p3 ∨ False)) ∨ p1) ∨ False) → (False ∨ True))))) ∨ ((p4 ∨ p2) ∨ True)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149690657116508847660358921709 : ((p5 ∧ ((((p2 → ((p1 → ((True → True) ∧ True)) ∧ (True ∧ False))) ∨ p5) → False) → ((p2 ∧ p3) ∧ False))) ∨ ((p4 → (False ∧ True)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63205045422307822166938563346 : ((p5 ∧ ((((True → (p5 ∧ ((False ∨ ((True ∧ p4) ∨ (False ∨ (p4 ∧ False)))) ∨ p3))) → False) ∧ p1) ∨ (p2 ∧ ((p3 → p3) ∧ p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63121740700406665007259743942 : ((p5 ∧ ((((p4 ∨ (p1 ∧ ((((p1 ∧ (False ∨ p5)) → p3) ∧ p3) ∧ (p2 → (p2 ∧ p3))))) ∧ (p2 → False)) ∨ (p4 ∨ p4)) → p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50173191763001472599937172974 : ((((((p1 ∨ ((False ∧ p3) ∧ (p3 ∧ p1))) ∧ ((((p3 ∨ p4) ∨ p2) ∨ p4) ∨ p4)) ∨ p1) ∧ p5) ∨ ((False ∨ p1) → (p1 ∨ p1))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323895754544496287455185652677 : (p5 ∨ ((((((p5 ∧ p1) → p5) → ((True → p4) ∧ False)) ∨ (p3 ∨ False)) → (False ∨ p3)) ∨ (p5 ∧ (p1 ∨ ((True ∨ False) → (True → p5)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h3 : ((p5 ∧ p1) → p5) := by
      -- Implications on the right can always be decomposed.
      intro h4
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- One of the premise coincides with the conclusion.
      exact h5
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h7 := h2 h3
    -- We need to get the right conjuct of h7 based on <expert-advice>.
    let h8 := h7.right
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h10
    case inr h11 =>
      -- False on the left can always be used.
      apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_330368874044361413094649317582 : (True → (p2 ∨ (((p1 → True) → (((p4 ∨ (p3 → (p1 ∧ ((((p3 → p3) → p1) ∨ p3) ∨ (p5 → p2))))) ∨ False) ∨ p3)) ∨ (p2 → p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354614846800844949217474569546 : (p5 → (((((p3 → p2) → ((((p4 ∨ p3) → p4) ∨ False) ∧ (p1 → (p2 ∧ True)))) ∨ ((p3 → ((p4 ∧ True) ∧ p1)) ∧ p5)) ∨ p3) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_678688231833614317391231524964 : (((((p3 ∨ p2) ∨ (p4 → ((((((p3 ∨ False) ∧ (False ∨ p2)) → p2) ∧ p3) ∨ p1) ∧ (False ∨ p3)))) ∨ ((True → False) → (p2 → p4))) ∨ p5) ∧ True) := by
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
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- False on the left can always be used.
  apply False.elim h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42555461770658138197804756617 : (((p1 ∨ (p2 ∧ (p3 ∨ (((p5 → (p3 ∧ (p5 → p5))) → p3) ∨ (((p2 → p1) ∧ p5) ∧ ((False ∨ False) ∨ (True ∨ p1))))))) ∨ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38325578881952291431029912286 : ((((True → (False ∨ (False → (False ∨ ((p3 ∨ ((p1 → False) ∧ ((p4 → p1) ∧ False))) ∧ p4))))) → (((p4 → p2) ∨ p5) ∧ p3)) ∧ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47529536803358665334803989421 : (((p4 ∨ (((False ∧ (((p2 ∨ (False ∧ (False ∨ (p2 ∨ (p1 ∨ p3))))) ∧ (p5 ∧ p3)) ∧ (True ∨ p5))) → p5) → p5)) ∨ (False → False)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193913692993974415221516135725 : ((p1 ∨ ((p3 ∧ (p3 → (p1 ∧ p1))) ∨ (p1 ∧ True))) → (p3 ∨ (((False ∧ (p2 ∨ p5)) ∧ False) ∨ ((((p4 → p2) ∧ True) ∧ p2) → p2)))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h10
    case inr h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h12.left
      let h14 := h12.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h15
      -- Conjunctions on the left can always be decomposed.
      let h16 := h15.left
      let h17 := h15.right
      -- Conjunctions on the left can always be decomposed.
      let h18 := h16.left
      let h19 := h16.right
      -- One of the premise coincides with the conclusion.
      exact h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53168503059222661415495366471 : ((((((((p2 ∧ p3) ∧ (False → p4)) → True) ∧ p4) ∨ p2) → p1) ∨ (((p5 ∨ p5) ∧ p4) ∨ (p5 → ((p1 ∧ (p3 ∧ p2)) → p1)))) ∨ False) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_662063998991051388617875329613 : ((((((False ∧ True) → (((p5 ∧ True) ∧ (p4 ∨ p5)) ∨ (p4 → p2))) ∧ ((p1 ∨ (False → ((p2 → True) ∧ p4))) → True)) → (True → p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138181059734957839798307360364 : ((p1 → ((True ∧ p2) ∧ (((p2 ∨ p5) ∧ p5) ∧ (((True → p1) ∧ True) → ((False ∨ (p2 ∧ p3)) ∨ (p3 → p2)))))) ∨ ((False ∧ True) → False)) := by
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
theorem thm_5_vars_249670079178749255771458051321 : ((p5 ∨ p4) ∨ ((((p1 ∨ (False → p5)) → (p4 → (p3 → p5))) ∨ ((((p2 ∧ p2) ∧ p3) → True) ∨ (p3 ∧ p5))) ∨ (True ∨ (p2 → p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337374524042730211616603228199 : (p1 → ((((p4 ∨ (p1 ∧ p3)) ∨ True) → (((False ∨ (p2 ∨ ((p1 ∧ p3) ∧ p1))) ∨ (False → p3)) → (p5 ∧ p5))) ∨ ((p1 → p1) ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40076826297044199677675629166 : (((((((p4 ∨ (((p5 ∨ True) → p4) → p5)) ∨ (p2 ∧ (False → ((p2 ∨ p4) ∧ ((p5 ∨ False) ∨ False))))) ∨ True) → p4) ∧ p2) ∨ True) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191091344933844352195113035990 : ((((p4 ∨ p5) ∨ p1) ∧ ((p3 ∧ (True → p1)) ∨ p2)) ∨ (((p3 ∧ p5) ∧ (True ∧ p4)) → (p1 → (p1 ∧ (p2 ∨ (p1 ∧ (False ∨ p1))))))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h4.left
  let h8 := h4.right
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Conjunctions on the left can always be decomposed.
  let h9 := h1.left
  let h10 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h11 := h9.left
  let h12 := h9.right
  -- Conjunctions on the left can always be decomposed.
  let h13 := h10.left
  let h14 := h10.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136213643801185558575015711410 : ((((((p2 ∨ p1) ∨ p3) ∨ p1) ∧ False) ∨ (((p5 ∨ (p5 ∨ (True ∨ (p2 → p4)))) ∨ (False ∨ (True ∧ p3))) ∨ True)) ∨ ((p3 → False) ∨ p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50814093871101664577082991522 : (((p4 → (((((p1 ∨ p5) ∨ p1) ∧ (p4 → (p3 → True))) ∧ (p5 ∧ (p2 → (p1 ∨ False)))) ∧ p5)) → (((p1 → p4) → True) → p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134469077654231000716923856057 : ((((p2 ∧ ((p1 ∨ p2) ∨ ((((p5 ∨ p5) → ((p3 ∨ False) ∧ p5)) ∨ (p1 ∨ (True ∧ p3))) ∨ True))) ∧ True) → p3) ∨ ((p4 → True) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115428629346867094616267719379 : ((((False ∨ (p5 ∧ (p1 ∧ (p2 ∨ p4)))) ∨ p2) ∨ (p1 ∨ ((True → (((p3 ∨ p3) ∨ p3) ∨ ((True → p3) ∧ False))) ∨ False))) ∨ (True ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



