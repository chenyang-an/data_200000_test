variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45375989434712443320269753255 : (((p4 ∧ (False ∨ ((((((p3 ∨ (True → (True ∨ True))) → ((p1 ∧ (p3 → (False ∧ False))) ∨ p3)) → True) ∧ p4) ∨ False) ∨ p4))) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56573626098770197153970883916 : (((True → (p2 → (p4 ∨ p2))) → (((((((False → False) → p4) → p5) → p3) ∧ (p2 ∨ (p5 → (True → p2)))) → p3) → (False ∧ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_752788911561357587104012255991 : (((False ∧ ((p3 ∧ ((((((p5 → p1) → p5) ∨ (True ∨ ((p4 ∧ False) → p5))) ∧ ((p4 ∨ p5) ∨ True)) ∧ p3) ∨ (p5 ∧ p2))) ∨ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51240631023140342483837672038 : (((((p5 → p4) ∨ p3) ∨ ((p2 ∧ (((p1 ∨ p5) ∨ (p1 ∧ p5)) → p4)) → (p1 → p3))) ∨ (((p3 ∧ p2) ∧ False) ∨ (p2 ∨ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48427347654036179262080227791 : (((p3 → ((False ∨ p1) ∨ (((True ∨ ((p5 → (p1 ∨ p4)) ∧ (True ∨ ((p2 → (p1 ∧ p5)) → p2)))) ∧ p4) → p3))) → (False ∨ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215399513899577039347162938790 : ((p2 ∧ (p3 ∨ (False ∧ True))) ∨ (((p5 ∨ p4) ∧ (p2 ∧ p3)) ∨ (((((False ∨ False) ∨ False) ∧ p5) → (((p1 ∧ p4) → False) ∧ False)) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  let h5 := h1.left
  let h6 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- False on the left can always be used.
      apply False.elim h8
    case inr h9 =>
      -- False on the left can always be used.
      apply False.elim h9
  case inr h10 =>
    -- False on the left can always be used.
    apply False.elim h10
  -- Conjunctions on the left can always be decomposed.
  let h11 := h1.left
  let h12 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h11
  case inl h13 =>
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h14 =>
      -- False on the left can always be used.
      apply False.elim h14
    case inr h15 =>
      -- False on the left can always be used.
      apply False.elim h15
  case inr h16 =>
    -- False on the left can always be used.
    apply False.elim h16
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115713810288109809560999339087 : (((((p3 ∧ p2) ∨ (p3 → p2)) ∨ p4) → (((p1 → (False ∧ (False ∨ p5))) ∨ p1) → (p3 ∧ (((p1 ∨ p5) → p5) ∨ p5)))) ∨ (p3 → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_697962772912750050061503051422 : (((((p5 ∨ ((p2 ∨ ((p3 ∧ (p3 → p1)) → p5)) → p2)) ∧ p3) ∨ ((p2 → (p4 → (p3 ∧ (False ∧ (False ∧ False))))) ∨ (True → p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260482489733734663710512767461 : ((p3 → False) → ((p3 ∨ (p3 → ((p3 ∨ p2) → (((p3 → (p4 ∨ p4)) ∧ (False → p4)) ∧ (p3 ∧ p3))))) ∨ (((p3 ∨ p5) ∨ True) → p2))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h6 : p3 := by
      -- One of the premise coincides with the conclusion.
      exact h2
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h7 := h1 h6
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h9 : p3 := by
      -- One of the premise coincides with the conclusion.
      exact h2
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h10 := h1 h9
    -- False on the left can always be used.
    apply False.elim h10
  -- Implications on the right can always be decomposed.
  intro h11
  -- False on the left can always be used.
  apply False.elim h11
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h12 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h13 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h14 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h15 =>
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56848192441295066660192034789 : (((True ∧ (p1 ∨ p5)) ∧ (p1 ∨ (p1 ∨ (p5 ∧ (((True → (((p3 → p2) ∨ ((p2 ∧ p3) → (False ∨ p5))) → p4)) ∧ False) → p2))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_140138658545096271506762141167 : ((((((p3 → p1) → (True ∨ (p1 ∨ p4))) ∧ (p4 ∨ (((p3 ∧ p1) ∨ p5) ∧ (p2 ∨ p5)))) ∨ p5) → (p1 ∧ p5)) → ((True → False) → p5)) := by
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
theorem thm_5_vars_135290277525262177186136486622 : (((p5 → ((((False ∨ p4) ∧ p2) ∧ p2) ∧ (p2 ∧ (p5 ∧ (((p3 ∨ (False ∧ False)) ∧ False) ∨ False))))) → (p5 → False)) ∨ (p4 → (p1 ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305898430120344383377079952960 : (p1 ∨ ((((p2 ∧ p3) ∧ (p4 ∨ p3)) ∧ p4) → (((p4 ∧ (((p2 ∧ ((False ∧ p4) ∨ p5)) ∧ (True ∧ p3)) ∧ p2)) ∨ (p5 ∨ True)) ∨ p3))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179207667086862249754642320143 : ((p4 ∧ ((((p3 ∧ ((p2 ∨ (p2 ∧ p3)) → p2)) ∨ p3) ∨ p2) ∨ p5)) ∨ (p5 → (p3 → (p4 → (((True → True) → p1) → (p1 ∨ False)))))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h5 : (True → True) := by
    -- Implications on the right can always be decomposed.
    intro h6
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h7 := h4 h5
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_220011859666822471985463036946 : (((True ∧ True) ∧ True) ∧ (p5 → ((p2 → ((p4 → (True ∧ (True ∨ p5))) → (((False → p3) → (p2 → ((p1 ∨ True) ∧ p1))) → p3))) ∨ p5))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231436692479214377949682784372 : (((p2 → False) ∨ p5) → (((((p5 ∨ (True ∧ (p1 ∧ (p3 ∨ (False ∨ p4))))) → p4) ∨ ((p5 ∨ p1) ∨ p2)) ∨ (True ∧ True)) ∨ (p2 ∧ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_768975882803789347601957052206 : (((p5 ∧ (((p2 ∨ p5) ∨ p4) ∧ (((False → (p2 ∧ (True ∨ (p2 ∨ ((((p1 → p4) ∧ p1) → p4) ∨ False))))) ∧ (p2 ∧ False)) ∧ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217793098092838433088595727463 : (((False ∨ (False → p5)) → False) → ((((p3 ∨ p4) → p4) → ((p1 → True) → (p1 ∨ p3))) → ((True → (p3 ∧ (p1 ∧ (p3 → p5)))) ∧ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h4 : (False ∨ (False → p5)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- False on the left can always be used.
    apply False.elim h5
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h4
  -- False on the left can always be used.
  apply False.elim h6
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h7 : (False ∨ (False → p5)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- False on the left can always be used.
    apply False.elim h8
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h9 := h1 h7
  -- False on the left can always be used.
  apply False.elim h9
  -- Implications on the right can always be decomposed.
  intro h10
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h11 : (False ∨ (False → p5)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h12
    -- False on the left can always be used.
    apply False.elim h12
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h13 := h1 h11
  -- False on the left can always be used.
  apply False.elim h13
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h14 : (False ∨ (False → p5)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h15
    -- False on the left can always be used.
    apply False.elim h15
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h16 := h1 h14
  -- False on the left can always be used.
  apply False.elim h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_593071419447293141824597063488 : ((((((((p5 → p5) ∧ p4) ∧ ((p5 ∧ (True → ((True ∧ p4) ∧ (p4 → p4)))) ∨ (p2 ∨ p3))) → p5) ∨ (p3 → (True ∨ True))) ∧ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_89164013828083949274911110427 : ((((p2 ∨ True) → False) ∧ (p2 ∨ ((p5 → ((((p2 ∧ ((p4 → p2) → p2)) → p4) ∧ (True ∧ (p3 → p4))) ∧ p5)) ∨ (False ∨ p3)))) → False) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h5 : (p2 ∨ True) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h6 := h2 h5
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h9 : (p2 ∨ True) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h10 := h2 h9
      -- False on the left can always be used.
      apply False.elim h10
    case inr h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- False on the left can always be used.
        apply False.elim h12
      case inr h13 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h14 : (p2 ∨ True) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h15 := h2 h14
        -- False on the left can always be used.
        apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138214116003880776755640802274 : ((p2 → ((((((p5 → p1) → (p5 ∧ p4)) → (p1 ∧ False)) → p5) ∧ (p1 ∨ (p3 ∨ ((p4 ∨ False) → p3)))) ∨ p1)) ∨ ((p1 → True) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_254695694725091645979717119499 : ((p3 ∧ p3) → ((((p3 → (((p3 → p1) ∨ (True ∨ p1)) → (p5 ∨ (p3 ∧ p5)))) ∨ (True ∧ False)) ∨ (p5 → (True ∨ (p4 → False)))) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50333717804734521223798050119 : ((((p3 → (((True ∨ p2) → (True ∨ False)) ∧ False)) ∨ ((((p4 → p3) ∧ True) ∧ p4) ∧ (p1 → p3))) ∨ (((p2 ∧ p1) ∨ True) ∨ p4)) ∨ p2) := by
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
theorem thm_5_vars_252960771845232246519655985083 : ((True ∧ p2) → (((p3 ∨ ((p2 ∧ False) → p5)) → p4) → (p5 → ((((p1 → True) ∧ ((p1 ∧ p5) → p3)) → p4) ∨ (p2 ∧ (p3 ∧ p1)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h6
  -- Conjunctions on the left can always be decomposed.
  let h7 := h6.left
  let h8 := h6.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h9 : (p3 ∨ ((p2 ∧ False) → p5)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h10
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- False on the left can always be used.
    apply False.elim h12
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h13 := h2 h9
  -- One of the premise coincides with the conclusion.
  exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59548964306330291549481626237 : (((p3 → p1) ∨ (((True ∨ (p4 ∧ ((((p2 ∨ p5) → (p2 ∧ (p1 ∨ p1))) → p5) ∨ True))) → p2) → ((p1 ∧ (p2 → p5)) ∧ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324164440162607750676850939311 : (p5 ∨ ((((True → (p2 → (p3 ∨ p5))) → (p3 → True)) → p5) ∨ (p4 ∨ ((True ∧ ((((False ∧ (False ∧ p5)) → p5) → p3) ∧ p2)) ∨ True)))) := by
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
theorem thm_5_vars_111983298704088632789573638372 : (((((False → (p3 → p3)) ∧ (p5 ∧ p1)) → (p3 ∨ (p4 → (((((p3 ∧ False) → (p1 ∨ p4)) ∨ False) → p3) ∨ p4)))) ∨ p5) ∨ (p3 → p2)) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h6
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257567863016515233315136422849 : ((p3 ∨ p1) → ((((((p5 ∨ True) → p3) → p2) ∨ p2) ∧ (True → (False ∧ (p4 ∧ (False ∧ (p5 → False)))))) → (p5 ∧ (False ∧ (p4 ∧ p2))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h6 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h7 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h8 := h4 h7
      -- We need to get the left conjuct of h8 based on <expert-advice>.
      let h9 := h8.left
      -- False on the left can always be used.
      apply False.elim h9
    case inr h10 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h11 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h12 := h4 h11
      -- We need to get the left conjuct of h12 based on <expert-advice>.
      let h13 := h12.left
      -- False on the left can always be used.
      apply False.elim h13
  case inr h14 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h15 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h16 : True := by
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
      have h20 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h21 := h4 h20
      -- We need to get the left conjuct of h21 based on <expert-advice>.
      let h22 := h21.left
      -- False on the left can always be used.
      apply False.elim h22
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h23 := h2.left
  let h24 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h23
  case inl h25 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h26 =>
      -- We want to use the implication h24 based on <expert-advice>. So we show its premise.
      have h27 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h24, we can now drive its conclusion.
      let h28 := h24 h27
      -- We need to get the left conjuct of h28 based on <expert-advice>.
      let h29 := h28.left
      -- False on the left can always be used.
      apply False.elim h29
    case inr h30 =>
      -- We want to use the implication h24 based on <expert-advice>. So we show its premise.
      have h31 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h24, we can now drive its conclusion.
      let h32 := h24 h31
      -- We need to get the left conjuct of h32 based on <expert-advice>.
      let h33 := h32.left
      -- False on the left can always be used.
      apply False.elim h33
  case inr h34 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h35 =>
      -- We want to use the implication h24 based on <expert-advice>. So we show its premise.
      have h36 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h24, we can now drive its conclusion.
      let h37 := h24 h36
      -- We need to get the left conjuct of h37 based on <expert-advice>.
      let h38 := h37.left
      -- False on the left can always be used.
      apply False.elim h38
    case inr h39 =>
      -- We want to use the implication h24 based on <expert-advice>. So we show its premise.
      have h40 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h24, we can now drive its conclusion.
      let h41 := h24 h40
      -- We need to get the left conjuct of h41 based on <expert-advice>.
      let h42 := h41.left
      -- False on the left can always be used.
      apply False.elim h42
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h43 := h2.left
  let h44 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h43
  case inl h45 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h46 =>
      -- We want to use the implication h44 based on <expert-advice>. So we show its premise.
      have h47 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h44, we can now drive its conclusion.
      let h48 := h44 h47
      -- We need to get the left conjuct of h48 based on <expert-advice>.
      let h49 := h48.left
      -- False on the left can always be used.
      apply False.elim h49
    case inr h50 =>
      -- We want to use the implication h44 based on <expert-advice>. So we show its premise.
      have h51 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h44, we can now drive its conclusion.
      let h52 := h44 h51
      -- We need to get the left conjuct of h52 based on <expert-advice>.
      let h53 := h52.left
      -- False on the left can always be used.
      apply False.elim h53
  case inr h54 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h55 =>
      -- We want to use the implication h44 based on <expert-advice>. So we show its premise.
      have h56 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h44, we can now drive its conclusion.
      let h57 := h44 h56
      -- We need to get the left conjuct of h57 based on <expert-advice>.
      let h58 := h57.left
      -- False on the left can always be used.
      apply False.elim h58
    case inr h59 =>
      -- We want to use the implication h44 based on <expert-advice>. So we show its premise.
      have h60 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h44, we can now drive its conclusion.
      let h61 := h44 h60
      -- We need to get the left conjuct of h61 based on <expert-advice>.
      let h62 := h61.left
      -- False on the left can always be used.
      apply False.elim h62
  -- Conjunctions on the left can always be decomposed.
  let h63 := h2.left
  let h64 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h63
  case inl h65 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h66 =>
      -- We want to use the implication h64 based on <expert-advice>. So we show its premise.
      have h67 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h64, we can now drive its conclusion.
      let h68 := h64 h67
      -- We need to get the left conjuct of h68 based on <expert-advice>.
      let h69 := h68.left
      -- False on the left can always be used.
      apply False.elim h69
    case inr h70 =>
      -- We want to use the implication h64 based on <expert-advice>. So we show its premise.
      have h71 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h64, we can now drive its conclusion.
      let h72 := h64 h71
      -- We need to get the left conjuct of h72 based on <expert-advice>.
      let h73 := h72.left
      -- False on the left can always be used.
      apply False.elim h73
  case inr h74 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h75 =>
      -- One of the premise coincides with the conclusion.
      exact h74
    case inr h76 =>
      -- One of the premise coincides with the conclusion.
      exact h74



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_329310024699326555633665799797 : (True → ((p5 ∨ (p5 ∨ False)) ∨ ((((True ∧ (False → p1)) → (True ∧ p4)) ∨ False) → (((True → ((p2 ∧ p4) ∧ p1)) ∨ (False → p3)) ∨ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60474439855641872234557350394 : (((p5 → p5) → (((((p2 ∨ p4) ∧ ((p2 → (p5 → False)) ∨ p5)) ∨ (False ∨ ((False ∨ ((True ∧ p5) ∧ True)) ∨ p3))) ∨ p1) ∧ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179588554375955537228933827338 : ((p3 → ((((((p5 → p5) → p4) ∧ p4) ∨ p3) ∧ (p4 → p5)) ∨ p4)) ∨ (((p3 ∨ (p1 ∨ ((p1 ∧ (p1 ∨ p5)) ∨ p5))) ∧ p1) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41123017754526731415932836406 : ((((p5 → ((p4 → ((p4 → (p5 ∧ p5)) ∧ (False ∨ p4))) ∧ (p3 ∨ ((p4 ∧ p3) ∧ (p5 → p1))))) ∧ (p4 ∨ (p3 ∨ p2))) ∨ True) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218311300005302939900155881562 : (((p5 ∨ p4) ∨ (False ∨ p5)) → ((p5 → (((p2 → (p4 ∨ (p2 → (p1 → (True ∧ (p4 ∨ ((p3 ∨ p1) ∨ p3))))))) ∨ p5) ∨ True)) ∨ False)) := by
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
      -- Implications on the right can always be decomposed.
      intro h4
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h6
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- False on the left can always be used.
      apply False.elim h8
    case inr h9 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h10
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68738268657918042403488969601 : ((p4 → (((p3 → (p4 → (p5 ∨ p4))) ∨ (True → (False ∧ ((((True → True) → p1) ∧ p3) ∨ False)))) → (((True ∨ False) → False) → p3))) ∨ p4) := by
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
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h5 : (True ∨ False) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h6 := h3 h5
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h8 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h9 := h7 h8
    -- We need to get the left conjuct of h9 based on <expert-advice>.
    let h10 := h9.left
    -- False on the left can always be used.
    apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137268258555665639195119142110 : ((p1 ∧ (False ∨ ((p1 ∨ p4) ∧ (False ∨ (False → ((p4 → (p5 → (p4 ∧ (((p2 ∧ p1) → p4) ∨ p2)))) → p4)))))) ∨ ((False → p2) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_717698781979982155454330192642 : ((((((p5 ∨ p4) ∧ p2) ∧ False) ∨ ((((p3 ∧ ((False → ((p4 ∨ False) ∧ ((p3 → (p2 ∧ True)) → False))) ∧ p2)) → p5) → False) → p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199192268582934597351363349360 : (((p4 ∧ ((p5 ∧ p5) ∨ (p5 → p5))) ∧ p5) → ((((p5 → (p3 ∨ (p3 → False))) → (p1 ∧ p4)) ∨ ((p3 ∧ p2) → (p1 ∧ False))) ∨ True)) := by
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
    let h7 := h6.left
    let h8 := h6.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_223324617275648318732031364756 : ((True ∨ (False ∧ False)) ∧ (True → (((p3 ∨ (False → p1)) ∧ (p5 → (p4 ∨ ((p2 ∧ (True → (p1 → (p5 → p3)))) ∨ p4)))) ∨ (True ∨ p1)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193739080674899535159272847132 : ((p3 ∧ ((((p2 → p3) → (p4 ∧ True)) ∨ False) ∧ p3)) → (p3 ∧ ((p4 → (p2 ∨ (p5 ∧ p4))) ∨ (p4 ∨ (False → (False ∧ (p2 → p5))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h7 =>
    -- False on the left can always be used.
    apply False.elim h7
  -- Conjunctions on the left can always be decomposed.
  let h8 := h1.left
  let h9 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h10 := h9.left
  let h11 := h9.right
  -- Disjunctions on the left can always be decomposed.
  cases h10
  case inl h12 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h13
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- False on the left can always be used.
    apply False.elim h13
    -- Implications on the right can always be decomposed.
    intro h14
    -- False on the left can always be used.
    apply False.elim h13
  case inr h15 =>
    -- False on the left can always be used.
    apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40724901952116440451735198892 : (((((p1 ∨ (p3 ∨ (p5 ∨ (p5 → p2)))) ∨ ((False ∧ ((p2 ∧ ((p1 ∧ (p5 ∨ p3)) ∨ p2)) ∨ (True → False))) → p5)) → p5) ∨ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159231265071280999966503880867 : ((p3 → (((False ∧ ((p2 ∨ False) ∧ ((((p2 ∨ p1) ∨ p4) → True) → False))) ∧ (True ∧ p3)) ∨ p2)) ∨ (False → (True ∧ (p1 ∨ (p2 ∨ p1))))) := by
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
theorem thm_5_vars_215039650947827173677868998017 : (((p2 ∨ p5) → (p2 ∨ p1)) ∨ (((((((p4 → p2) → p2) → p4) → p2) ∧ (True → (((False → p3) ∨ p2) → p5))) → (p3 ∧ True)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300354019689215531000464423714 : (False ∨ (((((((((p4 ∧ p4) ∨ p4) ∧ ((False ∧ p3) → p2)) ∨ False) ∧ p5) ∨ True) ∧ ((p2 → p1) ∧ p4)) ∧ True) ∨ (False → (False → p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165479332477026494398954080969 : ((((False ∧ (((p4 ∨ p5) → p3) → (p5 ∧ p4))) ∨ p1) ∨ ((False → p1) ∨ (p3 ∧ p4))) ∨ (p3 ∧ (p5 → ((p5 ∧ p4) ∨ (p5 → p5))))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_903457877269581326643305754413 : ((((True → ((True ∧ (((p4 ∨ (False → ((p5 ∨ (p3 ∨ p3)) ∧ p2))) → (p4 → True)) ∨ p4)) ∧ False)) ∧ (p4 ∧ (p5 ∨ (p1 → False)))) → p1) ∧ True) := by
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
  cases h5
  case inl h6 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h7 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h8 := h2 h7
    -- We need to get the right conjuct of h8 based on <expert-advice>.
    let h9 := h8.right
    -- False on the left can always be used.
    apply False.elim h9
  case inr h10 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h11 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h12 := h2 h11
    -- We need to get the right conjuct of h12 based on <expert-advice>.
    let h13 := h12.right
    -- False on the left can always be used.
    apply False.elim h13
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_788297071733233671383459821626 : (((p5 ∨ ((((((True → (p5 ∨ p5)) ∧ (p2 ∨ True)) ∧ p2) → ((p2 ∧ False) ∧ ((((p1 ∨ False) ∧ True) ∨ True) ∧ p4))) ∧ True) ∨ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186838599354142591592261109053 : ((((p2 ∧ p1) ∨ (False ∨ False)) ∨ (p4 → (p5 ∧ (p1 → p3)))) → (((p1 ∨ (p1 → (p3 ∨ (p3 → False)))) → ((p3 ∨ p5) ∧ p4)) ∨ True)) := by
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
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- False on the left can always be used.
        apply False.elim h7
      case inr h8 =>
        -- False on the left can always be used.
        apply False.elim h8
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46265718318206989112276127922 : ((((p5 ∧ ((False → ((((p4 → False) ∨ p3) ∧ (True ∨ p2)) → (p1 → p5))) → ((p3 ∧ p4) ∨ p4))) → (p4 ∧ False)) ∧ (p1 → p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185321144059312421001648665222 : ((p3 ∧ ((p3 ∨ (p5 ∧ p2)) ∧ (p3 ∧ (p1 → (p1 ∧ False))))) ∨ (p3 ∨ (((p2 ∧ (p2 ∧ p3)) ∧ (p2 ∨ p2)) → (p5 ∨ (p1 → True))))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h10 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h11
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347208132301010014346394319103 : (p3 → ((p2 ∨ (((p3 → p3) ∨ True) ∧ ((p3 ∧ (True ∨ False)) → p5))) ∨ (((p5 ∧ (True → (p1 → p4))) ∧ ((False ∧ p1) → p3)) → p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_50701806345430744283792801615 : ((((p1 → (p5 → p5)) → ((((p4 ∨ (p3 → (p5 → p4))) → (True ∨ (False ∧ p3))) ∨ p2) ∧ p1)) → (((p3 ∨ True) ∨ p1) ∧ p1)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p1 → (p5 → p5)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h2
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315694515189009341781829835003 : (p3 ∨ ((p2 ∨ False) ∨ (p3 → (p3 ∧ ((p2 ∨ ((True ∨ True) → (((p1 ∨ p1) ∧ p2) ∨ (p5 ∨ p1)))) ∨ (p3 ∨ (p4 → (p2 ∨ True)))))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301197596662468113272061683776 : (False ∨ ((p3 → (False ∧ ((p3 ∧ p3) ∨ (False ∨ p3)))) → ((((True ∨ (((p4 ∨ p1) ∧ p1) ∧ p1)) ∧ True) ∨ p4) → (p3 ∨ (True ∧ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    cases h4
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Conjunctions on the left can always be decomposed.
      let h10 := h8.left
      let h11 := h8.right
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- True on the right can always be proven directly.
        apply True.intro
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h13 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- True on the right can always be proven directly.
        apply True.intro
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h14 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299293676058551718861700398904 : (False ∨ ((((((p4 ∨ (p4 ∧ (p1 → False))) ∨ p5) ∧ p2) ∧ False) ∧ ((p5 → (False ∨ (p4 ∧ (p1 ∧ (True ∧ (p1 → False)))))) ∨ p3)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179965219215354238240515324980 : ((((((p3 ∨ (p5 ∨ True)) ∧ p2) ∨ p2) ∨ (False → (p1 ∧ p3))) ∨ p5) → (True → ((p4 → (p3 ∨ p4)) ∨ (False ∧ ((p2 ∧ True) ∨ False))))) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h5 =>
        -- Conjunctions on the left can always be decomposed.
        let h6 := h5.left
        let h7 := h5.right
        -- Disjunctions on the left can always be decomposed.
        cases h6
        case inl h8 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Implications on the right can always be decomposed.
          intro h9
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h8
        case inr h10 =>
          -- Disjunctions on the left can always be decomposed.
          cases h10
          case inl h11 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Implications on the right can always be decomposed.
            intro h12
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h12
          case inr h13 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Implications on the right can always be decomposed.
            intro h14
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h14
      case inr h15 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h16
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h16
    case inr h17 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h18
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h18
  case inr h19 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h20
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h20



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299351986916516811773238517964 : (False ∨ (((True ∧ (p3 ∧ True)) → ((p4 ∧ (p2 ∧ p4)) ∨ ((p3 → (p2 → (p4 ∨ (p1 ∧ (((p4 ∧ True) ∧ False) ∨ False))))) ∨ True))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_325673766121552939673058817117 : (p5 ∨ (p1 ∨ (((p5 → (True → (((p4 ∨ False) ∧ p3) ∧ (((p3 → False) → p1) → True)))) → ((((True ∧ False) → p2) → p2) ∨ p4)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115527669107235997460601924663 : (((True ∧ (False → ((p2 ∧ p2) → (p5 → True)))) → (p4 ∧ ((((True ∨ ((False → (p3 → p5)) ∨ False)) ∨ p5) → False) → True))) ∨ (False → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_746315058656768303386962796777 : ((((p2 ∨ True) → ((p4 ∨ ((p1 ∧ True) ∨ True)) ∧ ((p4 ∨ True) ∨ (((True ∨ (True ∨ p3)) → p2) ∨ ((False ∨ (p5 ∧ p2)) ∨ p2))))) ∨ p5) ∧ True) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_792584233507069930958385703384 : (((True → (((p3 → ((p2 → (p4 ∧ p3)) ∧ p2)) ∨ p3) → ((((p4 ∨ p5) → (((p3 ∨ True) → p1) ∧ (p2 ∧ p4))) ∧ p4) ∧ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228810704444851935847604432296 : ((p3 ∨ (p2 ∨ p5)) ∨ ((True ∧ (p3 ∨ (p1 ∨ (False → ((((True → (p3 ∨ p4)) → p2) → (p3 → (p2 ∨ p4))) ∧ p1))))) ∨ (True ∧ p5))) := by
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
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_722880835118351681578993209296 : (((((p2 ∧ p4) ∨ p1) ∧ (((p1 ∧ (p4 → p1)) ∧ (p3 → ((p1 ∨ p3) ∧ ((p3 → False) ∨ ((True ∨ p2) ∧ p2))))) → (p2 ∧ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_349285616598645348758147962336 : (p3 → (p2 → (((p1 ∨ ((False ∨ ((p1 → (p5 → ((True ∨ (False ∧ p2)) ∨ p1))) ∨ p3)) ∧ (p2 ∧ p1))) → (p1 ∧ p5)) ∨ (p3 ∨ False)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190849659044925832006300290569 : (((((p1 ∧ (p2 → True)) ∨ p3) ∨ p1) → (p3 ∧ p1)) ∨ (((((((True → False) ∧ p3) ∧ p5) ∧ False) ∧ ((True ∧ True) ∧ False)) → True) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248637559038545310065335668619 : ((p3 ∨ p1) ∨ ((((((((p1 ∧ p3) ∧ (False ∨ p2)) ∨ p1) ∨ p1) ∨ (True ∨ p5)) ∨ p4) ∧ ((p4 → p1) ∨ p5)) ∨ (True ∨ (p5 → False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_689452717225032751611345177159 : (((((((False → p2) ∧ ((p4 → (p3 ∨ p1)) → p3)) → False) ∨ ((p3 ∨ p2) ∧ False)) ∨ (p4 ∨ (p5 ∨ (((False ∨ p2) → p5) ∨ p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119234762021670049035002245282 : ((p2 → ((True → True) → (((True ∧ ((p1 ∧ False) ∧ p5)) ∧ (p1 → p2)) ∧ (p3 ∨ ((p4 ∨ False) ∧ ((p1 → True) ∨ False)))))) ∨ (False → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315031884712865343949253788883 : (p3 ∨ ((True → ((((True ∨ p4) ∨ False) ∨ p3) ∧ p1)) ∨ (((((((p1 ∧ True) → p3) ∧ p4) → False) ∧ True) ∨ p3) ∨ (p5 ∨ (True ∨ p2))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_66360069060720982468169191083 : ((p5 ∨ (False ∨ (((p3 → p2) ∧ (((((p3 ∧ p1) ∧ ((True ∨ p4) ∧ p1)) → (p4 ∨ (p3 → p1))) → p4) ∧ True)) ∧ (p1 ∧ p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341669426857346838906526354741 : (p2 → ((((((((p2 ∧ (True ∧ p1)) → p4) ∧ p3) → p1) → (((((p5 → p4) → True) ∧ p3) ∨ p4) ∨ p4)) ∨ p3) ∨ p2) ∨ (p5 ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323227664370360494041068676629 : (p5 ∨ (((p1 ∧ ((False ∧ False) → (False ∧ (p5 → False)))) → (((p1 ∨ True) ∨ (False ∨ p4)) → ((p5 ∧ p3) ∨ (p2 ∧ p5)))) ∨ (True ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164684886304940819087590637377 : ((((p3 ∧ (p5 ∧ (((True ∨ p3) → (p5 ∨ ((p2 ∨ p3) ∧ p4))) ∧ p1))) ∧ p2) ∨ False) ∨ ((False ∧ (True → (True → (p3 ∧ False)))) → p3)) := by
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
theorem thm_5_vars_135263420505227862029368700169 : (((p4 ∧ (((p4 ∧ (p1 → p2)) ∧ (((p1 ∨ p2) → p5) ∧ p5)) ∨ (p3 ∨ (False → (p3 ∨ p5))))) → (p5 ∨ False)) ∨ (p1 → (False → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_613374993841052755591054831328 : (((((True ∧ (False ∨ (p1 → (p2 ∨ ((p1 → (p1 ∧ p1)) ∨ (p4 ∨ (p5 ∧ (p2 ∧ ((False ∨ p1) ∧ p4))))))))) → (p3 → False)) ∨ True) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_609228741548268920331860625277 : (((((((False ∨ p4) ∨ p2) ∨ (((((False → True) ∧ (p4 → p3)) ∨ p2) → (False ∧ (False ∧ p2))) → ((p1 → p4) ∨ True))) ∨ p3) ∨ True) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_110698294053614593538101906422 : ((((((p2 ∨ ((p1 → ((p2 ∧ (p4 ∧ (p2 → (p3 ∨ True)))) ∨ p5)) ∨ (p3 → p3))) ∨ (p4 → True)) ∧ False) ∧ p3) ∧ p4) ∨ (False ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300983755701907993559272848694 : (False ∨ (((((p1 → p3) ∨ p3) ∨ (p5 → (p4 → (p2 ∧ p1)))) ∧ p2) → ((p4 → (((p5 ∧ p4) ∨ p1) ∧ p5)) ∨ ((False ∨ True) ∨ False)))) := by
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
    cases h4
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h6 =>
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307416240526289222357157044237 : (p1 ∨ (p4 ∨ (p5 → (p3 → (p1 ∨ (((False ∨ (p2 ∨ ((p3 → True) ∧ (p5 → (p4 ∧ (False → p3)))))) ∧ p4) ∨ (False ∨ (p3 ∧ p5)))))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179356399883056434118266933389 : ((p2 ∨ ((p2 → ((False → (p4 ∧ p1)) → (p2 → (p4 ∨ p1)))) ∨ True)) ∨ (((((p5 → p4) ∨ p5) → p5) → (p2 ∧ (True → p4))) → p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_140486829557398089213935652346 : ((((((((False ∧ p3) → False) ∧ ((True → False) ∧ p3)) → (p5 ∧ p3)) → p1) → False) ∧ (((p1 → p4) → False) ∧ p5)) → ((p4 ∨ True) ∧ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h6 := h1.left
  let h7 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h7.left
  let h9 := h7.right
  -- One of the premise coincides with the conclusion.
  exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217070481081610753684194227673 : ((((p3 → p3) ∧ True) ∨ True) → ((p4 ∨ p5) ∨ (((p5 → (p2 → ((p3 ∨ p1) ∧ p1))) → (True ∨ False)) ∧ ((p4 ∨ True) ∧ (False ∨ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
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
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h7
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
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
theorem thm_5_vars_185089926936879873207171679212 : (((p3 ∨ p5) ∨ (True ∧ ((((p2 ∨ p2) ∧ p3) ∨ p1) ∨ True))) ∨ (p1 ∧ ((False ∨ (((p4 ∧ p5) ∧ (p4 ∨ (False ∨ p2))) ∨ p5)) ∧ True))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_790506367702777557880652698535 : (((p5 ∨ (False ∨ (p2 ∨ (p4 → ((p4 ∧ (p5 ∨ (p1 → (True → False)))) → ((p3 ∧ p1) ∨ (p5 ∨ (((p5 → True) ∨ p1) ∨ p2)))))))) ∨ p2) ∧ True) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h7
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299298715999918409460188423557 : (False ∨ (((True ∧ (((p1 ∧ (p2 → (False ∨ p4))) → p1) ∧ False)) ∨ ((((p3 → (p5 ∧ p1)) → (True ∨ (p2 ∨ p4))) ∨ False) → p4)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_216659561960213747980057686510 : ((((p3 ∨ p4) ∨ True) ∧ p1) → (((p3 → ((p3 ∨ (((((p4 ∨ p3) → p1) ∨ p2) → p5) ∨ p2)) ∨ p5)) → p3) → ((p4 ∨ p3) ∧ p3))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h7 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h7
  case inr h8 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h9 : (p3 → ((p3 ∨ (((((p4 ∨ p3) → p1) ∨ p2) → p5) ∨ p2)) ∨ p5)) := by
      -- Implications on the right can always be decomposed.
      intro h10
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h10
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h11 := h2 h9
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h11
  -- Conjunctions on the left can always be decomposed.
  let h12 := h1.left
  let h13 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h12
  case inl h14 =>
    -- Disjunctions on the left can always be decomposed.
    cases h14
    case inl h15 =>
      -- One of the premise coincides with the conclusion.
      exact h15
    case inr h16 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h17 : (p3 → ((p3 ∨ (((((p4 ∨ p3) → p1) ∨ p2) → p5) ∨ p2)) ∨ p5)) := by
        -- Implications on the right can always be decomposed.
        intro h18
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h18
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h19 := h2 h17
      -- One of the premise coincides with the conclusion.
      exact h19
  case inr h20 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h21 : (p3 → ((p3 ∨ (((((p4 ∨ p3) → p1) ∨ p2) → p5) ∨ p2)) ∨ p5)) := by
      -- Implications on the right can always be decomposed.
      intro h22
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h22
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h23 := h2 h21
    -- One of the premise coincides with the conclusion.
    exact h23



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_326145467491403977448053194613 : (p5 ∨ (p1 → (p5 ∨ ((True ∨ p4) ∧ (((p3 ∧ (p5 → (((p5 ∨ (p3 ∨ (p3 ∧ False))) → p5) → False))) ∨ (p1 → (True ∧ True))) ∧ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_395798836352393751277494299351 : ((((p3 ∧ ((((p4 ∨ p4) ∨ True) ∧ ((((((p5 ∧ (False → p2)) ∨ p2) → (True ∨ (p4 → p4))) ∨ p3) → p3) → p3)) → p3)) ∨ True) ∧ True) ∧ True) := by
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
theorem thm_5_vars_99052645062280678887737064662 : ((True → ((p1 ∨ (p5 ∨ p4)) ∧ (((False ∨ ((True → (p4 → True)) → ((p3 ∨ (((p2 → p3) ∧ p2) ∨ p1)) ∧ p2))) → False) ∧ False))) → p5) := by
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
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150995944692223466933820395645 : (((True → ((p5 → ((p4 ∧ (p5 ∧ True)) → (p4 → (((p4 → p4) → p5) ∨ (p5 ∧ p3))))) ∧ p2)) ∨ p3) → (p5 ∨ (p3 → (p2 ∨ True)))) := by
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
theorem thm_5_vars_938114998428172577044683298977 : ((((p1 → (p1 → ((p5 ∨ p5) ∧ False))) ∧ ((p1 ∧ (((p2 ∧ (False ∧ ((p3 ∨ p5) ∨ True))) → p2) ∨ (p2 ∧ (p3 ∧ True)))) ∨ False)) → p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h8 : p1 := by
        -- One of the premise coincides with the conclusion.
        exact h5
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h9 := h2 h8
      -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
      have h10 : p1 := by
        -- One of the premise coincides with the conclusion.
        exact h5
      -- We have shown the premise of h9, we can now drive its conclusion.
      let h11 := h9 h10
      -- We need to get the right conjuct of h11 based on <expert-advice>.
      let h12 := h11.right
      -- False on the left can always be used.
      apply False.elim h12
    case inr h13 =>
      -- Conjunctions on the left can always be decomposed.
      let h14 := h13.left
      let h15 := h13.right
      -- Conjunctions on the left can always be decomposed.
      let h16 := h15.left
      let h17 := h15.right
      -- One of the premise coincides with the conclusion.
      exact h14
  case inr h18 =>
    -- False on the left can always be used.
    apply False.elim h18
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173302301911024149887935445384 : ((p1 → (((p3 ∧ True) ∨ p4) → (False ∧ ((p5 → p4) → (p5 ∧ (p3 ∧ p1)))))) ∨ ((((p4 → (p2 ∧ False)) → p4) ∧ p5) ∨ (False → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_782652081953456389257236799831 : (((p3 ∨ (((True ∧ ((((True ∨ p3) ∨ p1) ∧ ((p5 ∨ p3) → ((True → False) ∨ p1))) ∧ (True → (p1 ∧ (p3 → p4))))) ∨ p4) → p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_312361459089897806987218233865 : (p2 ∨ (p3 → ((((((p4 ∨ p5) ∨ p1) ∧ ((True ∨ (False ∨ p1)) ∧ ((True ∨ True) → p4))) ∧ (p1 ∧ (p3 ∧ p2))) ∧ p3) ∨ (p5 → p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171600437737121694601153607577 : ((((p5 → ((p3 → (p1 → False)) → p3)) ∧ (p3 ∧ (True → (p4 → p4)))) ∨ p1) ∨ (((False ∧ p1) → p1) ∨ (p2 → (p1 ∧ (False → p4))))) := by
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
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113601073276423675698833232087 : (((False ∨ (p3 → (p1 → (((((True ∧ p5) ∧ p2) ∨ (p1 → p2)) ∧ False) ∨ (p3 ∧ (p3 ∧ (p2 ∨ p3))))))) ∨ (p2 ∨ p5)) ∨ (p3 → p1)) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117784256104205128690334012796 : ((p4 ∧ ((((((True ∨ p1) ∨ True) → True) ∧ (((True ∨ False) → (p2 ∨ p4)) ∧ False)) ∨ p2) → (((p3 → p5) ∨ p1) → p4))) ∨ (False → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51380322002262874388911748486 : (((((((True ∨ (p4 → ((p2 → p3) ∨ (False → p3)))) ∨ p2) ∨ p2) → (p4 → p3)) ∨ p5) → (((p4 → (p5 ∨ p4)) ∧ p1) ∧ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257019142927343370449071793257 : ((p2 ∨ True) → (((p4 → ((((p2 ∨ p4) → ((False ∧ p4) → (p2 ∧ p4))) ∨ p2) → (p3 → True))) → (p2 ∨ p5)) → ((p5 ∨ p1) ∨ p2))) := by
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
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h5 : (p4 → ((((p2 ∨ p4) → ((False ∧ p4) → (p2 ∧ p4))) ∨ p2) → (p3 → True))) := by
      -- Implications on the right can always be decomposed.
      intro h6
      -- Implications on the right can always be decomposed.
      intro h7
      -- Implications on the right can always be decomposed.
      intro h8
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h9 := h2 h5
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h10
    case inr h11 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_631631063094980123865122383559 : (((((((p4 → (p2 ∧ (p3 ∨ ((p3 ∧ (p1 ∨ (p2 ∨ p1))) → (True ∧ True))))) → False) → (p4 ∨ ((True → True) → p4))) → p5) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_650643478805297725185110247876 : (((((p1 → (p2 → ((False ∨ p1) → ((p2 → p3) ∨ False)))) ∧ (((p5 ∧ (True ∧ p1)) → p4) → (p5 ∨ (p4 ∨ False)))) ∧ (p1 ∨ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



