variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52392482470324391841105089108 : ((((((False ∧ p4) ∧ p2) → (p1 → p2)) → ((p3 ∨ False) ∨ (True → p4))) ∧ ((False ∨ (p5 ∧ p5)) ∧ ((p3 → (True ∨ p3)) → p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205851623533245530217597839684 : (((p3 → p2) → ((p4 ∧ False) ∧ True)) ∨ (False ∨ (((False → p1) ∨ p4) ∨ (((p2 ∧ (((p1 ∧ (True ∨ p5)) ∨ p3) ∨ p3)) → p1) → p1)))) := by
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
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_326924862491471153682803043433 : (True → ((((p1 ∨ p3) ∨ ((((p3 ∨ p4) ∧ (p3 ∨ p4)) → p3) ∨ (p3 ∧ (p2 ∧ ((p5 → p4) ∧ (p3 ∧ (False ∧ p2))))))) → p1) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328606131699822577452031276953 : (True → ((((p5 ∨ (p2 ∨ (p2 ∨ (False ∨ (p5 ∨ p4))))) → (False ∨ False)) ∨ p2) ∨ (((p5 → (False ∨ True)) ∧ p5) ∨ (p3 → (p2 → p2))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55628458668786579374594633075 : (((p5 → ((p3 ∨ p3) → (p1 ∧ p5))) → (((p2 → p5) ∧ (False ∧ (p1 → p2))) ∧ ((p4 ∧ ((True → p5) ∧ (False ∨ p2))) → p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191918316175975404904071695895 : ((p5 ∨ (p1 → ((p1 → ((False → False) ∧ p5)) → p2))) ∨ ((True ∨ True) → (p4 → ((((p5 → p2) → p2) → p1) ∨ ((False → p2) ∨ p4))))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114567927251213198942946721257 : (((((p5 ∨ ((True → p3) → ((p4 ∧ (p5 ∧ p1)) ∨ True))) → p1) ∨ (True ∧ p1)) ∧ ((p4 ∨ (p4 ∨ True)) ∧ (p5 ∨ False))) ∨ (False → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_140512147038085425447724354565 : ((((True ∨ p5) → (((p3 ∧ (True ∧ p1)) ∨ (p5 ∧ ((p2 ∧ p4) → p4))) ∧ p4)) ∧ (((p2 ∧ p1) ∧ p4) → p5)) → ((True → p1) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (True ∨ p5) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h12
    -- One of the premise coincides with the conclusion.
    exact h11
  case inr h13 =>
    -- Conjunctions on the left can always be decomposed.
    let h14 := h13.left
    let h15 := h13.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_768094970208326027988365265747 : (((p5 ∧ (((False ∨ (((p2 → ((p2 ∨ (((False ∧ p4) ∧ True) ∨ False)) ∨ False)) ∨ p5) → (p4 ∧ (False ∨ p1)))) ∨ p5) ∨ (True → p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164159343346986992193597048647 : ((p4 ∨ (((((False ∧ (p4 ∧ p3)) ∨ p4) ∧ p4) ∨ ((p4 ∨ p2) ∧ p2)) ∨ (p2 ∨ True))) ∧ ((True ∧ (p3 → (False → p2))) ∨ (p1 → p5))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_14022310868390092481303875974 : ((((((p1 ∨ p4) ∧ (p1 → (p5 ∧ (p3 ∧ p5)))) ∧ p1) ∨ ((p5 ∧ ((p3 → (p2 ∨ p1)) → p2)) → (True → p5))) ∧ (True → True)) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Implications on the right can always be decomposed.
  intro h5
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42239656286697782648088319754 : (((False ∧ (p1 ∧ ((((((p4 ∧ p3) → (True → (True → p5))) → p3) ∨ False) ∧ (((p1 ∧ p5) → p4) → (False → p2))) ∨ p2))) ∨ True) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47543513476341213801931758457 : (((p5 ∨ ((p4 ∨ ((p3 → ((p2 ∧ p2) ∧ (False ∨ True))) ∧ p1)) ∧ (((p3 ∧ False) ∨ (p3 ∨ p5)) → (p1 ∧ p4)))) ∨ (False → p5)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_255506812250754240160920022968 : ((p5 ∧ p2) → (((((False ∧ (p1 ∧ (p5 → p3))) ∨ p1) ∨ (p5 ∨ p3)) → False) ∨ ((p1 → (False ∧ (True → ((p1 ∧ p5) ∧ p2)))) ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_777499896315774847646569346775 : (((p1 ∨ (((p3 ∧ p5) ∨ (((False ∨ (p2 ∨ p5)) ∧ p3) ∧ (False ∨ (p5 ∨ True)))) ∨ (((p3 ∨ p4) → (False → (True → p2))) ∨ True))) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_233982972571731221024949240436 : ((p5 ∨ (p5 ∧ p4)) → ((p1 ∨ ((p2 → (True → p4)) → (((p1 ∨ (((p4 ∨ p5) ∧ p2) ∧ p1)) ∨ (p2 → (p2 ∨ p1))) ∧ p5))) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h9
    -- One of the premise coincides with the conclusion.
    exact h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113729812237894086047512013847 : ((((p5 → ((p3 → (True ∨ ((True ∧ p1) ∧ ((p4 → False) ∨ (p5 ∨ p1))))) → False)) ∨ (False ∧ (True → p4))) → (p1 ∧ p1)) ∨ (False ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215334148092861967631981286397 : ((p1 ∧ (p3 ∨ (p3 ∨ False))) ∨ (True ∧ (((False ∧ (True ∧ (True → (((True ∨ p1) → p2) ∧ (p3 ∨ True))))) ∧ p5) ∨ ((p3 ∨ p3) → True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_665714791489535905924358601847 : (((((p5 ∨ (p3 ∧ ((((p2 → False) → ((False ∨ (p3 ∧ p1)) ∧ ((p3 ∧ p5) → p5))) → True) ∧ p3))) ∨ p4) ∧ ((p5 ∨ p5) ∧ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_627658651615040501964379677981 : (((((((p1 → p3) → (p5 → (((p2 ∧ (((p2 ∨ p4) ∧ p1) ∧ True)) ∨ (False → p3)) ∧ p1))) ∧ ((p4 ∧ p3) ∨ True)) ∧ p2) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_103048296606528681979337409398 : (((((p5 → (True → (p1 ∧ p4))) → p1) ∨ (False ∨ (False ∨ (p1 → ((False ∧ p2) → ((p1 ∧ p3) ∨ (p2 ∧ p5))))))) ∨ False) ∧ (p2 ∨ True)) := by
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
  -- False on the left can always be used.
  apply False.elim h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207451744699800196410479112908 : (((p4 ∨ (p4 ∨ (p3 ∨ p3))) ∨ False) → (p5 ∨ (((p3 ∨ (p1 → False)) ∧ (p3 ∧ p4)) ∨ ((False → (False ∧ ((p5 ∧ p5) ∨ p4))) ∨ p4)))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h4 =>
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h5 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h5
      case inr h6 =>
        -- Disjunctions on the left can always be decomposed.
        cases h6
        case inl h7 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Implications on the right can always be decomposed.
          intro h8
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- False on the left can always be used.
          apply False.elim h8
          -- False on the left can always be used.
          apply False.elim h8
        case inr h9 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Implications on the right can always be decomposed.
          intro h10
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- False on the left can always be used.
          apply False.elim h10
          -- False on the left can always be used.
          apply False.elim h10
  case inr h11 =>
    -- False on the left can always be used.
    apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56455145695690584882422882142 : ((((p2 → p1) ∨ (p1 → p1)) → ((((((p5 ∧ p1) ∨ (False → ((False ∨ p1) → (p3 ∨ p3)))) → p5) ∨ False) ∧ p3) → (p5 ∨ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_961333128574993094428475911650 : ((((p2 ∨ p1) ∧ (((((p2 ∧ p4) ∨ (((((p5 → False) ∨ True) → (p2 ∨ True)) ∧ (p3 → p3)) ∨ p3)) ∨ p5) → (p3 ∧ False)) ∨ False)) → p4) ∧ True) := by
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
    cases h3
    case inl h5 =>
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h6 : (((p2 ∧ p4) ∨ (((((p5 → False) ∨ True) → (p2 ∨ True)) ∧ (p3 → p3)) ∨ p3)) ∨ p5) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Implications on the right can always be decomposed.
        intro h7
        -- Disjunctions on the left can always be decomposed.
        cases h7
        case inl h8 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h4
        case inr h9 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h4
        -- Implications on the right can always be decomposed.
        intro h10
        -- One of the premise coincides with the conclusion.
        exact h10
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h11 := h5 h6
      -- We need to get the right conjuct of h11 based on <expert-advice>.
      let h12 := h11.right
      -- False on the left can always be used.
      apply False.elim h12
    case inr h13 =>
      -- False on the left can always be used.
      apply False.elim h13
  case inr h14 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h15 =>
      -- We want to use the implication h15 based on <expert-advice>. So we show its premise.
      have h16 : (((p2 ∧ p4) ∨ (((((p5 → False) ∨ True) → (p2 ∨ True)) ∧ (p3 → p3)) ∨ p3)) ∨ p5) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Implications on the right can always be decomposed.
        intro h17
        -- Disjunctions on the left can always be decomposed.
        cases h17
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
        -- Implications on the right can always be decomposed.
        intro h20
        -- One of the premise coincides with the conclusion.
        exact h20
      -- We have shown the premise of h15, we can now drive its conclusion.
      let h21 := h15 h16
      -- We need to get the right conjuct of h21 based on <expert-advice>.
      let h22 := h21.right
      -- False on the left can always be used.
      apply False.elim h22
    case inr h23 =>
      -- False on the left can always be used.
      apply False.elim h23
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173734005505775768864425491156 : ((((p1 ∧ ((False → p3) → ((p4 ∧ p5) ∧ p1))) ∨ ((p4 → p4) → p5)) ∨ True) → (((False ∧ (p1 → p4)) ∧ (False ∨ p1)) ∨ (p5 → True))) := by
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
theorem thm_5_vars_179960953307156416829312810736 : ((((((p3 → p5) ∧ (p5 → True)) ∨ False) ∧ (p5 ∨ (p1 ∧ True))) ∨ p2) → ((((True ∧ (False ∨ p1)) → p5) ∧ p4) → (p5 ∨ (False ∨ True)))) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h12 =>
        -- Conjunctions on the left can always be decomposed.
        let h13 := h12.left
        let h14 := h12.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h15 =>
      -- False on the left can always be used.
      apply False.elim h15
  case inr h16 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_654304745409480242444688774775 : ((((((p3 ∧ (p4 ∧ ((p1 ∨ p3) ∨ ((p4 ∧ False) ∨ ((p2 ∨ p1) → (True ∧ False)))))) ∧ ((True ∧ True) ∧ p3)) ∨ p3) ∨ (True ∨ False)) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_191205564587813787187066349179 : ((((p4 ∧ p5) → p2) → (p5 ∧ (p3 → (True ∧ p5)))) ∨ ((False ∨ (p1 ∨ (p2 → (((((False ∨ False) → p1) → p2) ∧ False) ∨ True)))) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_734622445414479694885508571694 : ((((p1 ∨ p3) ∧ ((p1 ∧ (((False → (p2 ∧ p4)) → p2) → p5)) ∧ ((((p5 → (p4 ∨ True)) → p2) ∧ (False ∨ (False ∨ p3))) → p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_77520170092794505715792837633 : (((True ∧ (((p2 → ((p4 → ((p5 ∨ p5) ∧ (True ∧ p2))) ∧ (p3 → (p5 ∧ (p5 ∧ (True ∧ p5)))))) ∨ True) ∨ (p3 ∧ p5))) → False) → p4) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (True ∧ (((p2 → ((p4 → ((p5 ∨ p5) ∧ (True ∧ p2))) ∧ (p3 → (p5 ∧ (p5 ∧ (True ∧ p5)))))) ∨ True) ∨ (p3 ∧ p5))) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58769504779149086986045422237 : (((p4 → p2) ∧ (p5 ∧ (True → (p2 ∨ (p1 ∧ ((((p3 ∨ p5) ∨ (True → ((p5 ∨ p1) ∨ True))) → ((False ∨ p3) ∧ False)) ∨ p3)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_254834406995571920771172420275 : ((p3 ∧ p5) → ((((((p2 ∨ p4) ∧ True) ∧ False) → p4) → (p2 ∨ (((p1 ∧ (True ∨ p1)) ∧ True) ∨ p4))) ∨ ((p2 ∧ p1) → (p3 → p3)))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134614517809510846803025512657 : (((((p4 → ((False ∧ (False → p4)) → (True → p3))) ∨ ((p5 ∧ (p2 ∧ p5)) → p2)) ∨ ((True ∨ p3) ∨ False)) → p1) ∨ (False ∨ (p5 → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63058905895166074885135538821 : ((p5 ∧ (((p4 → p3) → (((p5 ∨ p3) → (False ∧ (p4 ∧ (p3 → (p2 → ((((p1 ∨ p3) → p3) ∨ False) → False)))))) ∧ p4)) ∧ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111992433230399460079293378245 : (((((p1 → False) ∨ (p2 ∨ p3)) ∧ (((p1 → ((False ∨ True) → (((p3 ∨ True) ∨ (False → p1)) → p3))) ∨ True) → p2)) ∨ True) ∨ (True ∧ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156937900187165609647792130071 : ((((((p1 → (((p3 → False) ∧ (p1 → p1)) → (False → False))) ∨ True) → False) ∨ (p3 ∨ p2)) ∨ False) ∨ ((p2 ∧ p4) → ((p4 ∧ p3) → p2))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_312080786503005659852243044248 : (p2 ∨ (p5 ∨ ((p2 ∨ False) ∨ (((p4 ∧ p2) → (p5 → (p5 ∨ (p4 ∨ (p4 → ((((p1 ∧ p5) ∨ p1) → p2) ∨ p5)))))) → (False ∨ True))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_799041756391725003529223677070 : (((p1 → ((p1 ∨ p1) → ((False ∧ ((p3 ∧ (((p2 → (True ∨ (p2 → True))) ∧ (True ∨ p5)) ∨ p3)) → (p3 ∧ p5))) ∧ (False ∧ p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51248898264274148440621067696 : ((((p1 ∧ p1) ∧ ((((True ∨ True) → p3) ∧ p1) → (p3 ∧ (((True → p2) ∨ False) ∧ p4)))) ∨ ((True ∧ (True ∨ (p3 ∧ p3))) ∨ True)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_749601089888236672833182697345 : (((True ∧ ((((p4 ∨ (p5 ∧ (p2 ∨ (((p1 ∧ (p1 → p2)) → p2) ∧ (p1 → (False ∨ (p5 → (p1 ∨ p5)))))))) ∧ p4) ∧ p2) ∨ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_873983375670124172926902213449 : ((((p4 → (False ∨ ((((p2 → False) ∨ True) ∧ ((False ∨ (((p1 ∧ p4) → p1) ∨ p2)) → p1)) ∨ (((p1 ∨ p1) ∨ False) ∨ p4)))) → False) → False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p4 → (False ∨ ((((p2 → False) ∨ True) ∧ ((False ∨ (((p1 ∧ p4) → p1) ∨ p2)) → p1)) ∨ (((p1 ∨ p1) ∨ False) ∨ p4)))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- False on the left can always be used.
  apply False.elim h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37789943904666650973999599940 : (((((p4 ∧ p1) → (((((p2 ∨ (((p4 ∧ p3) → False) ∧ (p1 ∧ p3))) ∨ False) ∧ False) ∨ (p4 → (p2 → False))) → p4)) → p2) ∧ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2467648417775032076090304862 : ((True ∧ (((False ∧ p1) → False) → (p2 → (False ∧ p1)))) ∨ (((p1 → p3) ∨ (p1 ∨ p2)) → ((True → (p4 → (p1 ∧ False))) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191240121215207775225830832480 : (((True ∧ p1) ∧ ((((p3 ∧ p3) ∧ True) ∨ p5) ∧ p1)) ∨ (p3 → (((False ∨ p3) ∨ ((p5 ∧ (p2 → p2)) → False)) → ((False → p5) ∨ p4)))) := by
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
      -- False on the left can always be used.
      apply False.elim h4
    case inr h5 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h6
      -- False on the left can always be used.
      apply False.elim h6
  case inr h7 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h8
    -- False on the left can always be used.
    apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114530248968039376889876927422 : (((p3 ∨ ((p5 ∨ ((p1 ∨ (((True ∧ p1) → False) ∧ p5)) ∨ (p2 ∧ (p5 ∧ p3)))) → True)) → ((p5 ∨ (p5 ∧ p3)) ∧ p3)) ∨ (False → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185107093966129105144373768624 : (((p2 → p1) ∨ (((p1 ∧ p1) ∨ (False → False)) → (p3 ∨ p5))) ∨ ((False → p1) ∨ ((p5 ∨ (p4 ∨ p1)) ∧ (p2 → ((p1 ∧ True) ∧ p1))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_221642107816306974560499171527 : (((p5 → p2) ∨ True) ∧ (((p3 ∧ ((False ∧ True) ∨ p1)) ∧ (True → ((p1 → p3) ∨ ((True ∧ p5) → p1)))) ∨ ((p2 ∧ (p3 → False)) ∨ True))) := by
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
theorem thm_5_vars_304715325136967397316240478356 : (p1 ∨ (((((p4 → p4) ∧ (((((True ∧ p3) ∨ p2) ∧ (p4 ∨ p1)) ∨ p1) → (p1 ∧ True))) → p4) ∧ ((False ∨ p2) → p2)) ∨ (False → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_738674624312198770233223696447 : ((((p2 ∧ p1) ∨ (((((((p4 ∧ p1) → p1) ∧ p2) ∨ p3) ∨ (p4 ∨ True)) ∧ False) ∧ (p3 → (p3 ∨ (((p3 ∨ False) ∧ p3) ∧ p1))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_106127156447124155136111301690 : ((((p5 ∧ ((p4 → (False ∨ (True ∨ True))) ∧ True)) ∧ (p1 ∧ p4)) ∨ ((p5 → True) ∧ (((True → p5) ∧ p1) ∨ (False → p3)))) ∧ (True ∧ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- False on the left can always be used.
  apply False.elim h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54449525059591783409099617554 : (((((p2 ∧ ((False → True) ∧ True)) → p5) → p4) ∨ (((False → p3) → (p1 ∨ ((p1 → p4) ∨ ((p1 → False) ∨ (p5 ∨ False))))) ∨ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_8615888728417512572280620342 : (((((p5 ∧ True) ∨ ((p4 ∧ p4) ∧ (p4 ∨ ((True ∨ p3) ∧ (p5 ∧ ((True → p4) → (p2 → (False ∧ p2)))))))) ∨ (p3 → True)) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_208154557726360754783857909615 : ((((p3 → p4) → True) → (p5 ∧ p4)) → (((((((p1 ∨ p5) ∧ p1) ∨ (p3 ∧ (p2 ∧ ((p2 ∨ p4) ∨ True)))) → p2) ∧ p1) ∨ p4) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p3 → p4) → True) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345687592082816382146034423955 : (p3 → ((p4 ∨ ((p3 ∨ (((((p4 ∨ p1) ∧ p4) ∧ p1) → ((False ∧ ((p5 → False) → (True → (p5 ∧ p5)))) ∧ p1)) → p5)) → False)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337944509494572217937293853879 : (p1 → (((((p2 ∨ p2) ∨ (False → (p1 ∨ p4))) → (p2 ∧ p5)) → p4) ∨ (p2 ∨ (False → ((False → (p2 → p1)) → ((p3 → p5) ∨ p3)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_636128387520045582296913961644 : ((((((p1 ∧ (((p3 ∧ (p5 → True)) ∨ (p3 ∨ (p2 ∧ p2))) ∧ (p1 ∨ p1))) ∨ p2) ∨ ((p2 ∧ ((p4 ∧ p4) ∨ p4)) ∧ p5)) → p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150830345843912732619008339904 : ((((p1 → ((p2 → (p2 ∧ ((True → (True ∧ p2)) → (p1 ∨ p5)))) ∧ False)) ∨ (True ∨ (p2 ∧ p2))) ∨ False) → ((p4 ∧ (p3 ∧ False)) ∨ True)) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h4
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
    -- False on the left can always be used.
    apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40731913240721082570900356983 : ((((((p5 ∧ (p2 ∧ True)) → True) ∨ (True ∧ ((((p5 ∨ (True ∨ True)) ∨ ((p5 → True) → p5)) → p5) ∧ (p4 ∨ p5)))) → p2) ∨ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180029121328282235259936712210 : (((p2 ∧ (((p3 → p4) ∨ ((p4 ∧ p3) ∨ p2)) → (p3 → p4))) ∨ p5) → ((p4 ∨ (False → p1)) → (p2 → (p2 ∧ (p3 → (p1 → p1)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h8 =>
      -- One of the premise coincides with the conclusion.
      exact h3
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- One of the premise coincides with the conclusion.
      exact h11
    case inr h13 =>
      -- One of the premise coincides with the conclusion.
      exact h3
  -- Implications on the right can always be decomposed.
  intro h14
  -- Implications on the right can always be decomposed.
  intro h15
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h16 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h17 =>
      -- Conjunctions on the left can always be decomposed.
      let h18 := h17.left
      let h19 := h17.right
      -- One of the premise coincides with the conclusion.
      exact h15
    case inr h20 =>
      -- One of the premise coincides with the conclusion.
      exact h15
  case inr h21 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h22 =>
      -- Conjunctions on the left can always be decomposed.
      let h23 := h22.left
      let h24 := h22.right
      -- One of the premise coincides with the conclusion.
      exact h15
    case inr h25 =>
      -- One of the premise coincides with the conclusion.
      exact h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57853139905105842431621527892 : (((True ∨ (p5 ∨ p4)) → ((True ∨ (p4 → p2)) → (((p1 ∨ True) ∨ p1) ∨ (p2 ∨ (((p2 → (p4 ∨ p3)) → (p5 → p2)) ∨ p2))))) ∨ p4) := by
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
    cases h1
    case inl h4 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h7 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h9 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h12 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_741519856939272199303276012748 : ((((p5 ∨ p3) ∨ (p1 ∧ (((((p2 ∧ ((p2 ∧ p1) → False)) ∧ (True ∨ (p3 → p5))) ∨ ((p2 ∨ False) ∨ p3)) → (p3 ∧ p5)) ∨ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52154418525983636664983614174 : (((((p4 → ((p1 ∧ p3) ∨ (p3 ∧ (p3 → p5)))) → True) ∨ (p3 ∨ (p3 → p4))) → (p5 → ((p2 → (p3 → (p3 ∧ False))) ∨ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47888936920035016251062127049 : (((((p5 ∧ (p1 → ((p4 ∨ p3) ∧ (((False ∧ p3) → p1) ∨ p1)))) ∧ (p2 ∨ (p2 → (p2 ∧ True)))) ∨ (p3 → p2)) → (p5 ∧ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_793720196643841798496583894434 : (((True → (True → (True → (((p5 ∨ p2) ∧ True) ∨ ((((False → p5) ∧ False) ∧ (p4 ∨ ((True ∨ p1) ∨ ((p1 ∨ p2) ∧ p1)))) ∧ p4))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53793718122650023233383430488 : (((((((True ∨ p4) ∨ (p2 ∨ False)) ∨ p4) → True) → p4) ∨ (((p1 → (p4 ∧ (p5 ∨ (p1 → p5)))) ∧ (True ∧ p3)) ∨ (p2 → True))) ∨ p4) := by
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
theorem thm_5_vars_48311941615638207613431010294 : (((False ∨ ((((p3 ∧ p5) ∧ (((p3 ∧ (False ∧ (False ∨ p2))) ∧ ((False ∧ p3) ∧ True)) → (p4 → p4))) ∨ p5) → p5)) → (True → p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_395216429070563695692720111391 : ((((p1 ∧ (((p3 ∧ ((p2 ∨ (p4 ∧ (True ∧ (p4 ∨ True)))) ∧ ((p1 → (p1 ∨ p2)) ∨ True))) ∧ (p2 → (p3 ∨ True))) ∨ False)) ∨ True) ∧ True) ∧ True) := by
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
theorem thm_5_vars_801435483989473241695611242621 : (((p2 → ((p2 ∧ ((p5 ∧ (p3 ∨ (p2 ∧ (p5 ∧ p4)))) → False)) ∨ (((True ∧ p2) ∧ ((p4 ∧ (p1 ∨ (p1 ∨ True))) ∧ p3)) → p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204557293451909185883239371334 : ((((p3 → (p4 → p5)) → p1) ∨ p3) ∨ (p5 → (p5 → ((p5 → ((p1 ∧ p2) ∧ (True ∨ (p5 ∨ True)))) → (p2 ∧ ((False → False) ∧ p1)))))) := by
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
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : p5 := by
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- One of the premise coincides with the conclusion.
  exact h7
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h8
  -- False on the left can always be used.
  apply False.elim h8
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h9 : p5 := by
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h10 := h3 h9
  -- We need to get the left conjuct of h10 based on <expert-advice>.
  let h11 := h10.left
  -- We need to get the left conjuct of h11 based on <expert-advice>.
  let h12 := h11.left
  -- One of the premise coincides with the conclusion.
  exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_131917015537490393558562724776 : (((p1 ∨ False) ∨ ((((p2 ∨ p5) ∧ False) ∧ (p3 ∨ (p3 ∧ (p3 → p3)))) ∨ ((p3 ∧ ((p2 ∧ False) ∨ p2)) → True))) ∧ ((p3 ∨ p2) → True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68785455197819497114641824496 : ((p4 → (((((p1 → p2) ∧ True) ∨ (p4 → True)) ∨ p4) → ((((p3 ∧ p2) ∨ True) ∧ (True ∧ True)) ∧ ((p4 → (p5 ∧ p2)) ∨ p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_123134708104429379913687878452 : ((((p5 ∧ (True ∨ (True ∧ p1))) → (p4 ∨ (((p5 ∧ ((False ∧ (False ∧ False)) ∧ p3)) ∨ True) ∨ p2))) → ((p5 ∧ p3) ∧ True)) → (p5 ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p5 ∧ (True ∨ (True ∧ p1))) → (p4 ∨ (((p5 ∧ ((False ∧ (False ∧ False)) ∧ p3)) ∨ True) ∨ p2))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
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
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h10 := h1 h2
  -- We need to get the left conjuct of h10 based on <expert-advice>.
  let h11 := h10.left
  -- We need to get the left conjuct of h11 based on <expert-advice>.
  let h12 := h11.left
  -- One of the premise coincides with the conclusion.
  exact h12
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_674657072815015949986946412311 : ((((p1 → ((((((True ∨ p1) ∨ p3) ∨ False) ∧ p1) → (p3 ∧ True)) ∧ ((p3 ∧ p3) → (p3 → (p1 → p5))))) → (False ∨ (p5 ∨ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116695440227544236604233173845 : (((False ∧ p1) ∨ (((p5 ∧ (False ∧ p2)) ∧ (p1 ∧ p4)) ∨ ((p3 ∨ ((p4 → p4) ∨ p5)) → (p2 ∨ (False → (p4 ∨ p5)))))) ∨ (False → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342209248042357183985181530310 : (p2 → (((p3 ∧ ((p4 ∧ (p5 ∧ p1)) ∨ True)) ∧ (p2 ∧ (True ∧ ((((p2 ∧ p4) ∧ p1) → p3) ∧ p5)))) → ((p1 ∨ (p3 → p4)) ∨ p2))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Conjunctions on the left can always be decomposed.
    let h12 := h4.left
    let h13 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h14 := h13.left
    let h15 := h13.right
    -- Conjunctions on the left can always be decomposed.
    let h16 := h15.left
    let h17 := h15.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h18 =>
    -- Conjunctions on the left can always be decomposed.
    let h19 := h4.left
    let h20 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h21 := h20.left
    let h22 := h20.right
    -- Conjunctions on the left can always be decomposed.
    let h23 := h22.left
    let h24 := h22.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_196313350962775222446813227052 : ((p4 ∨ (((p4 ∧ (False ∧ False)) ∧ p4) ∨ True)) ∧ (((p4 ∨ (p4 ∧ (((p4 ∧ False) ∨ p5) ∧ p1))) → (p2 → (p3 ∨ (p2 ∨ p2)))) ∨ p3)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- False on the left can always be used.
      apply False.elim h11
    case inr h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_106218506794811956864222483186 : (((p5 ∧ ((((False → (p1 ∧ p5)) → p3) → (p3 ∧ p5)) ∨ p4)) → (((p2 ∨ p1) ∨ (True → ((p2 → p1) → p3))) ∨ True)) ∧ (True ∨ p4)) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66067233134414808707584404042 : ((p5 ∨ ((((p5 ∧ ((p5 → p4) → False)) ∧ True) ∨ (p1 → (((p4 ∧ ((p1 ∨ p5) ∨ p3)) ∨ ((True → p4) ∨ p1)) ∨ p1))) ∨ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_624275719605683454624387613527 : ((((p3 ∨ ((((True ∨ p2) ∧ ((((True → (p5 ∧ (True ∨ p5))) ∨ p2) → p1) ∧ (True ∨ (p5 → True)))) ∨ p4) ∨ (True ∧ p3))) ∨ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_7820937307732126259217977742 : (((((p3 ∨ (True → (p1 ∧ False))) ∨ (((True ∧ ((False ∧ True) → p2)) → (p3 ∨ (p4 → (p3 → p5)))) ∧ (p5 → p3))) ∧ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308490398868665146405800163644 : (p2 ∨ (((p1 → (((p4 ∨ p3) ∨ ((p3 → p5) → (((p4 ∨ True) → ((p2 → p3) ∨ p3)) ∨ False))) ∧ p1)) ∨ ((True ∨ True) ∧ True)) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_631110414752276094716762688370 : (((((((p5 ∨ p3) → ((((p2 ∨ p1) ∧ p2) → ((p3 → p1) → (p5 → p3))) ∧ (((p5 ∨ False) ∨ False) → True))) ∨ True) → False) → p4) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p5 ∨ p3) → ((((p2 ∨ p1) ∧ p2) → ((p3 → p1) → (p5 → p3))) ∧ (((p5 ∨ False) ∨ False) → True))) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51185555778134129389849630826 : ((((True ∧ ((p5 ∨ ((p4 → (p5 ∧ p5)) ∨ (p2 → p4))) → p5)) ∧ (False ∧ (p5 ∧ p5))) ∨ (p2 ∨ ((False → p3) ∨ (False ∨ p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256457850121900987691002707836 : ((False ∨ p4) → ((((p1 ∧ p3) ∧ True) ∧ (((p4 → (p2 ∧ (True ∨ (True ∧ True)))) → ((p4 → (p5 → p4)) → False)) ∧ (False → False))) ∨ True)) := by
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
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54681410472957029029026183222 : (((((True ∧ p4) ∧ ((p2 → p1) → True)) → True) → ((p4 → (p4 → (p3 ∧ False))) ∨ ((p2 ∧ (((False ∨ p5) ∧ p3) ∨ p1)) ∧ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207538632670002038357427976541 : ((((p5 ∨ (p2 ∨ True)) ∧ p3) → p5) → (p4 → ((((p2 ∧ p1) ∧ p2) → (((p1 ∧ ((False → p5) → p3)) → (p2 → p5)) ∧ True)) ∧ p4))) := by
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
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h3.left
  let h9 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h10 := h8.left
  let h11 := h8.right
  -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
  have h12 : (False → p5) := by
    -- Implications on the right can always be decomposed.
    intro h13
    -- False on the left can always be used.
    apply False.elim h13
  -- We have shown the premise of h7, we can now drive its conclusion.
  let h14 := h7 h12
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h15 : ((p5 ∨ (p2 ∨ True)) ∧ p3) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h9
    -- One of the premise coincides with the conclusion.
    exact h14
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h16 := h1 h15
  -- One of the premise coincides with the conclusion.
  exact h16
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184807058554550691748077398477 : (((True → (p4 → (False ∨ p3))) ∨ (p1 → (False ∨ (False ∧ p2)))) ∨ (p2 → (False ∨ (p5 → (p5 ∧ (True → ((p5 ∨ p4) ∨ (True ∨ p2)))))))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112854972297660718566845407531 : (((((p3 ∨ False) ∧ False) ∨ (((p1 ∧ p5) ∨ ((False → (((p2 ∨ p4) ∧ p2) ∨ (False → True))) → p1)) → (p4 ∨ p5))) → p3) ∨ (False → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_691146242679328004077611959024 : ((((((p4 → (((p5 → p1) ∨ p1) ∧ True)) → p1) → (p1 → ((p4 ∨ p5) → p1))) → (((True → False) ∧ (p4 → (True ∧ False))) → p5)) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300821562075021786255627441189 : (False ∨ (((True ∨ p1) ∧ (((p3 ∨ (p4 ∧ p5)) ∨ True) ∨ ((False ∧ p5) → (p2 → p5)))) → ((p2 ∨ p5) ∨ (True ∨ (p2 → (True ∧ p1)))))) := by
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
          -- Conjunctions on the left can always be decomposed.
          let h9 := h8.left
          let h10 := h8.right
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h10
      case inr h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h13 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h14 =>
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h15 =>
        -- Disjunctions on the left can always be decomposed.
        cases h15
        case inl h16 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h17 =>
          -- Conjunctions on the left can always be decomposed.
          let h18 := h17.left
          let h19 := h17.right
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h19
      case inr h20 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h21 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245722471903864310260183074212 : ((p3 ∧ p2) ∨ (((((p2 ∨ False) ∧ (p5 ∧ p3)) ∨ (p4 ∧ ((False → (p3 → p5)) → (p2 ∧ p1)))) ∧ (p1 → p4)) ∨ (p2 → (True ∨ p2)))) := by
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
theorem thm_5_vars_315076096534479818430900616062 : (p3 ∨ (((p4 ∨ ((p1 ∨ False) ∨ False)) ∨ True) ∧ ((p4 ∨ (((True ∨ p3) ∧ False) ∧ (p5 ∧ p2))) ∨ ((True ∨ (False ∨ p4)) → (p5 → p5))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- False on the left can always be used.
      apply False.elim h5
    case inr h6 =>
      -- One of the premise coincides with the conclusion.
      exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45481560891627717768409200556 : (((False ∨ ((True ∨ ((p3 → ((p4 → p1) ∧ p3)) → (p3 → p3))) → ((p4 → True) ∨ ((p4 → (p1 ∧ (p3 ∨ p2))) → True)))) → p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187072381162930511023818261533 : (((p4 ∨ p2) ∧ ((((p2 → (p4 → False)) ∨ False) ∨ True) ∧ p1)) → (((p4 → p5) ∧ (((p2 ∨ (p2 ∨ p1)) → False) ∧ (p1 ∨ False))) → p5)) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h1.left
    let h9 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h9.left
      let h12 := h9.right
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h13 =>
        -- Disjunctions on the left can always be decomposed.
        cases h13
        case inl h14 =>
          -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
          have h15 : p4 := by
            -- One of the premise coincides with the conclusion.
            exact h10
          -- We have shown the premise of h3, we can now drive its conclusion.
          let h16 := h3 h15
          -- One of the premise coincides with the conclusion.
          exact h16
        case inr h17 =>
          -- False on the left can always be used.
          apply False.elim h17
      case inr h18 =>
        -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
        have h19 : p4 := by
          -- One of the premise coincides with the conclusion.
          exact h10
        -- We have shown the premise of h3, we can now drive its conclusion.
        let h20 := h3 h19
        -- One of the premise coincides with the conclusion.
        exact h20
    case inr h21 =>
      -- Conjunctions on the left can always be decomposed.
      let h22 := h9.left
      let h23 := h9.right
      -- Disjunctions on the left can always be decomposed.
      cases h22
      case inl h24 =>
        -- Disjunctions on the left can always be decomposed.
        cases h24
        case inl h25 =>
          -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
          have h26 : (p2 ∨ (p2 ∨ p1)) := by
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h21
          -- We have shown the premise of h5, we can now drive its conclusion.
          let h27 := h5 h26
          -- False on the left can always be used.
          apply False.elim h27
        case inr h28 =>
          -- False on the left can always be used.
          apply False.elim h28
      case inr h29 =>
        -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
        have h30 : (p2 ∨ (p2 ∨ p1)) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h21
        -- We have shown the premise of h5, we can now drive its conclusion.
        let h31 := h5 h30
        -- False on the left can always be used.
        apply False.elim h31
  case inr h32 =>
    -- False on the left can always be used.
    apply False.elim h32



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138181252943986367300114324732 : ((p1 → ((p1 ∧ p4) ∧ ((p4 ∨ (((p2 ∨ True) ∨ p2) ∨ p3)) → ((p1 → p3) ∨ (p5 ∨ (p1 ∨ (p4 → p3))))))) ∨ (False → (False → False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_660477619114685684698698526781 : ((((((p3 → (False ∨ (((p5 → p4) → True) ∧ (((p1 → ((True ∧ (p1 → False)) → True)) → p5) ∨ p4)))) ∧ False) → p4) → (p5 ∨ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219686650041293536069494416275 : ((p1 → ((p3 ∨ p5) ∧ True)) → (((p3 → ((p1 → p1) ∧ (p1 → (p5 → (p5 ∧ ((p2 ∨ False) ∧ False)))))) ∨ (False → (p2 → p3))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314441395101412940667623331233 : (p3 ∨ ((p4 ∨ (p4 ∨ ((p3 ∨ False) ∨ ((p2 ∨ (((p3 → p4) ∨ (p5 ∨ p3)) → (p4 → p1))) → p5)))) ∨ (p1 → ((True ∨ p3) → p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
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
theorem thm_5_vars_349347138298324194431675760784 : (p3 → (p3 → ((p2 ∨ (p1 ∧ (((p3 → p2) ∨ p5) ∨ (p4 → ((p1 ∧ p2) ∨ (True ∧ ((p2 ∨ (p1 ∧ False)) ∨ True))))))) ∨ (True ∨ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49210682876207991355898721635 : ((((True ∧ False) ∧ (((True → True) ∨ ((p5 ∧ ((p4 ∨ (p5 ∧ p2)) → p4)) → (p2 ∧ (True ∨ p5)))) → p5)) ∨ ((True ∨ p3) → p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



