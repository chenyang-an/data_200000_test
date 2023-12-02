variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192956072842454945710195758935 : (((False ∧ (False ∧ ((p4 ∨ False) ∨ p2))) ∨ (p4 ∨ p1)) → ((p2 ∨ (False ∨ (((p4 ∨ False) ∨ (p5 ∧ p4)) ∧ (False ∨ (True ∨ p2))))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- False on the left can always be used.
    apply False.elim h3
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59171630054501411073400603928 : (((False ∨ p4) ∨ (((p2 → False) → (((p4 ∨ False) → (p5 ∨ (p5 → ((True → (p5 ∧ (False ∧ p2))) ∨ p2)))) ∧ False)) ∨ (p5 → p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116045126007356141401309989709 : (((True → (p3 ∧ (p2 ∧ p5))) → ((((((p3 ∨ p5) → p4) ∧ (False → (False ∧ p1))) ∧ p4) ∨ (p5 ∨ False)) ∨ (p2 → True))) ∨ (p5 ∧ True)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_355946734138529204946776137458 : (p5 → ((p4 ∧ (((True → (False ∧ p1)) ∧ (p3 ∨ (p5 → False))) ∧ ((True ∧ ((False ∧ p4) ∨ (p2 ∧ p3))) → False))) → ((p4 ∧ p5) ∧ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h9 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h10 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  -- Conjunctions on the left can always be decomposed.
  let h11 := h2.left
  let h12 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h13 := h12.left
  let h14 := h12.right
  -- Conjunctions on the left can always be decomposed.
  let h15 := h13.left
  let h16 := h13.right
  -- Disjunctions on the left can always be decomposed.
  cases h16
  case inl h17 =>
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h18 =>
    -- One of the premise coincides with the conclusion.
    exact h1
  -- Conjunctions on the left can always be decomposed.
  let h19 := h2.left
  let h20 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h21 := h20.left
  let h22 := h20.right
  -- Conjunctions on the left can always be decomposed.
  let h23 := h21.left
  let h24 := h21.right
  -- Disjunctions on the left can always be decomposed.
  cases h24
  case inl h25 =>
    -- We want to use the implication h23 based on <expert-advice>. So we show its premise.
    have h26 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h23, we can now drive its conclusion.
    let h27 := h23 h26
    -- We need to get the left conjuct of h27 based on <expert-advice>.
    let h28 := h27.left
    -- False on the left can always be used.
    apply False.elim h28
  case inr h29 =>
    -- We want to use the implication h29 based on <expert-advice>. So we show its premise.
    have h30 : p5 := by
      -- One of the premise coincides with the conclusion.
      exact h1
    -- We have shown the premise of h29, we can now drive its conclusion.
    let h31 := h29 h30
    -- False on the left can always be used.
    apply False.elim h31



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_593718739997177371563736791335 : (((((((p1 ∧ ((p3 ∧ True) → p2)) ∧ p3) ∨ ((((p2 ∨ (p3 ∨ p4)) ∨ p2) ∨ p3) ∧ p4)) ∧ (True ∨ ((False ∧ p5) ∧ p3))) ∧ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_221138093313198015026708438954 : (((True ∨ p3) ∨ p1) ∧ (p5 → (((p1 ∧ False) ∨ (p2 ∧ (((p2 ∨ True) → p1) → p3))) ∨ ((p2 → ((True ∨ p5) ∨ p2)) → (p3 → p3))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49185742837348461610047804439 : (((((p5 → (p4 ∧ p4)) → p5) → (((((((p5 ∧ p5) → p2) → p3) ∧ False) ∧ False) ∨ (p1 → p4)) ∨ p5)) ∨ (False → (p2 ∧ p1))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_201082892481509771451759300456 : ((p5 ∨ (p4 ∧ ((p4 ∨ p1) ∨ (p1 ∧ False)))) → ((p4 ∨ ((p4 → p5) → p1)) ∨ (p5 → ((p3 ∨ (True ∧ ((p4 → p3) → True))) ∧ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Implications on the right can always be decomposed.
    intro h4
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h9
      case inr h10 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h6
    case inr h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- False on the left can always be used.
      apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206524140962146112951856948721 : ((True → (((True ∨ p2) → True) ∧ p3)) ∨ (((((((((True → p3) ∧ p5) ∧ False) ∧ (p3 ∨ False)) ∨ True) ∨ p4) → False) → (p3 ∧ p1)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324482485629692438794657434949 : (p5 ∨ (((False ∧ (False → p1)) ∨ False) ∨ ((((p2 ∨ p4) → ((p4 ∨ p2) → p2)) ∧ p4) ∨ ((p5 ∧ (((False ∧ p5) ∧ p1) ∧ p5)) → p5)))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_793695970340583276090113600408 : (((True → (True → ((False ∧ (((((((p3 ∨ p4) ∧ p4) ∨ p2) ∧ False) ∨ p1) → (False → (p3 ∧ (p4 ∧ p2)))) → p1)) ∧ (p4 ∧ p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_648836221067016484117463995476 : (((((p3 → ((((p1 → ((p1 → p5) ∨ (True → p1))) → (p5 ∨ p2)) ∧ (True → (False ∨ p5))) ∧ (True ∧ p4))) ∨ p2) ∧ (False ∧ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257218668259405577287986325567 : ((p2 ∨ p2) → ((p3 ∧ p1) ∨ (((False ∧ p5) ∧ (((p1 ∧ p1) ∧ ((p2 ∧ (p5 ∨ False)) ∨ p1)) ∨ ((p1 ∨ p3) ∨ False))) ∨ (False → True)))) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47071919572248313489081937931 : ((((p3 ∨ (((p3 ∨ p5) → (p5 → (p1 ∧ (p4 ∨ ((True → True) ∧ ((p2 ∨ p2) → p3)))))) ∨ p1)) ∨ (p1 ∧ p1)) ∨ (p1 ∧ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68999878287794065915842633997 : ((p5 → ((((True → (p5 ∧ ((p3 ∨ p2) ∨ p3))) → (((p1 ∧ p1) ∧ p3) ∧ True)) ∨ (p2 ∧ ((False ∧ p4) ∨ (p5 → False)))) ∧ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347407057731801451939159307680 : (p3 → (((p3 ∨ (p1 ∧ ((p1 → p5) → p1))) → p2) → (((((p4 → (True ∨ p1)) ∧ p5) ∧ p4) ∧ (p4 ∧ p1)) → ((p5 ∨ p2) ∨ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- Conjunctions on the left can always be decomposed.
  let h10 := h5.left
  let h11 := h5.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_247528994798741446368755780009 : ((False ∨ p4) ∨ ((((((True → p2) ∨ p5) ∨ (p2 → ((((p1 ∧ p3) → (False → p1)) ∧ (True ∨ p4)) → p4))) → False) ∨ (p4 → p4)) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48559344152160524397710916830 : (((((False ∨ ((p1 ∨ p3) ∧ ((p5 ∧ ((True ∨ p2) ∨ p1)) ∧ p5))) ∨ (((p5 ∧ p1) ∨ True) ∧ p5)) → p2) ∧ (True → (True ∧ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56653856025717657169572839520 : ((((p3 ∨ p2) ∧ p3) ∧ (False ∨ ((((p1 ∧ True) ∧ (False → p3)) ∨ (True ∧ ((p5 ∨ True) ∧ False))) ∨ ((p1 → (p3 → False)) ∨ False)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198890665307743119204482449627 : ((p3 → ((p4 ∧ (p3 ∧ (False ∨ p1))) ∧ False)) ∨ ((((p5 → (p1 ∨ ((((p1 ∧ p5) → p1) → p2) ∨ p4))) → p5) → p5) ∨ (p4 → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118780852138647882688646137642 : ((p5 ∨ (p3 ∨ (((((p4 → p3) → p5) ∨ False) → (p2 ∧ (p1 ∨ ((p1 ∨ ((True ∨ p4) → p4)) ∧ (False ∨ p1))))) ∧ False))) ∨ (True ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233876329978873022896221113228 : ((p4 ∨ (False ∨ p4)) → (((p2 ∧ False) ∨ (p2 ∧ (p2 → (p4 → ((p3 → p2) → ((p3 ∧ ((p5 ∧ True) ∨ p1)) ∧ p5)))))) ∨ (p5 ∨ True))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- False on the left can always be used.
      apply False.elim h4
    case inr h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184270231202512292685589277607 : (((((p5 ∧ ((False → p1) ∨ p3)) ∧ True) → (True ∨ p3)) → p2) ∨ (((((p2 ∧ p3) ∨ p3) ∨ p1) → (p4 ∨ True)) ∧ (p1 ∨ (True ∨ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
      -- Conjunctions on the left can always be decomposed.
      let h4 := h3.left
      let h5 := h3.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171344559122838134475919677418 : (((((p2 → ((p3 ∧ False) ∧ p3)) ∧ ((p3 ∧ (p3 ∨ p4)) ∧ p5)) → False) ∧ p3) ∨ ((p2 → (p2 ∧ (p3 → True))) ∨ (p2 ∧ (p2 → False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51747712271192582621533889346 : ((((p2 → (p4 ∨ True)) → ((p5 ∨ ((p4 ∧ ((p1 ∧ p2) → False)) → p2)) ∨ p2)) ∧ (((((p2 ∨ p4) → p3) ∧ p5) → p5) ∧ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_312008647385366384840382250346 : (p2 ∨ (p4 ∨ (((p3 → (((False → (p5 → p5)) ∨ (False ∨ p4)) ∨ p4)) → False) → (False ∨ (((p4 ∧ p5) ∨ (p2 → (p3 ∧ True))) ∧ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p3 → (((False → (p5 → p5)) ∨ (False ∨ p4)) ∨ p4)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- False on the left can always be used.
    apply False.elim h4
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h2
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41402981578790415947178218165 : ((((((p3 ∧ (p3 ∨ ((p4 ∧ p4) → p4))) ∨ ((True ∧ p5) → p1)) ∧ p3) ∨ ((p5 → (p3 ∧ p3)) → (p5 → (p5 ∧ False)))) ∨ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_209340457445191292732878853235 : ((False → ((p5 → p3) ∨ (p2 ∧ p4))) → ((((p4 ∨ (((((p5 ∨ p2) ∧ (p4 ∨ False)) → p3) ∨ p4) → (True ∧ p4))) ∧ p3) ∨ p4) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258081381763321803061010313954 : ((p4 ∨ p2) → (p4 ∨ (((((p3 ∧ (p3 → False)) ∧ ((True ∧ (p1 → p4)) → False)) ∨ True) ∨ ((p1 → (p1 → True)) → (False ∧ p3))) ∧ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
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
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50456964711160856704767907508 : (((p4 ∨ ((False → (((p4 ∧ (p2 → (p3 ∧ (False → p1)))) ∨ (p4 → p4)) ∧ (p2 ∧ p4))) → p1)) ∨ (((p3 → p3) → p1) → p1)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p3 → p3) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232766153852947621887149953823 : ((p2 ∧ (True ∧ p1)) → (((((((((p4 ∧ p2) ∧ (p4 ∨ p5)) ∧ (p4 ∧ False)) ∧ True) ∨ p3) ∧ (True → p1)) ∨ True) ∨ p1) ∨ (False → p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341686102002487529358224363970 : (p2 → ((((True → p1) ∧ (((p4 ∨ ((((p1 → (p3 ∧ p2)) ∧ (p3 ∧ p1)) → True) ∧ p4)) → (p5 ∧ p2)) ∨ p5)) → p3) ∨ (True ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_750288347963580012753830721652 : (((True ∧ ((p4 ∧ ((False ∧ p5) ∧ (((((p5 → (p4 ∧ p1)) → p2) → p5) ∨ (p5 → (p5 ∨ True))) ∧ (p1 ∧ p3)))) ∨ (False → False))) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190563596293228350556353752210 : (((((p4 ∨ p4) ∧ p5) ∧ (False → (p1 ∧ True))) → False) ∨ (((True ∨ ((p4 → (True ∧ (p5 ∨ (p3 → p5)))) ∨ p3)) ∧ (p2 ∨ p5)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56047993764639825070352761629 : (((((p1 ∨ p4) ∧ True) → p1) ∨ (p4 ∧ ((p2 → p3) ∨ (((p4 ∨ p2) → (p3 → p1)) ∨ ((p5 → ((True → True) → p1)) ∧ p3))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135708117419111687950294419580 : ((((p1 ∨ p5) → (((p1 → (p3 ∨ (False ∧ (p5 ∨ p1)))) ∧ False) ∨ p1)) ∧ (True ∨ (p5 ∨ (p3 ∨ (p4 → True))))) ∨ (False → (p1 ∧ p3))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_84069362667290075258452583871 : (((((((p2 ∧ p4) ∧ p1) ∨ p5) ∧ (True → False)) ∧ (p5 → (p1 → (p3 → p2)))) ∧ ((p5 → (False ∨ ((True → p1) ∨ True))) ∧ p2)) → p3) := by
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
  cases h6
  case inl h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Conjunctions on the left can always be decomposed.
    let h11 := h9.left
    let h12 := h9.right
    -- Conjunctions on the left can always be decomposed.
    let h13 := h3.left
    let h14 := h3.right
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h15 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h16 := h7 h15
    -- False on the left can always be used.
    apply False.elim h16
  case inr h17 =>
    -- Conjunctions on the left can always be decomposed.
    let h18 := h3.left
    let h19 := h3.right
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h20 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h21 := h7 h20
    -- False on the left can always be used.
    apply False.elim h21



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54730885891681272493743531687 : (((((p3 ∧ True) → False) ∨ (p4 ∨ (p3 → p3))) → ((p3 ∨ ((((False ∧ p3) ∧ ((p2 ∨ p2) ∨ True)) ∨ p2) ∧ (p3 ∨ p4))) → p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61171578870402047069070227543 : ((False ∧ ((p4 ∨ (p4 ∨ p2)) ∨ ((p5 → (p3 ∨ (p2 → (((p2 → p3) ∧ p4) ∧ p3)))) ∨ ((p2 ∨ (p4 ∧ (True ∧ p3))) ∧ True)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215131737159452318579455433492 : (((p4 → False) → (p5 → p2)) ∨ ((p4 → p4) → ((False ∨ (((p3 ∧ (p5 ∨ (p2 → p5))) → (p3 ∧ False)) ∧ ((p3 ∨ p1) ∧ True))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61405606625657271469959695851 : ((p1 ∧ ((True → ((p5 ∧ True) ∨ (p5 ∧ (p5 → ((((True ∧ p1) ∨ ((p2 ∨ (True → p2)) ∨ (p3 ∧ False))) → True) ∨ p4))))) ∨ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_9882560808381491149525563552 : (((False ∧ (p2 ∨ (((((p4 ∨ (p3 → (p3 → (p5 ∨ False)))) ∨ (p2 ∧ ((False ∧ p5) ∨ (p5 ∧ p3)))) ∧ p4) → p3) → False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137868620985265781713659790621 : ((p3 ∨ (True → (((p1 ∨ p3) ∧ ((p4 ∨ (p4 → p1)) ∧ False)) ∨ (p4 → ((True ∧ p2) → ((p1 ∨ p1) → p1)))))) ∨ ((p2 → False) → p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h3.left
    let h7 := h3.right
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h3.left
    let h10 := h3.right
    -- One of the premise coincides with the conclusion.
    exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_685679219881345821951805755623 : ((((((False ∨ p3) ∨ ((p4 → (True → p3)) ∧ ((p3 → (True ∧ p2)) → (p2 ∧ False)))) ∨ p3) → ((p2 ∧ p1) ∨ ((p3 → p3) ∨ p1))) ∨ False) ∧ True) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h4 =>
        -- False on the left can always be used.
        apply False.elim h4
      case inr h5 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h6
        -- One of the premise coincides with the conclusion.
        exact h6
    case inr h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h10
      -- One of the premise coincides with the conclusion.
      exact h10
  case inr h11 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h12
    -- One of the premise coincides with the conclusion.
    exact h12
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_712987355881616000824065391377 : ((((p2 ∧ ((p5 ∨ (p2 ∧ False)) ∧ p1)) ∨ (p3 ∨ ((True ∧ (((((p3 ∧ p5) ∨ (p5 → p3)) → p1) → p1) ∧ p1)) ∨ (p4 ∧ True)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58652862748056297694763577214 : (((p1 → p3) ∧ ((False ∧ ((((p2 → p4) ∧ p1) → False) → ((((p1 ∨ (False ∨ (p5 ∨ p3))) ∧ (p2 → p1)) ∧ True) ∧ p4))) ∧ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_183799710553874218864636989658 : ((((((False ∨ p1) ∧ (p5 ∨ p2)) → (p3 ∨ p2)) ∨ p4) ∧ p4) ∨ ((p5 → p3) ∨ ((True ∧ (p2 → ((p1 → False) → (False ∨ p3)))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_792586729008574916411825030110 : (((True → (((p3 → (True ∧ ((p4 ∧ True) → True))) → p1) → (p5 ∧ (((((p1 → (False ∧ p1)) ∨ p4) ∧ p5) ∨ p4) ∨ (p1 ∧ p3))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_229753771080174078456032893495 : ((p4 → (p2 ∨ p3)) ∨ ((((((p5 ∧ (p2 ∨ ((p1 → p3) ∨ p3))) → p1) → (p2 ∧ (True → p4))) ∧ (p4 → False)) → p3) ∨ (p1 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_201313808767691481415179533418 : ((p4 → (False → (p4 → (p5 ∨ (p4 ∨ p3))))) → (((True ∨ p1) → p3) ∨ ((p2 ∨ (False → (((True ∨ p3) ∧ True) ∧ (p1 ∧ p2)))) → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134717937326024568912913497841 : (((((p4 ∨ p1) ∨ p1) ∨ ((((p4 ∧ p2) ∨ (False ∨ False)) ∨ (p5 → (((True → p1) ∨ p3) ∨ p1))) ∧ p2)) → p1) ∨ ((True ∧ p2) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149414492421720676168058559025 : ((True ∧ ((p3 ∨ ((p3 ∧ ((True ∧ p5) ∨ p5)) → True)) ∧ ((p2 ∨ (False → (False ∧ p5))) → (p1 → False)))) ∨ ((p3 ∧ False) → (p1 ∨ p2))) := by
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
theorem thm_5_vars_797345141330992622058534271967 : (((p1 → (((False ∨ ((p4 ∧ p2) ∨ (p2 → ((False → False) → (p2 ∧ p2))))) → (((p1 ∧ (p2 ∨ p5)) → (True → p4)) ∨ True)) ∨ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147887994371375995630132518524 : (((((p4 ∨ p5) ∨ ((True ∨ p2) ∨ (((p2 ∧ (p3 ∨ p3)) → (p2 ∨ p1)) ∨ p4))) ∧ p2) ∧ (p1 ∨ p5)) ∨ (True ∧ (p1 → (p2 ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_352793083882441322305308441276 : (p4 → ((p1 ∨ p3) → (((True → ((((((True ∨ (p1 → p2)) ∧ False) → p5) → False) ∨ p1) ∧ ((p3 ∧ p2) ∧ False))) ∧ (p5 → p2)) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_145126606657005526996747498299 : (((p3 ∧ (p2 ∨ (False ∧ ((p4 ∨ (p1 → False)) ∧ True)))) ∨ (True ∧ ((False ∧ (p4 ∨ p5)) ∨ (False → p5)))) ∧ ((p3 ∨ False) → (p3 ∨ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- False on the left can always be used.
  apply False.elim h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- False on the left can always be used.
    apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340455565840314802325741933384 : (p2 → (((((p3 ∧ ((False → p1) ∨ p4)) ∧ p1) ∧ ((p1 → ((False ∨ p2) → p4)) → p3)) → ((p1 ∧ (True → True)) ∧ (p1 → True))) ∧ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h9 =>
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h10 =>
    -- One of the premise coincides with the conclusion.
    exact h6
  -- Implications on the right can always be decomposed.
  intro h11
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h12
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319659693881370501626296540344 : (p4 ∨ ((((p5 ∧ ((False ∧ p1) ∧ p1)) → p2) ∧ p4) → ((((False → p1) → (p2 ∨ (p2 ∧ (p3 ∧ ((p5 ∧ p4) ∨ False))))) ∨ p4) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199832099170448855343242452511 : ((((p5 ∨ False) ∨ (p2 → False)) ∧ (p2 → False)) → ((((p4 → p4) → ((True ∧ (p5 ∨ ((p5 ∧ p1) → p4))) ∧ (p5 → True))) ∨ True) ∨ p4)) := by
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h6 =>
      -- False on the left can always be used.
      apply False.elim h6
  case inr h7 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323676214368225890247506723419 : (p5 ∨ (((p4 ∨ p3) ∧ (p2 → ((p4 → (True → (False ∧ (False ∧ p5)))) ∨ (((p5 → p2) ∨ p5) → p5)))) ∨ ((False ∧ (p1 ∨ p5)) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215485571872953634354354364396 : ((p4 ∧ ((False ∨ True) ∧ p5)) ∨ (((((p5 → (p4 ∧ (((p2 → p2) → p2) → (False ∨ (p4 ∨ True))))) ∨ p4) ∧ p2) ∧ p5) → (p4 ∨ p3))) := by
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
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h7 : p5 := by
      -- One of the premise coincides with the conclusion.
      exact h3
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h8 := h6 h7
    -- We need to get the left conjuct of h8 based on <expert-advice>.
    let h9 := h8.left
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h9
  case inr h10 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234443465911073206327359163956 : ((p2 → (p3 ∧ p3)) → ((p2 ∨ (True → ((p4 ∧ (((((((True → p2) ∧ False) ∨ p5) → p1) ∧ p3) → p5) ∧ p3)) ∨ True))) ∨ (p4 ∧ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41796542347146547540425979169 : ((((True ∧ (p1 ∨ (p1 → False))) → ((((False ∨ (False ∨ False)) ∨ (p2 ∨ (((p1 ∧ p2) ∧ False) ∧ p4))) → (p2 → False)) ∨ p2)) ∨ True) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_626484613634669798923676359843 : ((((p4 → ((p4 ∧ (p4 ∧ ((False ∨ ((True → p2) → p1)) → ((p3 ∧ p4) → (p2 ∧ (False ∨ (p5 ∧ p2))))))) ∨ (p5 ∧ True))) ∨ True) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_319490211500073684181330274074 : (p4 ∨ (((p3 ∧ (p2 ∨ False)) ∧ (p2 ∧ ((p5 ∨ True) → (False ∧ p4)))) → (((p3 → (False → p5)) ∧ ((p2 ∨ True) ∨ (True ∨ p2))) → p4))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h1.left
      let h8 := h1.right
      -- Conjunctions on the left can always be decomposed.
      let h9 := h7.left
      let h10 := h7.right
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- Conjunctions on the left can always be decomposed.
        let h12 := h8.left
        let h13 := h8.right
        -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
        have h14 : (p5 ∨ True) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h13, we can now drive its conclusion.
        let h15 := h13 h14
        -- We need to get the left conjuct of h15 based on <expert-advice>.
        let h16 := h15.left
        -- False on the left can always be used.
        apply False.elim h16
      case inr h17 =>
        -- False on the left can always be used.
        apply False.elim h17
    case inr h18 =>
      -- Conjunctions on the left can always be decomposed.
      let h19 := h1.left
      let h20 := h1.right
      -- Conjunctions on the left can always be decomposed.
      let h21 := h19.left
      let h22 := h19.right
      -- Disjunctions on the left can always be decomposed.
      cases h22
      case inl h23 =>
        -- Conjunctions on the left can always be decomposed.
        let h24 := h20.left
        let h25 := h20.right
        -- We want to use the implication h25 based on <expert-advice>. So we show its premise.
        have h26 : (p5 ∨ True) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h25, we can now drive its conclusion.
        let h27 := h25 h26
        -- We need to get the left conjuct of h27 based on <expert-advice>.
        let h28 := h27.left
        -- False on the left can always be used.
        apply False.elim h28
      case inr h29 =>
        -- False on the left can always be used.
        apply False.elim h29
  case inr h30 =>
    -- Disjunctions on the left can always be decomposed.
    cases h30
    case inl h31 =>
      -- Conjunctions on the left can always be decomposed.
      let h32 := h1.left
      let h33 := h1.right
      -- Conjunctions on the left can always be decomposed.
      let h34 := h32.left
      let h35 := h32.right
      -- Disjunctions on the left can always be decomposed.
      cases h35
      case inl h36 =>
        -- Conjunctions on the left can always be decomposed.
        let h37 := h33.left
        let h38 := h33.right
        -- We want to use the implication h38 based on <expert-advice>. So we show its premise.
        have h39 : (p5 ∨ True) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h38, we can now drive its conclusion.
        let h40 := h38 h39
        -- We need to get the left conjuct of h40 based on <expert-advice>.
        let h41 := h40.left
        -- False on the left can always be used.
        apply False.elim h41
      case inr h42 =>
        -- False on the left can always be used.
        apply False.elim h42
    case inr h43 =>
      -- Conjunctions on the left can always be decomposed.
      let h44 := h1.left
      let h45 := h1.right
      -- Conjunctions on the left can always be decomposed.
      let h46 := h44.left
      let h47 := h44.right
      -- Disjunctions on the left can always be decomposed.
      cases h47
      case inl h48 =>
        -- Conjunctions on the left can always be decomposed.
        let h49 := h45.left
        let h50 := h45.right
        -- We want to use the implication h50 based on <expert-advice>. So we show its premise.
        have h51 : (p5 ∨ True) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h50, we can now drive its conclusion.
        let h52 := h50 h51
        -- We need to get the left conjuct of h52 based on <expert-advice>.
        let h53 := h52.left
        -- False on the left can always be used.
        apply False.elim h53
      case inr h54 =>
        -- False on the left can always be used.
        apply False.elim h54



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341105941878202373127148715902 : (p2 → ((p4 → (((p3 ∨ p2) ∨ False) → (False ∧ (((p1 ∨ (False ∧ ((p5 → False) ∧ False))) ∧ (p2 ∧ ((False ∧ p3) → p1))) ∧ p1)))) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_972231483063541521187584229642 : ((((True ∨ p5) → (((((p1 → (p4 → p1)) ∧ ((p1 → False) ∨ ((False ∧ (p4 ∨ (p5 ∧ (True ∨ p2)))) ∨ True))) ∨ True) ∧ p3) ∧ p2)) → p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (True ∨ p5) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the left conjuct of h3 based on <expert-advice>.
  let h4 := h3.left
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- One of the premise coincides with the conclusion.
  exact h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_18081540147269233162127732118 : (((p1 ∨ (((p5 ∨ (((True ∧ (((p3 ∨ p5) ∧ (p4 ∨ p3)) ∧ p5)) ∨ False) ∧ p3)) ∨ p1) ∨ p4)) ∨ (((p2 ∧ p1) → p2) ∧ True)) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338409652101084354437748837399 : (p1 → (((True → p5) ∧ (p4 ∨ p3)) → ((((p1 ∧ (False ∧ (p3 ∨ p2))) ∨ (((p1 ∨ p5) → p5) ∧ (p3 ∧ p1))) ∨ (p3 ∧ False)) ∨ p5))) := by
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
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h6 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h7 := h3 h6
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h9 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h10 := h3 h9
    -- One of the premise coincides with the conclusion.
    exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_639567689132774208267561899190 : ((((((p4 ∧ True) → False) ∧ (p4 → (((((True → p1) → (True ∨ p5)) ∧ (p4 ∧ False)) → p3) → ((p5 ∧ (p5 ∧ p1)) ∧ p4)))) → False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_682282247333226596623885097080 : (((((((True → False) → p5) ∧ (p1 ∧ ((True ∧ (p1 ∨ p3)) → (p5 → p1)))) ∧ (p5 ∧ True)) ∧ ((p2 ∨ ((False ∨ False) ∧ p5)) ∧ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_316595379443723912844566465392 : (p3 ∨ (p3 ∨ (p5 ∨ (((((False ∧ (((p4 ∨ (p2 ∨ p5)) → (p1 ∧ (p4 ∨ True))) ∧ False)) → p2) → False) ∧ ((True ∧ p3) ∧ p1)) → p5)))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h8 : ((False ∧ (((p4 ∨ (p2 ∨ p5)) → (p1 ∧ (p4 ∨ True))) ∧ False)) → p2) := by
    -- Implications on the right can always be decomposed.
    intro h9
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- False on the left can always be used.
    apply False.elim h10
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h12 := h2 h8
  -- False on the left can always be used.
  apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_339503585492258240490297376997 : (p1 → (False ∨ (((((p3 ∨ (p5 ∧ (p3 → True))) ∧ p3) ∧ p4) ∧ (p4 ∨ False)) ∨ (p4 → ((((True ∨ False) → p4) ∧ False) → (p2 → p4)))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_689296988559051577123542773412 : ((((((((True ∨ (p1 ∧ p4)) ∧ p2) → p3) → (True → (p3 ∧ p4))) ∧ (p2 → p2)) ∨ ((p2 ∨ True) → (((p1 → True) ∨ p2) ∨ p4))) ∨ p1) ∧ True) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h4
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191642796615981646295904870526 : ((p4 ∧ ((False ∧ (False ∨ (p5 → p4))) → (True → p4))) ∨ (p5 ∨ (((p1 ∧ p4) ∨ ((False ∧ ((p4 ∨ True) → (p4 ∧ p2))) ∨ True)) ∨ p3))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111816368437733718574541823476 : ((((p3 ∨ ((((p5 → ((p5 → p4) ∧ p5)) → (p2 ∨ (True ∧ (p3 ∨ (p3 ∧ p5))))) ∨ p1) ∨ p3)) → (True → False)) ∨ p5) ∨ (False → False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_810733722026930120558310378025 : (((p5 → (((p4 → True) → False) → (p3 ∨ (p3 ∨ (((p2 → ((p3 ∧ p4) → ((False → (p2 → p4)) → p1))) → p4) ∨ (p3 → p2)))))) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (p4 → True) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h3
  -- False on the left can always be used.
  apply False.elim h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_663350926209883096461731320320 : (((((p4 → p2) ∨ (True ∧ (p1 ∧ ((((p1 → False) → p4) → True) → ((True ∧ ((p3 ∨ (True ∧ p2)) ∧ p1)) ∧ p5))))) → (p3 → p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119274247398325204703532008347 : ((p3 → (((False ∨ (((p1 ∨ p2) ∨ ((p2 → p2) ∨ p2)) ∧ p5)) ∨ (p2 ∧ (p5 ∧ ((False ∧ (p3 ∧ p1)) ∧ True)))) ∧ p1)) ∨ (False → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158931661830804748934785335902 : ((p2 ∨ ((((p1 ∨ (p4 ∧ (p4 ∧ p3))) → ((p1 → p2) → ((True ∧ False) ∧ p5))) ∨ p1) ∨ True)) ∨ ((p5 → p5) → (True ∨ (p4 ∧ p1)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214570651572523365581793857401 : (((p2 ∨ p1) ∧ (p4 ∨ p5)) ∨ ((((True ∨ (((False ∨ ((False ∨ p5) ∧ False)) ∧ (p3 ∨ p4)) → (p5 ∧ p2))) ∨ (p4 ∨ p3)) → False) → False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((True ∨ (((False ∨ ((False ∨ p5) ∧ False)) ∧ (p3 ∨ p4)) → (p5 ∧ p2))) ∨ (p4 ∨ p3)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309931265901198399831817155344 : (p2 ∨ (((p4 ∧ p3) ∧ (p1 ∨ ((p4 ∧ p1) ∧ (p2 ∧ ((p3 ∨ (p3 ∨ (False ∧ p2))) → True))))) ∨ (p1 → ((True ∨ p2) ∨ (True ∨ p2))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305408851859166975649166411382 : (p1 ∨ ((((False ∨ p4) ∧ (p3 → True)) ∧ (p1 ∨ (False ∨ ((p5 ∧ p1) ∨ (p3 ∨ p4))))) ∨ ((False ∨ p3) ∨ (False → ((p1 ∨ p2) ∧ p1))))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190405554516817450579163103807 : (((p4 ∧ (True → ((True → (p1 ∨ p3)) ∧ p4))) ∨ False) ∨ (((p1 ∧ (True → (((True → p5) ∧ p3) ∨ False))) → p5) ∨ (True ∧ (p2 → True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_138293061281786186944559435702 : ((p3 → ((p5 ∧ (((p5 ∨ p5) → (((True → (p4 → (True ∧ True))) → True) ∨ p1)) → (True ∨ p1))) ∨ (p1 → p5))) ∨ (p4 → (p2 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207607707578545228478481560947 : (((((p1 ∨ True) → False) → p4) → False) → (((True → ((True ∧ p2) ∨ ((False ∨ ((p1 → p2) ∧ p5)) ∨ (p2 ∨ False)))) ∧ True) ∧ (False ∨ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : (((p1 ∨ True) → False) → p4) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h5 : (p1 ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h6 := h4 h5
    -- False on the left can always be used.
    apply False.elim h6
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h7 := h1 h3
  -- False on the left can always be used.
  apply False.elim h7
  -- True on the right can always be proven directly.
  apply True.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h8 : (((p1 ∨ True) → False) → p4) := by
    -- Implications on the right can always be decomposed.
    intro h9
    -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
    have h10 : (p1 ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h9, we can now drive its conclusion.
    let h11 := h9 h10
    -- False on the left can always be used.
    apply False.elim h11
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h12 := h1 h8
  -- False on the left can always be used.
  apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259812052395498148074471462234 : ((p1 → p3) → (((p3 → (p2 ∨ p5)) → (((((((p3 → p1) ∨ p4) ∧ True) ∨ (False ∨ False)) ∨ True) ∨ p3) ∨ p3)) ∨ ((p1 ∨ p3) ∧ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40684907063099533299304129747 : (((((((True ∧ (p4 ∨ p2)) ∧ (p4 ∨ (((False → p5) ∧ p4) ∨ (True ∧ p1)))) → p4) ∧ (((p2 ∧ p5) ∨ p5) ∨ True)) → p2) ∨ True) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_312688002275960376676900595208 : (p3 ∨ (((p4 ∨ ((((p3 → ((((True → ((False → p4) ∨ p3)) ∨ p3) ∨ p5) ∨ False)) → False) ∧ p4) ∨ p4)) ∨ ((p3 ∧ p2) → p3)) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_919198987200731750824359092184 : (((((p4 ∧ ((p4 ∧ False) ∨ (p4 → False))) ∧ ((True → (p5 → p3)) → p3)) ∧ ((((p5 ∨ p1) ∨ p1) ∨ (p4 ∧ (False ∧ p4))) → True)) → p1) ∧ True) := by
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
  let h6 := h4.left
  let h7 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- False on the left can always be used.
    apply False.elim h10
  case inr h11 =>
    -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
    have h12 : p4 := by
      -- One of the premise coincides with the conclusion.
      exact h6
    -- We have shown the premise of h11, we can now drive its conclusion.
    let h13 := h11 h12
    -- False on the left can always be used.
    apply False.elim h13
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_265637330544307998404100890719 : (True ∧ (p2 ∨ ((p5 ∨ ((p4 ∨ ((p3 ∧ p1) ∨ ((p2 ∧ p1) → (True ∧ (p2 ∧ p2))))) ∨ (True ∧ (p2 → (p3 ∧ (True ∨ p3)))))) ∨ p3))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_592816073214605800817400402693 : (((((((False ∨ (((p2 ∨ p5) ∨ p5) ∨ p3)) → ((p1 ∧ p4) ∧ (p4 ∨ p2))) → (False ∧ (p2 ∧ p1))) ∧ (True ∨ (p1 ∨ p4))) ∧ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301178774247742269806980142279 : (False ∨ ((((p2 → (True ∧ p1)) ∨ False) ∨ (False → p3)) → ((((True ∧ (p1 → (p4 ∧ ((p5 → (p2 → False)) ∨ p1)))) ∧ p4) → p5) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
      -- False on the left can always be used.
      apply False.elim h4
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137852225007128623689440757133 : ((p3 ∨ ((True ∧ p4) ∨ ((True ∧ p3) ∧ ((((p5 ∨ p5) → True) → p2) ∧ (p5 ∧ ((False ∨ False) → (False ∨ p1))))))) ∨ (p2 ∨ (True ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260466404703195077342735921547 : ((p3 → False) → (((p5 → False) ∧ (((False ∧ True) ∧ True) ∨ ((p1 → p5) → (((((p3 → p4) ∧ (True → p1)) → p4) ∧ p1) ∨ p5)))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257318884144902756050928205000 : ((p2 ∨ p4) → ((p2 ∨ (((p5 → (False ∧ ((p4 ∨ (p2 ∨ p2)) ∨ p2))) ∧ ((p3 → False) ∧ (p1 → p4))) → (p3 → p2))) ∨ (True ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_672786867841785604480784432984 : (((((p1 → (((False ∨ p2) ∨ (p1 ∨ p5)) ∧ ((p1 → p5) → (p5 ∧ (True ∨ (p4 ∧ p2)))))) → (True → False)) → (p3 ∧ (p4 ∧ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_32577551562732354754978406249 : ((p2 ∨ (((p2 ∧ (((p1 ∨ p2) ∧ False) ∨ p5)) ∧ ((True ∧ p4) → p4)) ∨ ((p2 ∧ p1) → ((True → True) ∨ ((p5 ∨ p3) ∧ p4))))) ∧ True) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39877664118983505632540379062 : (((p2 → (((((((((False ∧ p3) → p4) ∨ p3) ∧ p3) → p3) → p1) → ((p3 → False) ∧ p3)) ∨ (p3 ∨ p4)) → (p4 → p3))) ∧ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190726970591171798536719519337 : ((((p2 ∨ p3) ∧ ((True ∨ True) ∧ p3)) ∧ (p5 → p3)) ∨ (((((((True ∧ p2) ∨ (p5 ∨ p5)) ∨ p1) ∨ p4) → False) ∨ (True ∨ p3)) ∨ False)) := by
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



