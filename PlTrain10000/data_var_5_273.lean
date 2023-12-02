variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52163844285585406666658652562 : ((((p5 ∧ ((((True ∨ p2) ∧ p3) ∨ p1) ∨ p2)) ∧ ((p5 → p1) ∧ (p3 → True))) → (((False → (True ∨ (p2 ∨ p5))) → False) → False)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h11 =>
        -- Conjunctions on the left can always be decomposed.
        let h12 := h4.left
        let h13 := h4.right
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h14 : (False → (True ∨ (p2 ∨ p5))) := by
          -- Implications on the right can always be decomposed.
          intro h15
          -- False on the left can always be used.
          apply False.elim h15
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h16 := h2 h14
        -- False on the left can always be used.
        apply False.elim h16
      case inr h17 =>
        -- Conjunctions on the left can always be decomposed.
        let h18 := h4.left
        let h19 := h4.right
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h20 : (False → (True ∨ (p2 ∨ p5))) := by
          -- Implications on the right can always be decomposed.
          intro h21
          -- False on the left can always be used.
          apply False.elim h21
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h22 := h2 h20
        -- False on the left can always be used.
        apply False.elim h22
    case inr h23 =>
      -- Conjunctions on the left can always be decomposed.
      let h24 := h4.left
      let h25 := h4.right
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h26 : (False → (True ∨ (p2 ∨ p5))) := by
        -- Implications on the right can always be decomposed.
        intro h27
        -- False on the left can always be used.
        apply False.elim h27
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h28 := h2 h26
      -- False on the left can always be used.
      apply False.elim h28
  case inr h29 =>
    -- Conjunctions on the left can always be decomposed.
    let h30 := h4.left
    let h31 := h4.right
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h32 : (False → (True ∨ (p2 ∨ p5))) := by
      -- Implications on the right can always be decomposed.
      intro h33
      -- False on the left can always be used.
      apply False.elim h33
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h34 := h2 h32
    -- False on the left can always be used.
    apply False.elim h34



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_808018007606187653127730780742 : (((p4 → (True ∧ (((p5 → p4) ∧ ((p1 ∨ (p2 → p5)) ∨ ((((False → (p5 ∧ p3)) → (p3 → p5)) ∨ False) ∨ (p2 ∨ p4)))) ∨ p1))) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57700126496044056829489944245 : ((((p1 ∧ p1) → False) → (p2 ∧ (p2 → ((p3 → ((True ∧ p1) ∧ (p5 ∨ ((p5 → ((p5 → False) ∧ (False → p1))) ∧ p3)))) ∨ p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321099807104653098887414069036 : (p4 ∨ (p1 ∨ (p1 → (p1 ∧ ((p2 ∨ p1) → ((p2 → (((((p2 ∧ p1) ∨ (p5 → p2)) → ((p5 ∨ False) → p2)) → p5) ∧ True)) ∨ p1)))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50990817998563644280328163691 : ((((p4 ∨ p1) ∧ (p1 → ((p2 → (p4 ∨ (p2 → True))) ∨ ((p1 ∨ (False → True)) ∨ p3)))) ∧ ((p4 → (p2 → p5)) ∧ (p3 ∨ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174869560818294264205974130731 : (((p1 → False) ∨ (False → (((p1 ∨ p2) ∧ (((p1 → True) ∧ p5) → p2)) → p4))) → (((((p5 ∨ p1) → p3) → p4) → p3) → (p4 → p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h4 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h5 : (((p5 ∨ p1) → p3) → p4) := by
      -- Implications on the right can always be decomposed.
      intro h6
      -- One of the premise coincides with the conclusion.
      exact h3
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h7 := h2 h5
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h8 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h9 : (((p5 ∨ p1) → p3) → p4) := by
      -- Implications on the right can always be decomposed.
      intro h10
      -- One of the premise coincides with the conclusion.
      exact h3
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h11 := h2 h9
    -- One of the premise coincides with the conclusion.
    exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51002356414810530522082555545 : ((((p2 ∧ True) → (((p3 ∨ (p1 ∨ ((p2 ∧ p5) ∧ (p5 ∧ p3)))) ∨ False) → (False → p2))) ∧ ((p2 ∧ ((p4 → p5) → p1)) ∨ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116534881817565930331176293975 : (((True ∨ p4) ∧ ((True ∨ (p3 ∧ (False ∨ p4))) ∧ (((False ∨ p1) ∧ (((p5 ∧ False) ∨ p5) → p5)) → ((p2 ∧ p2) ∨ p3)))) ∨ (p4 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_600601566659678889813592848610 : ((((True ∧ (p5 → ((p3 → (((True ∨ ((((p2 ∨ p3) ∧ (p1 ∧ p2)) → True) → p5)) ∨ p3) ∧ ((p1 ∧ False) ∧ False))) ∨ p1))) ∧ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_209155264208702208174026362728 : ((p3 ∨ ((p2 ∨ p5) → (p4 → p3))) → (((((False → p2) ∧ (p3 ∧ (p1 ∨ ((p2 ∨ (p2 ∧ p4)) ∧ p1)))) → p4) ∨ (p2 → True)) ∨ p5)) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40907801382498848282414931973 : ((((p3 ∧ (((p4 ∨ ((p1 ∧ (p1 ∧ (False → False))) ∧ ((p2 ∨ p2) ∧ ((False ∨ p3) → True)))) → p3) ∧ p4)) ∧ (p4 ∨ True)) ∨ True) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179921624213135211927825518571 : (((((((p4 ∧ (p1 → (True → False))) ∧ False) ∨ p1) ∨ p1) → p3) ∨ p1) → (((p3 ∧ (p4 ∨ (True ∧ p1))) ∨ True) ∨ ((p1 → p2) → False))) := by
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
theorem thm_5_vars_319160405285024388049951693241 : (p4 ∨ (((p2 ∨ (p5 → (((((p1 ∧ (False ∨ p5)) ∨ True) ∨ False) → (p2 ∨ p5)) ∧ p4))) ∨ p3) ∨ ((p5 ∧ (p3 → p2)) → (p5 ∨ p2)))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341093283561853480340497300657 : (p2 → ((p2 → (((p5 → (False ∧ ((p4 ∨ False) → (((p2 ∧ p1) ∨ (p1 → False)) ∨ (p2 ∧ p2))))) → False) ∨ (True ∨ (p1 ∨ p5)))) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65840270299551528319305556692 : ((p4 ∨ ((p3 ∧ (False ∧ p1)) ∧ (p4 ∨ (((p3 → True) ∧ True) → (((p4 → (p1 → (p2 → (False ∧ (p2 ∧ False))))) → p1) ∨ p4))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60223674009112214229606344470 : (((True → p2) → ((((p1 ∧ ((p5 → (p2 ∧ p5)) → (p4 ∧ (p1 → (p4 ∨ p3))))) → p3) → p2) ∨ ((False ∨ False) ∧ (p4 ∨ False)))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260693414735184089843612037233 : ((p3 → p3) → (p4 ∨ (p2 ∨ (((((p1 → False) ∨ p2) → p4) ∨ (p3 ∧ (p3 ∨ p2))) ∨ (p5 ∨ ((p2 → p2) ∨ (False ∧ (p1 ∨ False)))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_677751291219717347021066808284 : (((((p4 ∧ ((p5 ∧ ((p5 ∧ ((((False ∨ False) ∨ p4) ∨ (p2 ∨ True)) ∧ True)) ∨ p3)) → p5)) → p3) ∨ (False → ((p5 ∨ p2) ∧ p4))) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59147813532330906964275075493 : (((False ∨ False) ∨ ((p3 → ((((p1 ∧ ((p3 ∨ p1) ∨ (p1 → (p5 → False)))) ∧ p3) → ((True ∨ (p4 ∧ True)) ∧ p5)) ∧ True)) ∧ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200877317859086535886580640287 : ((False ∨ ((p5 → ((p3 ∨ False) ∨ p1)) ∨ True)) → ((p4 ∨ (p5 ∨ (True → (p3 → ((p2 → False) ∧ p1))))) ∨ (False → (p5 ∧ (p3 → False))))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h5
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- False on the left can always be used.
      apply False.elim h5
      -- Implications on the right can always be decomposed.
      intro h6
      -- False on the left can always be used.
      apply False.elim h5
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- False on the left can always be used.
      apply False.elim h8
      -- Implications on the right can always be decomposed.
      intro h9
      -- False on the left can always be used.
      apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213363029722259681820796970878 : (((p4 ∧ (p1 → p4)) ∧ p5) ∨ ((((True → ((p1 ∨ ((p2 ∧ (p5 ∨ (p3 ∨ True))) ∨ p1)) ∧ False)) ∨ p5) → (p3 ∨ (p3 ∨ True))) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_68598437442738661717601328647 : ((p4 → ((((p2 → ((p1 → p4) ∨ (p2 ∧ True))) → ((((p4 ∧ p3) → p1) → ((p4 ∧ p2) ∧ p2)) ∨ (p1 → p4))) ∧ p4) ∨ p1)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_690728640950763835449793726039 : (((((((p2 ∧ ((p4 ∨ True) ∧ (p4 ∨ (p1 → (p3 ∧ p3))))) ∨ True) ∨ p3) → False) → (((p2 ∧ False) → True) ∧ ((p1 ∧ True) ∨ p4))) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : (((p2 ∧ ((p4 ∨ True) ∧ (p4 ∨ (p1 → (p3 ∧ p3))))) ∨ True) ∨ p3) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- False on the left can always be used.
  apply False.elim h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310152456933667026808199984117 : (p2 ∨ ((((p3 ∨ p5) ∨ (p5 → (p4 ∨ (p3 ∨ p2)))) ∨ (p4 → (p1 → p1))) → ((p2 ∨ ((p3 ∨ p3) → p3)) ∨ ((p5 ∨ p1) ∨ False)))) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h4 =>
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
          -- One of the premise coincides with the conclusion.
          exact h7
      case inr h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h8
    case inr h9 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- One of the premise coincides with the conclusion.
        exact h11
      case inr h12 =>
        -- One of the premise coincides with the conclusion.
        exact h12
  case inr h13 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h14
    -- Disjunctions on the left can always be decomposed.
    cases h14
    case inl h15 =>
      -- One of the premise coincides with the conclusion.
      exact h15
    case inr h16 =>
      -- One of the premise coincides with the conclusion.
      exact h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148037274413286552651274943912 : ((((p4 ∧ p5) ∨ ((((((p5 ∨ True) ∧ p2) → p4) ∧ p1) ∧ p3) ∨ (False ∨ (False → True)))) ∨ (p3 ∨ p2)) ∨ ((p1 ∧ (p1 ∨ p1)) → p4)) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_611728719310778997673922914122 : (((((True → (((p5 ∨ (((p1 ∧ p1) → p3) ∨ (p4 ∧ ((p2 ∧ (False ∧ p1)) → (p3 ∧ p3))))) ∧ False) ∧ (p2 ∧ True))) → p5) ∨ False) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the left conjuct of h3 based on <expert-advice>.
  let h4 := h3.left
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- False on the left can always be used.
  apply False.elim h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112773655600258968150254521247 : (((((((False → p5) ∨ (True ∨ True)) ∨ p3) → False) ∧ ((((False ∨ False) ∨ (False ∧ (False ∧ (False → True)))) ∧ p2) → p5)) → p2) ∨ (p5 → p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (((False → p5) ∨ (True ∨ True)) ∨ p3) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_702928508030315713699423867815 : (((((p4 ∧ (p4 ∨ True)) ∧ (((p3 ∧ True) ∨ p5) → p4)) ∨ (p2 ∨ ((p1 → (((p5 ∨ (p2 ∨ p4)) → True) ∨ (True ∧ p1))) → True))) ∨ p2) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119144334887881935764969352481 : ((p1 → (p1 → (True → (((p5 → False) ∧ p3) ∨ (((p4 ∧ (p4 ∨ False)) → p3) ∨ (p4 → (((True ∨ True) ∨ p2) → False))))))) ∨ (p3 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165425774566016147443322260643 : ((((p3 → (p3 ∨ False)) ∨ (((p2 ∨ (p3 ∨ p2)) ∨ p3) ∨ p5)) → (p3 → (False ∨ p2))) ∨ (((p2 ∧ (p1 ∧ (False ∨ p3))) ∨ True) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310243654915859903569848480929 : (p2 ∨ (((p5 ∨ (p5 → (p3 ∨ p4))) → (((True ∨ True) ∨ p1) ∧ False)) → ((p4 ∧ ((p4 → p3) ∨ p5)) ∨ ((p1 ∨ (True ∨ p2)) → True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234776076295130697532695330749 : ((p5 → (True ∧ p4)) → ((((p4 → (True ∨ p5)) → p5) → ((p5 ∨ p3) ∧ (p2 → (((p1 ∨ p4) → False) ∨ p4)))) ∨ ((False → p3) ∧ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (p4 → (True ∨ p5)) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h5
  -- Implications on the right can always be decomposed.
  intro h6
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h7 : (p4 → (True ∨ p5)) := by
    -- Implications on the right can always be decomposed.
    intro h8
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h9 := h2 h7
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h10 : p5 := by
    -- One of the premise coincides with the conclusion.
    exact h9
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h11 := h1 h10
  -- We need to get the right conjuct of h11 based on <expert-advice>.
  let h12 := h11.right
  -- One of the premise coincides with the conclusion.
  exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_196303146387408312649045229098 : ((p3 ∨ (p4 ∨ ((p3 → p2) ∨ (False → p2)))) ∧ (p4 ∨ ((p2 → p4) ∨ (((p3 → (True ∨ (((p1 ∧ p3) → p5) ∧ p2))) ∨ p2) ∨ True)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42315205527722044814425748723 : (((p2 ∧ ((True ∧ p2) ∨ ((((((False → (p5 → p1)) → p4) ∧ ((False → (p1 ∨ False)) ∧ p2)) → p1) → p5) → (p1 ∨ p2)))) ∨ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199632194195827646278027834321 : (((((p5 ∨ True) ∨ p3) ∨ (p4 ∧ p5)) → p3) → (((((p4 ∧ (p2 → (True → (False ∧ p3)))) ∧ p4) → p5) → (False ∧ (p4 ∧ False))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213056037990526335417453799391 : ((p5 → (p5 ∨ (p5 ∨ False))) ∧ (p4 → (p1 → (((((p3 ∧ (p3 ∧ (p4 ∨ p4))) ∨ p1) ∨ p4) ∧ p3) ∨ ((False ∨ p5) ∨ (p3 ∨ p1)))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135585476066812632527665337515 : ((((((p2 ∨ False) ∨ (((p5 ∧ p1) ∨ p5) → (True → False))) ∧ p5) ∧ (True → p2)) ∨ (p1 ∨ (p1 → (False ∧ True)))) ∨ ((False → p1) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249434065682061178862149619680 : ((p5 ∨ False) ∨ ((p3 ∧ ((p1 → p4) ∧ ((False ∧ False) ∧ (p5 ∧ (p4 ∧ False))))) ∨ ((p5 ∨ ((p5 ∨ (p2 → p2)) ∨ p5)) ∨ (p2 → False)))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43374816086104550331656080093 : ((((((p3 ∨ p5) → (True → ((((((False ∨ False) ∨ p2) → p1) ∧ p4) ∧ p5) ∧ (p1 ∧ p1)))) ∧ ((p3 ∧ True) → p2)) ∨ p2) → p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137736509686810806169507544063 : ((p1 ∨ (True → ((p1 ∧ p5) ∨ ((p5 ∨ (((p4 → p5) ∧ (False ∨ p5)) ∧ False)) ∨ ((False ∨ True) ∨ (p1 ∨ p4)))))) ∨ ((p1 → p2) → p5)) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136064325095603925703584830185 : ((((p1 → ((p2 ∨ p1) ∨ p3)) ∨ (p1 → False)) ∧ (p1 ∧ (p5 ∧ ((p4 → False) ∧ (p2 ∨ ((False ∧ p4) ∧ False)))))) ∨ (p5 → (p5 ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111612626973141899931176572612 : (((((p4 ∧ (p5 ∧ ((p3 → True) ∧ (((((True → p3) ∨ p1) ∧ p4) ∧ p2) ∧ ((p5 ∧ p1) → p4))))) ∨ p1) ∨ p2) ∨ True) ∨ (False ∧ p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_325994966942481207008138314814 : (p5 ∨ (True → ((((False ∧ ((p1 → (p4 ∨ (True ∨ (False ∧ p1)))) ∧ False)) ∨ p5) ∨ ((p3 → p3) ∨ p2)) → ((p1 ∧ (p5 ∨ True)) ∨ True)))) := by
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
      let h5 := h4.left
      let h6 := h4.right
      -- False on the left can always be used.
      apply False.elim h5
    case inr h7 =>
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55595418866991149242414096520 : (((p5 ∨ (((p2 ∨ p4) ∧ p4) ∨ p1)) → (((p2 ∧ (True ∧ p3)) ∧ (((False ∨ False) ∨ p5) ∨ True)) ∨ ((p1 ∧ (True → p1)) ∨ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54893175809655572825348271758 : (((((p5 → p2) ∨ (p1 → p1)) ∨ p5) ∧ ((p3 ∨ p4) → (((p2 ∧ (p3 → ((p2 → False) ∨ False))) ∨ p1) ∧ ((p3 ∧ p3) → p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_141583904907018699663304118022 : ((((p2 → p5) ∧ p3) → (False ∧ ((((((p2 → p5) ∨ p1) ∧ p3) ∧ (p3 ∨ False)) → (p3 ∨ (p4 ∧ False))) ∨ False))) → ((True → p5) → p5)) := by
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
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_781404450551663546960013171216 : (((p2 ∨ (p3 ∧ (((True → (True ∨ ((True → (((True ∧ p4) ∧ False) ∨ (True ∧ p4))) ∧ p5))) → p4) → (((p5 → p3) → False) ∨ False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228627861566436546680747505856 : ((p1 ∨ (p5 → p1)) ∨ ((True → p1) → ((((p4 ∧ p5) → (True ∧ p4)) ∨ ((((True ∨ (p3 ∨ (p1 ∧ p5))) ∨ p5) ∧ p2) ∨ p4)) → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h4 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h5 := h1 h4
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h10 =>
        -- Disjunctions on the left can always be decomposed.
        cases h10
        case inl h11 =>
          -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
          have h12 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h1, we can now drive its conclusion.
          let h13 := h1 h12
          -- One of the premise coincides with the conclusion.
          exact h13
        case inr h14 =>
          -- Disjunctions on the left can always be decomposed.
          cases h14
          case inl h15 =>
            -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
            have h16 : True := by
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h1, we can now drive its conclusion.
            let h17 := h1 h16
            -- One of the premise coincides with the conclusion.
            exact h17
          case inr h18 =>
            -- Conjunctions on the left can always be decomposed.
            let h19 := h18.left
            let h20 := h18.right
            -- One of the premise coincides with the conclusion.
            exact h19
      case inr h21 =>
        -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
        have h22 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h1, we can now drive its conclusion.
        let h23 := h1 h22
        -- One of the premise coincides with the conclusion.
        exact h23
    case inr h24 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h25 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h26 := h1 h25
      -- One of the premise coincides with the conclusion.
      exact h26



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167573188644733588636322670554 : ((((((p5 ∧ p1) → p2) ∧ (p2 ∨ (p4 ∧ p2))) → (p5 ∧ (p1 ∨ True))) ∨ (p1 ∨ False)) → (((((False → p2) → p5) → p3) → p5) ∨ True)) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- False on the left can always be used.
      apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167443988436587373923232752007 : (((p2 ∨ ((False ∨ p3) ∨ (p2 → (((p2 ∧ (p4 ∨ True)) → False) → (p2 ∧ p4))))) → False) → ((p1 ∧ p5) ∨ (p2 ∨ ((p2 ∨ False) ∨ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p2 ∨ ((False ∨ p3) ∨ (p2 → (((p2 ∧ (p4 ∨ True)) → False) → (p2 ∧ p4))))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h3
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h5 : (p2 ∧ (p4 ∨ True)) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h3
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h6 := h4 h5
    -- False on the left can always be used.
    apply False.elim h6
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h7 := h1 h2
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197535833175460539584378732968 : (((((False ∧ True) ∧ True) ∨ p5) ∨ (p2 ∧ p3)) ∨ (True ∧ (False ∨ (True ∨ ((True → (p2 → p3)) → (False → ((True → (p1 → p1)) ∧ p5))))))) := by
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
theorem thm_5_vars_213792490951693258611877279785 : (((p1 ∧ (p1 → True)) ∨ p5) ∨ ((p1 → (p2 → (p2 ∧ p5))) → ((p1 ∧ ((True ∨ p3) → ((True ∧ p2) ∧ (p2 ∧ (False ∧ p4))))) → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h5 : (True ∨ p3) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h6 := h4 h5
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- One of the premise coincides with the conclusion.
  exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42174769221449998746490227056 : (((True ∧ (((p2 ∧ ((((((((True ∨ p5) → p4) ∧ True) → True) ∧ p4) → True) ∨ False) ∧ ((p2 ∨ p1) ∧ p1))) ∧ False) ∨ p1)) ∨ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_602756664193015335295602392096 : ((((False ∨ (p5 ∧ (p5 ∧ ((p5 ∨ ((True ∨ (p4 → ((p2 ∧ p3) ∨ (p4 → p2)))) ∨ (p5 ∨ (p3 ∨ p4)))) ∧ (p5 → p3))))) ∧ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_747560392762012160239841135147 : ((((True → p3) → ((((p5 ∧ False) ∨ (((p5 → ((p5 ∧ p5) ∧ p2)) ∨ (p1 ∨ ((p2 ∧ p4) ∧ (p3 → p5)))) ∨ True)) → False) → False)) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : ((p5 ∧ False) ∨ (((p5 → ((p5 ∧ p5) ∧ p2)) ∨ (p1 ∨ ((p2 ∧ p4) ∧ (p3 → p5)))) ∨ True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- False on the left can always be used.
  apply False.elim h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217593457955374048331738662820 : ((((p5 ∨ p5) ∨ p2) → p2) → ((p2 → (((p2 → ((p5 ∨ p2) → ((p5 ∧ p2) ∧ (False ∨ ((p3 ∧ p2) ∨ p5))))) ∨ p1) ∨ p3)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_344607937690737364768127513965 : (p2 → (p1 → (((((p5 ∨ True) ∨ ((False ∧ ((False ∨ False) → False)) ∨ p4)) → (p4 ∧ p4)) ∨ (p4 ∧ p1)) ∨ ((p3 ∨ (True ∧ p5)) ∨ True)))) := by
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
theorem thm_5_vars_49318502835897856266369140230 : (((p3 ∨ (((p2 ∨ ((False → p2) ∨ (p3 ∧ (True ∧ (p3 ∨ p5))))) → (p2 ∧ (p1 ∧ True))) ∨ (False → p1))) ∨ (True → (False → False))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39215401645968843143100972335 : (((True ∧ (((p3 ∨ p4) ∧ ((True ∧ (p2 ∨ p1)) ∨ p1)) ∧ (p2 → (False → ((p4 ∨ (p2 ∨ ((p1 ∧ p3) → p1))) ∧ p3))))) ∧ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_316681386590165917108835934006 : (p3 ∨ (p5 ∨ ((((((p4 ∧ False) → p5) ∨ (p2 ∧ p4)) → (p4 ∧ (((True ∨ p1) → False) ∨ False))) ∧ ((p5 ∨ p2) ∧ p4)) ∨ (p3 ∨ True)))) := by
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
theorem thm_5_vars_113502489012018203906549516307 : (((((False ∨ ((p4 ∨ True) ∨ (((p5 ∧ p2) ∧ False) ∨ (p1 → p3)))) ∨ p4) ∧ (((p5 ∨ p2) ∨ p5) ∧ p4)) ∨ (p4 ∧ p1)) ∨ (False ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118296456112364883251989100527 : ((p1 ∨ (p2 ∧ ((((p5 → (p4 ∧ ((True → (p3 ∧ (p4 ∨ p2))) ∨ p5))) ∧ (p4 ∨ p2)) → True) → (p2 ∧ (True → p5))))) ∨ (False → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190361532054402512940941315224 : ((((p1 ∨ p5) ∧ (((True ∧ p2) → True) ∨ p5)) ∨ False) ∨ ((p2 ∧ (p3 ∧ (((p3 ∧ p4) ∧ p2) ∨ p1))) ∨ (((p5 → p3) → True) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_76630124461279157026740068187 : (((((p2 → False) ∧ ((p2 ∧ p4) ∧ (p2 ∧ (p3 → (p3 ∨ (((p4 ∧ p1) ∨ p1) ∨ p3)))))) → (p4 → (p4 ∧ (p5 ∧ False)))) → False) → p5) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p2 → False) ∧ ((p2 ∧ p4) ∧ (p2 ∧ (p3 → (p3 ∨ (((p4 ∧ p1) ∨ p1) ∨ p3)))))) → (p4 → (p4 ∧ (p5 ∧ False)))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the left can always be decomposed.
    let h5 := h3.left
    let h6 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h7.left
    let h10 := h7.right
    -- Conjunctions on the left can always be decomposed.
    let h11 := h8.left
    let h12 := h8.right
    -- One of the premise coincides with the conclusion.
    exact h10
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the left can always be decomposed.
    let h13 := h3.left
    let h14 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h15 := h14.left
    let h16 := h14.right
    -- Conjunctions on the left can always be decomposed.
    let h17 := h15.left
    let h18 := h15.right
    -- Conjunctions on the left can always be decomposed.
    let h19 := h16.left
    let h20 := h16.right
    -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
    have h21 : p2 := by
      -- One of the premise coincides with the conclusion.
      exact h19
    -- We have shown the premise of h13, we can now drive its conclusion.
    let h22 := h13 h21
    -- False on the left can always be used.
    apply False.elim h22
    -- Conjunctions on the left can always be decomposed.
    let h23 := h3.left
    let h24 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h25 := h24.left
    let h26 := h24.right
    -- Conjunctions on the left can always be decomposed.
    let h27 := h25.left
    let h28 := h25.right
    -- Conjunctions on the left can always be decomposed.
    let h29 := h26.left
    let h30 := h26.right
    -- We want to use the implication h23 based on <expert-advice>. So we show its premise.
    have h31 : p2 := by
      -- One of the premise coincides with the conclusion.
      exact h29
    -- We have shown the premise of h23, we can now drive its conclusion.
    let h32 := h23 h31
    -- False on the left can always be used.
    apply False.elim h32
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h33 := h1 h2
  -- False on the left can always be used.
  apply False.elim h33



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118841733678291785823706963925 : ((True → ((((p5 ∧ p4) → True) ∧ ((((True → (True → p2)) ∧ ((True → False) → p4)) → False) ∧ False)) ∨ ((True ∨ False) ∨ False))) ∨ (False ∧ p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159987647297904437672811400928 : (((((p4 → (p2 ∨ (p3 → (True ∨ p4)))) → p2) ∨ (((True → p1) → p2) → (True → True))) → False) → (p1 ∧ (((True → p1) ∧ p2) → p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p4 → (p2 ∨ (p3 → (True ∨ p4)))) → p2) ∨ (((True → p1) → p2) → (True → True))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h2
  -- False on the left can always be used.
  apply False.elim h5
  -- Implications on the right can always be decomposed.
  intro h6
  -- Conjunctions on the left can always be decomposed.
  let h7 := h6.left
  let h8 := h6.right
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h9 : (((p4 → (p2 ∨ (p3 → (True ∨ p4)))) → p2) ∨ (((True → p1) → p2) → (True → True))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h10
    -- Implications on the right can always be decomposed.
    intro h11
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h12 := h1 h9
  -- False on the left can always be used.
  apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_972014505653202643807059087546 : ((((True ∨ True) → (((p1 ∨ (((False ∨ p3) ∨ False) → (p1 ∧ p2))) ∧ False) ∧ (((False ∧ p3) ∧ (False ∧ (p5 ∨ p2))) ∨ (p4 ∨ p2)))) → p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (True ∨ True) := by
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
  -- False on the left can always be used.
  apply False.elim h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305815716212767981183169091809 : (p1 ∨ ((p1 ∨ ((True → ((p2 ∨ p5) ∨ p1)) ∧ False)) → ((p3 ∨ (p3 → p3)) → (((p1 ∨ True) → (((False ∧ p2) ∧ p5) ∨ True)) ∨ True)))) := by
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
    cases h1
    case inl h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- False on the left can always be used.
      apply False.elim h7
  case inr h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- False on the left can always be used.
      apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227551660317760053613226257600 : ((True ∧ (p2 → p5)) ∨ (p5 → (((((p4 ∧ ((False ∨ ((p3 ∧ p3) ∨ p2)) ∨ True)) ∧ p5) ∨ p5) ∧ ((p1 → p1) ∨ False)) ∨ (p4 ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_601175909330112300465295756070 : ((((p2 ∧ ((p4 ∧ (((p3 ∧ ((True ∧ p5) → p5)) ∧ (p5 ∨ (p2 → ((p3 → (True → True)) ∨ p4)))) ∧ (p2 ∧ False))) ∧ p2)) ∧ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115226802179901598332052962314 : (((((p1 ∨ p5) → (p4 ∧ (p5 → (p1 ∨ p2)))) ∧ p5) ∨ (p1 ∨ (((p5 ∨ (False → ((p5 ∧ p5) ∨ p3))) ∧ False) ∧ p2))) ∨ (p5 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_602252246513500564450951164172 : ((((p5 ∧ (p4 → ((p5 → ((((p1 ∧ p3) ∨ p5) ∨ (p2 ∧ p5)) ∨ p5)) → ((p5 ∨ False) ∧ (p3 ∧ ((p5 → p4) → False)))))) ∧ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135002964507135487116094624247 : (((p5 ∧ ((((p3 → ((p5 ∨ p3) ∨ ((p2 → ((p4 ∧ p3) → True)) ∧ p5))) → False) ∨ p3) ∨ True)) ∧ (p4 → p2)) ∨ ((True ∨ p2) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_723897404702445187169540755296 : ((((True ∧ (p1 ∨ True)) ∧ (((False ∨ ((((p3 ∨ p4) → True) ∨ p1) → p5)) → ((p5 → p2) ∨ (p1 ∧ (True ∧ p5)))) ∨ (False → p3))) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_149512048335008822421225816553 : ((p1 ∧ ((True → (p3 → (p2 ∨ p5))) → (((((False ∧ True) ∧ p5) ∨ True) ∧ p4) → ((True ∧ p1) ∨ False)))) ∨ (True ∨ (True ∧ (p1 ∧ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_608465827194753481580904704511 : ((((((((p2 ∧ (((p3 ∧ ((p4 ∧ ((p4 → p4) ∨ p5)) ∨ p4)) ∨ p3) ∧ (p1 ∨ p4))) → False) → (p5 ∧ True)) → p4) ∨ False) ∨ True) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_786369676475545903797730737784 : (((p4 ∨ (((p5 ∧ ((((((p3 → p3) → p3) → False) ∨ (p1 ∧ True)) ∨ p1) ∧ p3)) ∨ p3) → ((p5 ∨ p2) ∧ ((p4 ∨ False) ∨ p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_22892352175471906191672614608 : ((((p4 ∧ p3) ∨ ((p1 ∧ p2) ∧ p5)) ∨ ((((False → p4) → ((True ∧ p1) ∧ (True → True))) → p4) ∨ ((p4 → (p4 ∨ True)) ∨ True))) ∧ True) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324381052175045439804246540946 : (p5 ∨ ((False ∨ (p4 ∨ ((False → False) ∧ p2))) ∨ ((p2 ∨ False) ∨ ((p5 ∨ ((((p3 ∨ True) → p1) ∨ (p4 → (p4 ∧ p1))) → True)) ∨ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_19573454073936890799238856422 : (((((False ∨ (False ∧ ((p4 → False) ∧ True))) ∨ p4) ∧ ((p5 → (False → p1)) ∧ True)) ∨ (p4 → (p5 → ((p1 ∧ (p1 → p2)) → p1)))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- One of the premise coincides with the conclusion.
  exact h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_720711899508473905847858738989 : ((((((p3 → p2) → p5) → True) → (p5 ∨ (((False → ((((p4 ∧ p1) ∧ (p3 ∧ (True ∧ p1))) ∨ p2) ∧ p5)) ∧ p3) ∧ (p1 → p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_802257211486848612329958153037 : (((p2 → (p4 ∧ (((((p4 ∨ (True ∨ (True ∨ ((p5 ∨ (True ∧ True)) ∧ p5)))) ∧ ((p4 ∧ False) ∨ (p1 ∨ p3))) ∧ p3) ∧ False) ∧ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_725023812557194518040038071895 : ((((False → (True ∧ p3)) ∧ (((p4 ∧ (p3 → p4)) ∧ p2) → (((p5 ∧ True) ∧ ((((True ∨ p4) → p4) ∨ (p5 → p3)) ∧ False)) ∨ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_813084908554399402501958822654 : ((((((True → False) ∧ (p3 → ((p2 → (p3 ∨ (p1 → ((((p4 → p3) → (True ∧ p3)) → (p4 ∨ p3)) → p1)))) ∧ p4))) ∧ p1) ∧ p4) → False) ∧ True) := by
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
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h8 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h9 := h6 h8
  -- False on the left can always be used.
  apply False.elim h9
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148036587487077934318509165043 : ((((True ∧ p2) ∨ (((p4 ∨ ((p5 → (p5 → True)) ∧ (True ∨ p3))) ∧ False) ∨ (p3 ∧ p1))) ∨ (p1 ∧ p2)) ∨ (p2 → ((p3 ∧ p4) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115479920538674269380730879255 : (((p3 → (True → (p4 ∧ ((p1 ∧ False) ∨ p2)))) ∨ (False ∨ ((((p2 ∨ (p3 ∨ (p5 → p3))) ∧ p1) → p5) ∧ (p2 ∧ p5)))) ∨ (False → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_737137586590965407596529427192 : ((((p3 → p4) ∧ ((((((p4 → (p2 → p5)) ∧ ((p2 ∨ (p4 → p3)) ∨ False)) ∨ p5) ∨ True) ∧ True) ∨ (p5 → (p5 → (True → p5))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57354933613092352473936028434 : (((p3 ∧ (p1 ∨ p2)) ∨ ((p2 → p2) ∧ ((p1 → ((True ∧ False) → p4)) → ((p2 → (True ∨ ((False ∧ (p3 ∨ p1)) ∨ p3))) ∧ p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_599629059494127620986189954289 : (((((True → p4) ∨ ((((True ∨ p5) ∨ (False ∨ p2)) → ((p5 ∨ p5) ∨ (p3 ∨ False))) → ((p2 ∧ (p1 → (p2 ∧ p1))) ∧ p1))) ∧ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_264651363324740231909445807988 : (True ∧ ((p4 ∨ (p4 ∧ p4)) → (p1 ∨ ((False ∧ (False ∧ False)) ∨ ((p2 ∨ ((((False → (False ∨ (False ∨ p4))) ∨ p1) ∧ True) ∨ p4)) ∨ p3))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
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
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
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
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230626694121429344251359104801 : (((p2 → p3) ∧ p4) → (p4 → (((((p1 ∨ p4) ∧ p2) ∧ ((False ∨ p4) ∧ p1)) ∨ p5) ∨ (p2 ∨ ((p2 ∧ ((p2 → p4) ∨ p4)) → p3))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h5
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h9 : p2 := by
      -- One of the premise coincides with the conclusion.
      exact h6
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h10 := h3 h9
    -- One of the premise coincides with the conclusion.
    exact h10
  case inr h11 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h12 : p2 := by
      -- One of the premise coincides with the conclusion.
      exact h6
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h13 := h3 h12
    -- One of the premise coincides with the conclusion.
    exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45839038995297260637558124400 : (((p2 → ((p2 ∧ ((p4 ∨ p4) ∨ False)) → ((((p3 → (((p3 ∧ p4) → p1) ∨ p4)) ∧ False) → (p4 ∨ p1)) ∨ (True ∧ False)))) → p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187385674815926375708427984699 : ((p4 ∧ ((p3 ∧ ((True → True) ∨ (p2 ∧ (p1 → p1)))) ∧ p2)) → (((p2 ∧ (p5 ∨ (p5 → ((p4 ∨ p2) ∧ (False ∨ p2))))) → p5) → p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h9 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h10 : (p2 ∧ (p5 ∨ (p5 → ((p4 ∨ p2) ∧ (False ∨ p2))))) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h6
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h11
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h3
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h6
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h12 := h2 h10
    -- One of the premise coincides with the conclusion.
    exact h12
  case inr h13 =>
    -- Conjunctions on the left can always be decomposed.
    let h14 := h13.left
    let h15 := h13.right
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h16 : (p2 ∧ (p5 ∨ (p5 → ((p4 ∨ p2) ∧ (False ∨ p2))))) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h6
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h17
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h3
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h6
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h18 := h2 h16
    -- One of the premise coincides with the conclusion.
    exact h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156948783468768424245997408972 : (((((p3 ∨ True) → (p4 ∨ (((((False ∨ p2) ∨ p1) → True) ∨ True) ∧ p4))) → (False ∧ p2)) ∨ p3) ∨ (p3 → (p1 → ((True → p3) ∧ True)))) := by
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
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_715417167231865755337396539572 : ((((((p1 → p5) ∧ p3) ∧ p5) ∧ (p1 → ((p4 ∨ p4) ∧ ((((False ∧ p5) → (True ∧ p2)) → p3) ∧ ((p3 → p5) → (p1 → True)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_750343737242875691475379288 : ((((p1 ∧ p1) → p2) ∨ (((((True → (p2 → p2)) ∧ (p5 → p5)) → (True ∧ ((p3 ∧ (False → p4)) → p5))) ∨ p2) ∨ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115982408174593354740741819914 : ((((p1 ∧ (p2 ∧ p3)) ∨ True) → ((((((False ∨ (p4 ∨ p3)) ∧ True) ∨ True) ∧ p4) ∨ p1) ∧ (p5 → ((p3 → p1) → p1)))) ∨ (p1 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205952356126517647868410634672 : ((False ∧ (p3 ∨ ((False ∨ p2) ∨ False))) ∨ (True ∨ (((p4 ∨ ((p5 ∧ (p4 → (True ∧ (True → p1)))) ∧ (p2 ∧ False))) ∧ (True ∧ False)) → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_628770152607077964485988526359 : (((((p1 → (p2 → ((p1 ∧ (((p5 → False) ∨ (p2 ∨ True)) ∧ p4)) ∨ ((p4 ∨ (p4 ∧ p1)) → (True ∨ (False → p3)))))) ∧ p3) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_668216736824995377040651816991 : ((((p2 → (((True ∨ False) → (((p2 ∨ True) → (False → (p1 ∨ (p2 ∨ p3)))) ∧ p2)) ∧ ((p5 ∨ p3) → False))) ∧ (p5 ∨ (p5 ∨ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



