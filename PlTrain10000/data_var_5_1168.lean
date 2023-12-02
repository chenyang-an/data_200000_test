variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231086744089607262988268501558 : (((False ∨ p1) ∨ p3) → ((False ∨ p2) ∨ (((p4 ∨ p5) ∧ (((p1 ∧ True) ∨ p4) → p5)) → (p5 ∨ ((p5 → p2) ∨ (p5 ∧ (True → p4))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h3 =>
      -- False on the left can always be used.
      apply False.elim h3
    case inr h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h5
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h8 =>
        -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
        have h9 : ((p1 ∧ True) ∨ p4) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h8
        -- We have shown the premise of h7, we can now drive its conclusion.
        let h10 := h7 h9
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h10
      case inr h11 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h11
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
      -- We want to use the implication h15 based on <expert-advice>. So we show its premise.
      have h17 : ((p1 ∧ True) ∨ p4) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h16
      -- We have shown the premise of h15, we can now drive its conclusion.
      let h18 := h15 h17
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h18
    case inr h19 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148194526432243714822026766614 : ((((p3 ∨ (p2 ∧ p2)) ∨ ((p2 → (p5 → p2)) → ((p3 ∧ (p5 ∨ True)) ∧ p3))) ∧ ((p1 ∧ p1) ∨ False)) ∨ ((p3 → (True ∨ p3)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185065251058294509746167819262 : (((p3 ∧ False) ∨ (((p4 → (p5 → p3)) → p4) ∨ (p3 ∨ True))) ∨ ((p5 ∧ ((True → (p5 ∧ (p1 ∧ p3))) ∧ p2)) → ((p5 ∨ p3) ∨ p4))) := by
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
theorem thm_5_vars_775616269002924698492441876872 : (((False ∨ (False ∨ (((p5 ∨ p2) ∧ (False ∧ p2)) ∨ ((p4 ∨ (True ∨ (False ∨ p3))) ∧ (False ∨ ((p1 ∧ (p2 ∧ (False ∨ False))) ∨ p2)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156841316250146861551566684513 : (((p2 → (False ∧ (p5 ∧ (((p5 ∧ p5) → (p4 ∧ ((p3 ∨ p4) ∧ p4))) ∨ (p5 → p1))))) ∧ p5) ∨ (True ∨ (((True ∧ p4) ∧ p3) → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54433715432455081870625876293 : ((((p1 ∧ (p2 ∨ ((p4 → p2) ∧ False))) ∨ p5) ∨ (((p5 ∧ (((True → False) ∨ False) ∧ False)) ∧ False) ∨ ((p2 ∨ p4) → (p1 ∧ p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_792493742208876266517364775376 : (((True → ((((p5 ∧ ((True ∧ p1) ∧ p3)) ∨ (True → p2)) ∧ False) ∨ (((p2 ∧ p4) ∨ ((True → ((False ∧ p5) ∧ p5)) ∨ True)) ∨ p3))) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_788500765072325227300762150963 : (((p5 ∨ ((p4 ∧ ((p3 ∧ (((p4 ∨ (((p2 ∧ (((p5 → p1) → (p1 ∧ True)) → p5)) → p1) ∨ False)) ∧ p3) ∧ True)) ∧ p1)) ∨ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256802929735790221229045123387 : ((p1 ∨ p2) → (False ∨ ((((p3 ∨ True) ∧ (p4 → False)) → (((((p3 ∧ p2) → True) ∧ p5) ∧ p1) → (p2 ∨ (False ∨ (True → p1))))) ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h3.left
    let h10 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h12
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h13 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h14
      -- One of the premise coincides with the conclusion.
      exact h6
  case inr h15 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_653876623498495811529893723911 : (((((((p2 ∨ (p3 ∨ False)) → p5) → (((((p3 ∧ p4) → (True → (False ∨ p5))) ∨ p3) ∨ p5) → (p2 → p1))) ∧ False) ∨ (p1 → True)) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_117192755789979685259481426805 : ((True ∧ (((True ∧ ((((p4 ∨ p2) ∨ (p4 → p3)) → p4) ∧ (False ∨ p2))) ∧ (p1 → p3)) ∨ (((p1 ∧ p4) → True) ∨ True))) ∨ (p1 ∨ p2)) := by
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
theorem thm_5_vars_62299039502808532855820374027 : ((p3 ∧ ((((p2 → ((p2 → ((p1 ∨ p2) → p5)) ∧ False)) → (((p5 ∨ (False ∧ (p5 ∨ p1))) → p1) ∨ p3)) ∧ p3) ∧ (p2 ∧ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119964091783892371438472298925 : ((((p2 ∧ (((((p4 ∧ (p3 ∨ p3)) ∧ p1) ∨ (p5 → p5)) → (p2 ∧ False)) ∧ p4)) ∧ ((p1 ∨ p1) ∨ (p3 → True))) ∧ True) → (False ∨ p3)) := by
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
  let h8 := h7.left
  let h9 := h7.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
      have h12 : (((p4 ∧ (p3 ∨ p3)) ∧ p1) ∨ (p5 → p5)) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h13
        -- One of the premise coincides with the conclusion.
        exact h13
      -- We have shown the premise of h8, we can now drive its conclusion.
      let h14 := h8 h12
      -- We need to get the right conjuct of h14 based on <expert-advice>.
      let h15 := h14.right
      -- False on the left can always be used.
      apply False.elim h15
    case inr h16 =>
      -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
      have h17 : (((p4 ∧ (p3 ∨ p3)) ∧ p1) ∨ (p5 → p5)) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h18
        -- One of the premise coincides with the conclusion.
        exact h18
      -- We have shown the premise of h8, we can now drive its conclusion.
      let h19 := h8 h17
      -- We need to get the right conjuct of h19 based on <expert-advice>.
      let h20 := h19.right
      -- False on the left can always be used.
      apply False.elim h20
  case inr h21 =>
    -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
    have h22 : (((p4 ∧ (p3 ∨ p3)) ∧ p1) ∨ (p5 → p5)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h23
      -- One of the premise coincides with the conclusion.
      exact h23
    -- We have shown the premise of h8, we can now drive its conclusion.
    let h24 := h8 h22
    -- We need to get the right conjuct of h24 based on <expert-advice>.
    let h25 := h24.right
    -- False on the left can always be used.
    apply False.elim h25



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263082015524552999398535170094 : (True ∧ (((((p4 ∧ (True → p2)) ∨ (p5 ∧ p4)) ∨ (((p5 → p4) ∧ (p5 ∧ p2)) ∨ ((p2 ∨ p4) ∨ (p4 → p4)))) ∨ p1) ∨ (True ∨ p2))) := by
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
theorem thm_5_vars_308528916781050578354142128833 : (p2 ∨ ((((((p4 ∨ (p2 ∧ p4)) → p1) → (True ∨ p2)) ∨ (False ∨ (p4 ∧ p3))) → (((((p2 → p3) ∧ p1) ∧ p3) ∨ True) ∨ p2)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177780846934480207603148083368 : (((p3 ∧ (p1 ∨ (p4 ∧ (p4 → ((p5 ∧ (p4 ∨ p2)) → False))))) ∧ p1) ∨ (((True ∧ True) ∧ (p4 → p4)) ∧ (p4 ∨ ((False → p1) ∨ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_593767521096021714835615804260 : (((((False ∧ (p3 ∨ (True ∧ ((p5 → ((False ∨ True) ∧ (False ∧ True))) ∧ (p2 → (p2 ∨ p2)))))) ∧ ((False ∧ (False ∨ True)) ∨ p5)) ∧ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172214918838102978223446788514 : ((((p5 ∨ p5) → (p4 → ((p4 → (True ∧ p3)) ∨ False))) → (False ∨ (p2 ∧ p5))) ∨ (((p2 ∨ p3) ∨ True) → ((False → (p1 ∧ p5)) ∨ p2))) := by
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
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h4 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h5
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- False on the left can always be used.
      apply False.elim h5
      -- False on the left can always be used.
      apply False.elim h5
  case inr h6 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h7
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- False on the left can always be used.
    apply False.elim h7
    -- False on the left can always be used.
    apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_801745224820183742015792704697 : (((p2 → (((p2 ∨ True) ∧ p4) ∨ ((p1 ∧ (((True ∧ (p3 → (p3 ∧ ((p4 → p2) → p1)))) ∨ (p5 ∧ (p1 → p4))) ∨ p3)) ∧ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_802101989748917754845804006767 : (((p2 → (False ∧ ((((p5 ∨ p1) ∨ p1) ∨ (False ∧ ((((p4 ∨ (p4 ∨ p3)) ∧ (p5 ∧ p2)) → p4) → (p3 ∨ (p5 ∧ p3))))) ∧ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60060759435976002805550514702 : (((p2 ∨ p1) → ((False → (p3 → ((p4 ∧ ((((False → False) ∧ p3) ∧ p5) ∧ p4)) ∨ True))) ∧ ((p5 ∧ (True → p2)) ∨ (False ∨ True)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116078884427063303152278349579 : ((((True ∧ p2) ∨ p4) ∧ ((p4 ∧ (p3 → p2)) ∨ (False ∧ ((True ∧ (p3 ∧ True)) → ((p4 → (True → p3)) ∧ (p4 ∧ p5)))))) ∨ (False → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_631032767414846320740790416556 : (((((((p1 → (((p4 ∨ (((p3 → True) ∧ p5) ∧ (p3 ∧ ((p4 ∧ p5) ∨ p3)))) ∧ True) ∨ (p2 ∧ p5))) → p1) ∨ p3) → True) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117490011704596233530521458814 : ((p1 ∧ (p1 → ((((((p3 ∨ p5) ∧ ((p3 ∧ ((p1 ∧ False) ∨ p5)) → True)) ∨ (p5 ∧ (p2 ∧ p2))) ∨ p3) ∨ p1) → False))) ∨ (False → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60449344176079613765550608887 : (((p5 → False) → (((p2 → p5) ∨ ((p5 → p5) → False)) ∨ ((p3 ∧ (p3 ∧ ((p2 ∧ p4) → p1))) ∨ (((p2 → p1) → False) → False)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_8418586602623694159575694817 : ((((p1 ∧ ((True → (((p5 ∨ True) ∨ ((True ∨ p2) ∨ p1)) ∨ ((p5 ∧ False) → (p4 ∨ True)))) ∨ (p2 → (p3 → False)))) → p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_601973420339231235217118090636 : ((((p4 ∧ (p3 → ((False → (p2 ∨ p1)) ∧ (((False ∧ (p4 ∨ p2)) → p1) → (((p5 → (p1 ∧ p3)) → False) ∨ (True ∧ p5)))))) ∧ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147874574721360550946622172330 : (((p4 → (((p3 ∨ ((p2 ∧ p3) → (p2 ∨ p1))) → (p3 ∧ ((p3 ∧ p2) ∨ p1))) ∨ (p2 ∨ p5))) → p1) ∨ (p5 ∨ (p5 → (True ∨ p1)))) := by
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
theorem thm_5_vars_143044369350655468913907206874 : ((False → ((False → ((((p3 → p3) ∧ ((True → p4) ∨ p1)) ∨ False) ∧ ((p4 ∨ p1) → (False ∧ (p5 ∨ False))))) ∨ p4)) → ((p2 → p5) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_209534374497195556987311364303 : ((p4 → (p3 ∧ ((True ∧ p2) → True))) → ((p3 → ((((p2 → (p2 → (p5 ∧ ((p1 ∧ False) ∨ p2)))) ∨ p1) ∧ p2) ∨ p3)) ∨ (p4 → p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158518101340598911667196885308 : (((p3 ∨ True) → (False ∨ (((((False → p3) ∨ p3) → p1) ∧ (p1 → (p5 → p5))) ∨ (p4 → p3)))) ∨ (((p5 ∧ p4) ∨ p4) → (p4 ∨ p3))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111113701634682026000747559446 : (((((p1 → (p4 ∧ (p4 → (True ∧ (p4 ∧ p5))))) ∨ p1) → ((p1 → (p3 → False)) ∧ ((p3 → (True ∧ True)) → p1))) ∧ False) ∨ (p3 → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181468682991931729019323106218 : ((p4 ∨ ((p5 → (p1 ∧ ((p1 ∨ p3) → (p5 ∨ True)))) → (p5 ∨ p3))) → ((p2 ∨ p5) ∨ ((p2 → p4) ∨ (p3 → (p5 → (p5 ∨ p4)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Implications on the right can always be decomposed.
    intro h6
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_209075518558599656901993729310 : ((p1 ∨ (p5 ∨ (p1 ∨ (p5 ∧ p3)))) → (((False ∨ p5) ∧ (p5 ∨ ((False ∨ (True ∨ ((False → p5) → p1))) ∨ (p2 ∨ True)))) → (p1 ∨ True))) := by
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
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h8 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h8
      case inr h9 =>
        -- Disjunctions on the left can always be decomposed.
        cases h9
        case inl h10 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h11 =>
          -- Disjunctions on the left can always be decomposed.
          cases h11
          case inl h12 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h12
          case inr h13 =>
            -- Conjunctions on the left can always be decomposed.
            let h14 := h13.left
            let h15 := h13.right
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
    case inr h16 =>
      -- Disjunctions on the left can always be decomposed.
      cases h16
      case inl h17 =>
        -- Disjunctions on the left can always be decomposed.
        cases h17
        case inl h18 =>
          -- False on the left can always be used.
          apply False.elim h18
        case inr h19 =>
          -- Disjunctions on the left can always be decomposed.
          cases h19
          case inl h20 =>
            -- Disjunctions on the left can always be decomposed.
            cases h1
            case inl h21 =>
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- One of the premise coincides with the conclusion.
              exact h21
            case inr h22 =>
              -- Disjunctions on the left can always be decomposed.
              cases h22
              case inl h23 =>
                -- Show the right disjunct based on <expert-advice>.
                apply Or.inr
                -- True on the right can always be proven directly.
                apply True.intro
              case inr h24 =>
                -- Disjunctions on the left can always be decomposed.
                cases h24
                case inl h25 =>
                  -- Show the left disjunct based on <expert-advice>.
                  apply Or.inl
                  -- One of the premise coincides with the conclusion.
                  exact h25
                case inr h26 =>
                  -- Conjunctions on the left can always be decomposed.
                  let h27 := h26.left
                  let h28 := h26.right
                  -- Show the right disjunct based on <expert-advice>.
                  apply Or.inr
                  -- True on the right can always be proven directly.
                  apply True.intro
          case inr h29 =>
            -- Disjunctions on the left can always be decomposed.
            cases h1
            case inl h30 =>
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- One of the premise coincides with the conclusion.
              exact h30
            case inr h31 =>
              -- Disjunctions on the left can always be decomposed.
              cases h31
              case inl h32 =>
                -- Show the right disjunct based on <expert-advice>.
                apply Or.inr
                -- True on the right can always be proven directly.
                apply True.intro
              case inr h33 =>
                -- Disjunctions on the left can always be decomposed.
                cases h33
                case inl h34 =>
                  -- Show the left disjunct based on <expert-advice>.
                  apply Or.inl
                  -- One of the premise coincides with the conclusion.
                  exact h34
                case inr h35 =>
                  -- Conjunctions on the left can always be decomposed.
                  let h36 := h35.left
                  let h37 := h35.right
                  -- Show the right disjunct based on <expert-advice>.
                  apply Or.inr
                  -- True on the right can always be proven directly.
                  apply True.intro
      case inr h38 =>
        -- Disjunctions on the left can always be decomposed.
        cases h38
        case inl h39 =>
          -- Disjunctions on the left can always be decomposed.
          cases h1
          case inl h40 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h40
          case inr h41 =>
            -- Disjunctions on the left can always be decomposed.
            cases h41
            case inl h42 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- True on the right can always be proven directly.
              apply True.intro
            case inr h43 =>
              -- Disjunctions on the left can always be decomposed.
              cases h43
              case inl h44 =>
                -- Show the left disjunct based on <expert-advice>.
                apply Or.inl
                -- One of the premise coincides with the conclusion.
                exact h44
              case inr h45 =>
                -- Conjunctions on the left can always be decomposed.
                let h46 := h45.left
                let h47 := h45.right
                -- Show the right disjunct based on <expert-advice>.
                apply Or.inr
                -- True on the right can always be proven directly.
                apply True.intro
        case inr h48 =>
          -- Disjunctions on the left can always be decomposed.
          cases h1
          case inl h49 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h49
          case inr h50 =>
            -- Disjunctions on the left can always be decomposed.
            cases h50
            case inl h51 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- True on the right can always be proven directly.
              apply True.intro
            case inr h52 =>
              -- Disjunctions on the left can always be decomposed.
              cases h52
              case inl h53 =>
                -- Show the left disjunct based on <expert-advice>.
                apply Or.inl
                -- One of the premise coincides with the conclusion.
                exact h53
              case inr h54 =>
                -- Conjunctions on the left can always be decomposed.
                let h55 := h54.left
                let h56 := h54.right
                -- Show the right disjunct based on <expert-advice>.
                apply Or.inr
                -- True on the right can always be proven directly.
                apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115877386930996614495605362007 : ((((p4 ∧ (p1 ∧ p4)) ∧ p4) ∨ (((p1 → (False ∧ (False ∨ (p2 → p1)))) ∨ ((p3 ∨ (True ∧ False)) ∨ (p5 ∧ p4))) → p5)) ∨ (p4 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165995193997805237673395501493 : (((p3 ∧ p4) ∨ (((True → (((False → p3) ∧ p2) ∧ p1)) ∧ p4) ∨ (p5 ∨ (p3 ∧ p5)))) ∨ (((p5 → ((p5 → p1) ∧ True)) ∧ False) → p2)) := by
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
theorem thm_5_vars_316700973425652326514003085484 : (p3 ∨ (p5 ∨ (((p2 ∨ False) → True) → (((p3 ∨ ((True → (p1 ∨ p2)) ∨ (p1 ∨ p2))) ∨ (p4 → False)) ∨ ((p5 ∨ (p1 ∨ p3)) → True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_44309489884242280178444970727 : (((((False ∨ ((p5 ∧ ((p3 ∨ p2) ∨ p5)) ∧ (p5 → (p5 → (p4 ∨ p3))))) ∨ p4) ∨ ((p3 → p3) ∧ (p5 ∨ (p1 → p5)))) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179480162477565512267883098253 : ((True → (((((True ∨ p1) → p5) ∨ p5) ∨ p1) ∨ (p2 ∨ (False ∨ p1)))) ∨ ((p2 → ((p4 → False) ∧ (p5 ∧ p3))) ∨ (p3 → (p3 ∧ p3)))) := by
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
theorem thm_5_vars_113212681258818208231782455404 : (((((p1 ∨ False) → (((p2 → (p1 ∧ ((p5 ∧ True) ∧ p2))) ∨ p5) ∨ (((p2 ∧ p2) ∧ p3) ∨ p4))) ∨ p2) ∧ (p3 ∨ p1)) ∨ (p3 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179293267216126422244334564731 : ((False ∨ ((((False ∨ (p2 ∨ False)) → (p4 → True)) → (p5 → p5)) ∧ p2)) ∨ (((((p2 → (False → (p1 ∧ p5))) → False) ∨ p4) ∧ p3) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_649727285260088891612578825192 : ((((((p5 ∧ ((True ∨ (p5 → (p3 ∧ ((p4 ∧ ((False ∨ p1) ∨ p4)) ∧ True)))) ∧ (False → p5))) ∨ True) → (p4 ∨ p4)) ∧ (p3 ∨ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46700385864456621668451158953 : (((p3 ∨ (p4 → ((p5 ∧ (p2 → p1)) ∨ ((p2 ∨ (False ∨ False)) ∨ (((((True ∧ p4) ∨ p3) ∧ True) → p2) → p1))))) ∧ (True ∧ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350246023343566620296730280904 : (p4 → ((True ∧ (p3 ∧ ((((True ∧ p3) ∧ p1) → (p1 ∨ (((p1 → True) → ((p1 ∨ p2) ∨ ((p5 ∧ p1) → p2))) ∧ p3))) → p1))) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134690566899813173122548948721 : ((((((p3 → False) → True) → (p3 → True)) → ((((((True ∨ False) ∧ p1) → p1) ∧ p5) → (p4 → p5)) ∨ p1)) → p1) ∨ (True ∨ (p2 ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167478070903766703343911526054 : ((((((p3 → p5) → (p1 ∧ (p4 ∧ ((p3 ∧ p1) ∨ p3)))) ∨ True) ∧ p5) ∧ (p5 ∨ p1)) → (((p3 → p4) → p5) ∨ (p2 → (True → False)))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h7 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h8
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h9 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h10
      -- One of the premise coincides with the conclusion.
      exact h5
  case inr h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h12 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h13
      -- One of the premise coincides with the conclusion.
      exact h12
    case inr h14 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h15
      -- One of the premise coincides with the conclusion.
      exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206385704661481810239010520911 : ((p3 ∨ ((True ∨ (p1 ∧ p2)) ∧ False)) ∨ (p3 → ((((((p3 ∧ p5) ∧ p5) ∧ p1) ∧ p3) ∨ (((True ∧ False) ∧ (True ∨ True)) ∨ False)) ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148858808324220833937921626218 : (((True ∨ ((p3 ∧ False) ∨ p3)) ∧ ((p5 ∨ ((p2 ∨ p2) ∧ ((p4 ∨ (p3 ∧ True)) ∧ (p2 ∨ p4)))) ∧ p5)) ∨ (True → (p3 → (p1 → p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150889389759299542406889606568 : ((((p1 ∨ ((p2 → False) → True)) → (p3 ∧ (((p3 ∨ ((p1 ∨ (p5 ∨ p2)) → p3)) ∨ p1) ∧ False))) ∨ False) → ((p1 ∨ p5) ∨ (p3 ∧ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h3 : (p1 ∨ ((p2 → False) → True)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h4
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h5 := h2 h3
    -- We need to get the right conjuct of h5 based on <expert-advice>.
    let h6 := h5.right
    -- We need to get the right conjuct of h6 based on <expert-advice>.
    let h7 := h6.right
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- False on the left can always be used.
    apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165084121130035909887848952672 : (((p1 ∨ ((((p2 → p3) ∨ (((p3 → False) ∧ True) ∧ False)) ∨ (p4 ∨ p3)) ∧ True)) → p3) ∨ (((p5 ∧ p4) ∨ (p3 ∧ p2)) ∨ (False ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43844106556165523347616846109 : (((((p2 ∧ ((True → (p3 ∨ (False → False))) ∧ ((p2 → False) ∧ (((p3 ∧ (p1 ∨ p2)) ∨ p1) ∧ False)))) → p4) ∧ (p1 ∨ p2)) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342271084269953462721501740077 : (p2 → ((((p5 ∨ (p1 ∧ p1)) ∨ (p5 ∧ ((((True ∨ p5) ∧ True) ∨ (p1 ∧ p4)) ∧ p4))) ∧ p1) ∨ (((p5 → (p5 ∨ p2)) → p1) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213274772683072357955729766441 : ((((True → p1) → p3) ∧ p4) ∨ ((((p5 ∧ (p5 → p3)) → p2) ∨ ((False ∨ False) ∨ ((True ∧ p2) → (False → ((p3 ∨ p3) ∧ p1))))) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h2
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_343057218037842893505744210379 : (p2 → ((p4 → (False ∧ (p1 → True))) → (((p5 → p4) ∧ p5) → (((((p1 ∧ False) → ((True ∨ p3) ∨ p5)) → False) ∨ (p1 ∨ True)) ∧ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h6 := h3.left
  let h7 := h3.right
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_614464851953741549095725103532 : (((((((((p3 ∧ p3) → p4) → ((False → (p3 → (False ∨ p2))) → p2)) ∧ (p1 → p1)) ∨ p4) ∧ ((p5 ∧ p1) ∨ (p3 ∧ True))) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136208455579373197927295767450 : (((False → (((p5 ∧ p3) → p2) → p3)) ∧ (((p5 ∨ p1) → p1) → (((p3 ∧ (p4 ∧ p1)) ∧ p1) ∧ (True ∨ p2)))) ∨ (p1 → (p4 → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_93717465163405683105605492046 : ((p1 ∧ (((True → False) ∧ (True ∧ ((p1 → p1) ∨ (((p3 ∧ p3) → (((((p5 → p1) → True) ∧ p4) → p1) ∨ p2)) ∨ p3)))) ∧ p4)) → p2) := by
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
  let h8 := h7.left
  let h9 := h7.right
  -- Disjunctions on the left can always be decomposed.
  cases h9
  case inl h10 =>
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h11 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h12 := h6 h11
    -- False on the left can always be used.
    apply False.elim h12
  case inr h13 =>
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h14 =>
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h15 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h16 := h6 h15
      -- False on the left can always be used.
      apply False.elim h16
    case inr h17 =>
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h18 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h19 := h6 h18
      -- False on the left can always be used.
      apply False.elim h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300557798635460379269922265795 : (False ∨ (((p1 ∨ ((p3 ∨ False) ∨ True)) → ((((p2 ∧ True) → (p2 ∨ (p3 → p2))) ∧ (False ∧ p2)) ∧ p5)) ∨ (p1 → ((p1 ∨ p5) ∨ p5)))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199354593779539213745099259014 : ((((p5 → (p3 ∨ (p1 ∨ p5))) → p1) ∨ p4) → (((p5 ∨ (False ∨ (p5 → p2))) ∨ (False → (p4 → (p2 ∨ ((p5 → p1) ∨ p2))))) ∨ p5)) := by
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
    -- Implications on the right can always be decomposed.
    intro h4
    -- False on the left can always be used.
    apply False.elim h3
  case inr h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- Implications on the right can always be decomposed.
    intro h7
    -- False on the left can always be used.
    apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111469751977556439549070497196 : (((p1 → ((((((p3 → p4) ∨ (((p1 ∧ True) → True) ∨ p2)) → p1) ∨ (p3 ∧ (False → p5))) ∨ (p3 ∨ p2)) → False)) ∧ p2) ∨ (True ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_790700617452076592642031518203 : (((p5 ∨ (p5 ∨ (p5 ∧ ((((((p5 ∨ True) ∨ p5) → ((True → p3) → (((p4 ∧ p4) ∨ p4) ∨ (p2 ∨ False)))) ∧ p3) ∨ p3) ∨ p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231317321315314220391618749935 : (((True → False) ∨ p3) → ((p1 → p3) → ((((((p3 → ((p3 → True) ∧ True)) → (False ∨ (False → p4))) ∨ p1) → p3) ∨ (p5 ∧ p5)) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
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
theorem thm_5_vars_312356828817477339941510327340 : (p2 ∨ (p3 → ((((((p5 ∨ (p3 ∧ p5)) ∨ (p3 ∨ p5)) ∧ p2) ∧ (p2 → p1)) ∧ (((p4 ∧ p4) → (p5 ∧ p5)) → (False → True))) → p1))) := by
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
  let h5 := h3.left
  let h6 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h11 : p2 := by
        -- One of the premise coincides with the conclusion.
        exact h8
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h12 := h6 h11
      -- One of the premise coincides with the conclusion.
      exact h12
    case inr h13 =>
      -- Conjunctions on the left can always be decomposed.
      let h14 := h13.left
      let h15 := h13.right
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h16 : p2 := by
        -- One of the premise coincides with the conclusion.
        exact h8
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h17 := h6 h16
      -- One of the premise coincides with the conclusion.
      exact h17
  case inr h18 =>
    -- Disjunctions on the left can always be decomposed.
    cases h18
    case inl h19 =>
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h20 : p2 := by
        -- One of the premise coincides with the conclusion.
        exact h8
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h21 := h6 h20
      -- One of the premise coincides with the conclusion.
      exact h21
    case inr h22 =>
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h23 : p2 := by
        -- One of the premise coincides with the conclusion.
        exact h8
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h24 := h6 h23
      -- One of the premise coincides with the conclusion.
      exact h24



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338501640215680147625137689315 : (p1 → (((True ∧ True) ∧ p3) ∨ (((((p2 ∧ (p1 → p1)) ∧ (p2 ∨ ((p1 ∧ ((False ∨ p4) → False)) ∨ p3))) → (p2 ∨ True)) → p4) ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225526862437020544377308098782 : (((True → True) ∧ p5) ∨ (((p5 → p1) ∨ (((((p1 ∧ p4) → p2) ∨ (False ∧ (p1 ∨ (p4 → False)))) ∨ p4) → p3)) → ((p2 ∧ p1) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_68195117858559285140737415036 : ((p3 → (((p4 ∧ (p5 → p2)) ∧ ((p3 → ((((True ∨ ((p2 ∧ (p1 ∨ p1)) → (p3 ∧ p3))) → p5) → p4) ∧ False)) ∨ p2)) ∨ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342789230259102533676088389336 : (p2 → (((p2 ∨ (p3 → p1)) ∧ ((p1 → p4) ∨ p2)) → ((p4 ∧ p2) → (p2 ∧ ((((p4 → True) ∧ p1) ∧ (p2 ∨ p2)) ∨ (p3 ∨ True)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h2.left
  let h7 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h9 =>
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h10 =>
      -- One of the premise coincides with the conclusion.
      exact h1
  case inr h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h12 =>
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h13 =>
      -- One of the premise coincides with the conclusion.
      exact h1
  -- Conjunctions on the left can always be decomposed.
  let h14 := h3.left
  let h15 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h16 := h2.left
  let h17 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h16
  case inl h18 =>
    -- Disjunctions on the left can always be decomposed.
    cases h17
    case inl h19 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h20 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h21 =>
    -- Disjunctions on the left can always be decomposed.
    cases h17
    case inl h22 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h23 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45692641022067266247312260619 : (((p5 ∨ (p3 ∨ (((True → p1) → (((((True ∨ False) ∨ True) → p4) → False) ∧ p1)) ∧ (((True → p2) ∧ (p3 ∨ p3)) ∧ p5)))) → p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37859392796278373445883909305 : ((((p2 → (((p2 → (((True ∨ (p2 → True)) → p2) → p2)) → ((False ∧ p5) ∧ p3)) ∨ ((p4 ∨ (p4 ∧ p1)) → p5))) → p4) ∧ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_146945809340649843968413956839 : (((((((p1 ∨ (p2 ∨ (p2 ∧ True))) → p5) ∧ (p4 → p1)) ∨ (p3 ∨ ((True → p3) ∨ p4))) ∨ False) ∧ True) ∨ (False → (p2 ∧ (p2 ∨ p5)))) := by
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
theorem thm_5_vars_111436132312423963869647851441 : (((p5 ∨ ((p4 ∧ (((p3 ∧ p5) ∨ ((False ∨ p3) → True)) ∧ (((True ∨ False) → (p2 ∧ (p1 ∨ p2))) → False))) ∨ p1)) ∧ True) ∨ (p1 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_202502098771525359156253281220 : ((((p5 ∨ p2) ∨ True) ∨ (p5 → p5)) ∧ (((((((False ∧ False) ∧ (p3 → True)) ∧ p4) → p3) → False) → (False ∨ (p3 ∨ False))) ∧ (False → p2))) := by
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
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((((False ∧ False) ∧ (p3 → True)) ∧ p4) → p3) := by
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
    -- False on the left can always be used.
    apply False.elim h8
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h10 := h1 h2
  -- False on the left can always be used.
  apply False.elim h10
  -- Implications on the right can always be decomposed.
  intro h11
  -- False on the left can always be used.
  apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_709204777897894522699226594410 : (((((True → False) ∧ ((p3 → (p1 ∨ False)) ∧ p4)) → (((((p3 ∧ p3) ∨ p4) ∨ ((True ∨ False) ∨ p4)) ∨ (p1 ∨ (p4 → p5))) ∧ p3)) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h5
  -- Conjunctions on the left can always be decomposed.
  let h6 := h1.left
  let h7 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h7.left
  let h9 := h7.right
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h10 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h11 := h6 h10
  -- False on the left can always be used.
  apply False.elim h11
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166331254830455719475420617952 : ((p5 ∧ ((p4 → p2) → (p5 ∧ (True ∧ (True ∧ (((p4 → True) ∧ (p2 ∨ p1)) ∨ p5)))))) ∨ ((p4 → ((p3 → p1) → (p5 ∨ p4))) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171076932450454180629920094794 : ((p5 ∨ (False ∨ ((p5 ∨ (p1 → True)) ∨ (p1 ∨ (p1 ∨ ((p2 → False) → p1)))))) ∧ (p1 ∨ ((((p3 ∧ p4) ∧ p4) ∧ (p3 ∨ p1)) ∨ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41425343015946108518321510943 : (((((((True ∨ p1) → (True → p5)) ∧ ((False → p1) ∧ (p2 ∧ p5))) ∧ p3) → ((p4 ∧ (True → (p4 ∧ p5))) ∧ (True → p1))) ∨ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205223123400629720105995964613 : ((((p1 ∨ False) ∧ p4) ∨ (p2 ∨ False)) ∨ ((False → (p4 → (p1 ∨ (p4 → p3)))) ∨ (True ∧ ((p2 ∨ (False → True)) → ((p2 ∧ False) → False))))) := by
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
theorem thm_5_vars_205716401965617685125497049700 : (((p2 → p4) ∨ ((p3 ∨ p3) ∧ p5)) ∨ (((p1 ∨ p5) → ((p2 ∨ True) ∨ p2)) ∨ (((False ∧ p3) ∧ ((p4 ∧ False) ∧ p4)) ∧ (True ∧ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_150140568745740015036219872771 : ((p1 → (((((p2 ∧ p4) ∨ ((p3 ∧ p4) ∨ True)) ∧ ((False ∨ p2) → (False → p2))) → (p5 ∨ False)) ∧ p4)) ∨ ((p2 → (p2 → p1)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50216253531163967976983821427 : ((((((((p1 → p3) ∨ p1) ∨ p3) → True) → ((False → p3) ∧ (p3 ∨ ((False ∨ p4) ∨ p4)))) ∨ False) ∨ (((p3 ∧ False) ∨ p1) ∨ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171494880704219527913049578094 : (((p3 → ((p2 ∧ ((p4 → p3) ∨ p4)) → (p5 ∧ ((p2 ∧ True) ∧ p4)))) ∧ p2) ∨ ((((p2 ∧ False) ∨ p5) ∨ p2) → (True ∨ (p3 ∨ p2)))) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h4 := h3.left
      let h5 := h3.right
      -- False on the left can always be used.
      apply False.elim h5
    case inr h6 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h7 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134068802706348228974593399996 : ((((((((True ∧ p2) ∧ ((True ∨ (p5 ∧ True)) → ((p1 ∧ (p2 ∨ True)) ∨ p1))) ∧ p4) ∨ p2) → p5) → p1) ∨ True) ∨ ((p2 ∨ p3) ∧ p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187932757594075122927234292690 : ((((p5 ∧ (((p3 ∧ False) → p1) ∨ p2)) → True) ∧ True) ∧ ((p3 ∨ (p5 ∨ (False ∨ (((False ∨ False) ∧ (True → (False → False))) ∨ True)))) ∨ p4)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59948827489825741071146039001 : (((True ∨ p2) → ((((True → p3) ∨ p2) ∨ (p2 ∨ p1)) ∧ ((p2 → (True → ((p3 → True) ∨ p1))) ∧ ((p5 → False) ∨ (True → p2))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180460442799071635992645025145 : (((p4 ∧ ((((p1 ∨ p4) ∨ (p2 → p4)) ∨ p2) ∧ p4)) → (p1 ∧ p3)) → (p3 ∨ ((True ∨ (p3 → p1)) ∨ (True ∧ ((p3 ∨ False) ∨ False))))) := by
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
theorem thm_5_vars_116312129007411805449812126736 : (((p4 → (False ∧ p1)) ∨ ((True → p1) ∧ ((((p4 → p1) ∧ (p5 ∨ (p1 → p3))) → p3) ∧ ((p3 ∨ (p2 → False)) → p3)))) ∨ (p5 → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225302668777662404228452468688 : (((False ∨ p2) ∧ True) ∨ ((((((p2 → True) → p3) → (p1 → ((p5 ∨ (p4 → p4)) → (p1 ∧ p2)))) ∧ (True → p3)) ∨ p4) ∨ (False → False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_327714459416938849656983250454 : (True → ((((False ∨ (p2 → (((True ∧ p5) ∨ p2) → (((p4 ∧ p2) ∨ p3) ∧ True)))) → (p5 → p2)) ∨ (p3 → (p3 ∨ False))) ∧ (True ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147623545976815740147928242292 : ((((((p4 → (p3 ∧ (True ∧ ((p4 ∨ ((p4 ∨ True) ∧ (p1 ∧ p1))) ∧ False)))) ∧ p5) → p2) → p2) → False) ∨ (False → ((p3 ∧ False) ∧ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173200263359715480060117193691 : ((p5 ∨ ((True → (p3 → (False ∨ ((p5 ∨ False) ∧ ((True → p3) ∧ p1))))) ∨ p1)) ∨ ((p1 ∨ ((False ∧ (p3 ∧ True)) → False)) ∨ (False ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_394271761506060847182368775838 : (((((True ∨ True) → ((p3 ∧ ((p3 → p1) ∧ (p2 ∧ ((p2 → p3) → p4)))) ∨ (p1 ∧ ((p4 ∨ ((p1 ∧ False) → True)) → p2)))) ∨ True) ∧ True) ∧ True) := by
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
theorem thm_5_vars_613150707320581852739196240256 : (((((((((((p4 → p3) ∨ (p5 ∧ p5)) ∧ p4) ∧ False) → (False → (p1 ∧ (p1 ∧ p2)))) ∨ p3) ∨ (p2 ∧ p2)) → (p3 → p1)) ∨ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43154873882487973639248234229 : (((((p1 ∨ ((True ∧ True) → p4)) ∧ (p4 ∧ ((p2 ∧ (p5 → p5)) ∨ ((((p4 ∧ False) ∨ True) ∨ (True ∧ p5)) ∨ p2)))) ∧ p2) → p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172134426585854903199388021154 : ((((p2 ∨ p5) ∧ (((p1 → (False ∧ p4)) ∨ False) → p5)) ∧ (p4 ∧ (True → p1))) ∨ ((((p4 ∨ p1) ∨ False) ∧ p5) → ((p3 ∨ p5) ∨ p1))) := by
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h6
  case inr h7 =>
    -- False on the left can always be used.
    apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57171755795435531122517824867 : ((((p4 ∧ p2) ∨ p2) ∨ ((p4 ∧ (((True ∨ (p5 ∨ p3)) ∨ p3) → (p1 ∧ (False ∧ p5)))) → (((p1 ∨ p1) ∨ (p2 → p4)) → p5))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h7 : ((True ∨ (p5 ∨ p3)) ∨ p3) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h8 := h6 h7
      -- We need to get the right conjuct of h8 based on <expert-advice>.
      let h9 := h8.right
      -- We need to get the left conjuct of h9 based on <expert-advice>.
      let h10 := h9.left
      -- False on the left can always be used.
      apply False.elim h10
    case inr h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h1.left
      let h13 := h1.right
      -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
      have h14 : ((True ∨ (p5 ∨ p3)) ∨ p3) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h13, we can now drive its conclusion.
      let h15 := h13 h14
      -- We need to get the right conjuct of h15 based on <expert-advice>.
      let h16 := h15.right
      -- We need to get the left conjuct of h16 based on <expert-advice>.
      let h17 := h16.left
      -- False on the left can always be used.
      apply False.elim h17
  case inr h18 =>
    -- Conjunctions on the left can always be decomposed.
    let h19 := h1.left
    let h20 := h1.right
    -- We want to use the implication h20 based on <expert-advice>. So we show its premise.
    have h21 : ((True ∨ (p5 ∨ p3)) ∨ p3) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h20, we can now drive its conclusion.
    let h22 := h20 h21
    -- We need to get the right conjuct of h22 based on <expert-advice>.
    let h23 := h22.right
    -- We need to get the left conjuct of h23 based on <expert-advice>.
    let h24 := h23.left
    -- False on the left can always be used.
    apply False.elim h24



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114670343310705966840066840909 : ((((p4 ∧ p4) → (((p3 ∧ (False ∧ p4)) ∨ (((p3 ∧ True) ∨ p5) ∨ p1)) ∨ p1)) ∨ ((p1 ∨ (p4 → p4)) → (True ∨ p4))) ∨ (True ∧ p1)) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165156637796588354655733502893 : ((((p3 → ((p5 → p1) ∧ True)) ∧ (((True ∧ p2) ∧ (p4 → False)) → p2)) ∧ (p2 ∨ p1)) ∨ ((((p2 ∧ (False → p3)) → False) ∨ p3) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60247280823893279368303687511 : (((False → True) → (((True ∧ p5) → p1) ∨ (((True ∧ (p5 → ((p5 ∧ p2) → p2))) → (p5 ∧ (True ∧ False))) → ((True → p1) ∧ p4)))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (True ∧ (p5 → ((p5 ∧ p2) → p2))) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Implications on the right can always be decomposed.
    intro h5
    -- Implications on the right can always be decomposed.
    intro h6
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- One of the premise coincides with the conclusion.
    exact h8
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h9 := h2 h4
  -- We need to get the right conjuct of h9 based on <expert-advice>.
  let h10 := h9.right
  -- We need to get the right conjuct of h10 based on <expert-advice>.
  let h11 := h10.right
  -- False on the left can always be used.
  apply False.elim h11
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h12 : (True ∧ (p5 → ((p5 ∧ p2) → p2))) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Implications on the right can always be decomposed.
    intro h13
    -- Implications on the right can always be decomposed.
    intro h14
    -- Conjunctions on the left can always be decomposed.
    let h15 := h14.left
    let h16 := h14.right
    -- One of the premise coincides with the conclusion.
    exact h16
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h17 := h2 h12
  -- We need to get the right conjuct of h17 based on <expert-advice>.
  let h18 := h17.right
  -- We need to get the right conjuct of h18 based on <expert-advice>.
  let h19 := h18.right
  -- False on the left can always be used.
  apply False.elim h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57698912075461063693886351348 : ((((False ∧ p5) → p5) → (((p5 ∨ p4) ∨ (True → p5)) ∨ (False → ((False → ((((p1 ∨ p5) → p4) → p2) ∧ (p4 → p4))) ∧ p1)))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- False on the left can always be used.
  apply False.elim h3
  -- Implications on the right can always be decomposed.
  intro h5
  -- False on the left can always be used.
  apply False.elim h3
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337546032805736178999787782419 : (p1 → (((p1 ∧ p4) ∨ ((p3 ∨ ((p5 ∨ p3) → ((False → (p5 ∧ True)) → (p1 ∧ (p1 ∧ False))))) ∨ p1)) ∨ (p3 ∨ ((p1 ∨ p3) ∧ p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



