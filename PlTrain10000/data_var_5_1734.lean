variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52326678884465588288641133906 : ((((p4 ∧ (p1 ∨ ((((True → p4) ∧ False) ∧ p5) → (p1 → p5)))) ∨ p5) ∧ (p1 ∧ (((p1 ∨ (p2 → False)) ∨ (False ∧ p4)) → False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_628551430150013128265889866407 : (((((False ∨ (((((((p5 ∧ True) ∨ p4) ∨ p3) ∧ False) ∧ p4) ∨ (True ∧ p5)) ∧ ((p4 → True) ∨ ((p1 ∨ p4) ∨ p2)))) ∧ p2) → False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43934290659469198425286350851 : ((((((p4 → False) ∨ (((p3 → (True → p4)) ∨ ((True ∧ p1) → p4)) → p5)) ∨ ((p1 ∨ p1) → (p1 ∨ p2))) ∨ (p2 → True)) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_176925066315797628803703797439 : (((p5 ∨ p3) ∨ (((((True ∨ False) ∧ (False ∨ True)) → False) → True) → True)) ∧ (((p2 ∨ p5) ∧ ((False ∨ p4) ∨ ((p5 ∨ p2) → p3))) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_577376844562339576727109296852 : (((p3 → ((((False ∧ (p4 → True)) → (p1 ∨ (p5 ∨ (p4 ∧ p2)))) → (((False ∨ (p5 → p1)) ∧ (p1 ∧ p5)) ∧ True)) → (p1 ∨ False))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : ((False ∧ (p4 → True)) → (p1 ∨ (p5 ∨ (p4 ∧ p2)))) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- False on the left can always be used.
    apply False.elim h5
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h7 := h2 h3
  -- We need to get the left conjuct of h7 based on <expert-advice>.
  let h8 := h7.left
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- We need to get the left conjuct of h9 based on <expert-advice>.
  let h10 := h9.left
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h10
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198296248272480667948620437575 : ((p1 ∧ (((p1 → True) ∨ (p2 → p2)) ∨ p5)) ∨ ((True ∧ (p4 ∧ p1)) ∨ ((p3 → (((p2 → False) → True) → (p2 ∧ (False ∨ p3)))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_615643686569848336330958973673 : (((((((p5 ∧ ((p3 → (p2 ∧ True)) ∧ False)) ∧ ((False → p2) ∧ False)) ∨ p4) ∧ (((False ∧ (p1 → p3)) ∧ (True ∧ p2)) ∧ p1)) ∨ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337343791528414412679465427852 : (p1 → (((((((p2 ∧ p1) → ((p1 ∧ True) → p3)) ∧ False) ∨ (True → (((p4 → p1) → p2) → p5))) → False) ∨ p5) ∨ ((p3 → p1) ∨ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_864988399683565194541228704889 : ((((((True ∧ (p5 ∧ (True ∨ True))) ∧ p1) ∨ ((p4 ∨ (p3 ∧ p2)) ∨ (False → (p3 → (p4 ∧ ((p4 ∧ (p3 → p2)) ∨ p4)))))) → False) → p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((True ∧ (p5 ∧ (True ∨ True))) ∧ p1) ∨ ((p4 ∨ (p3 ∧ p2)) ∨ (False → (p3 → (p4 ∧ ((p4 ∧ (p3 → p2)) ∨ p4)))))) := by
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
    -- False on the left can always be used.
    apply False.elim h3
    -- False on the left can always be used.
    apply False.elim h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h2
  -- False on the left can always be used.
  apply False.elim h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173913700150897516062747001734 : ((((False ∨ ((((p1 → p3) ∨ p2) ∨ (p2 ∧ (p3 → False))) → True)) → p5) → True) → ((False → p5) ∧ ((p3 ∧ p5) ∨ (p1 → (p3 → p1))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_32570699159908659184195307764 : ((p2 ∨ (((p3 ∨ ((p2 ∨ p4) ∧ ((True ∨ ((True ∨ True) → False)) → p3))) ∨ p3) → (p4 ∨ (((p4 ∧ (p3 → p5)) → p1) → p3)))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
      -- Implications on the right can always be decomposed.
      intro h4
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h9
        -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
        have h10 : (True ∨ ((True ∨ True) → False)) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h7, we can now drive its conclusion.
        let h11 := h7 h10
        -- One of the premise coincides with the conclusion.
        exact h11
      case inr h12 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h12
  case inr h13 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h14
    -- One of the premise coincides with the conclusion.
    exact h13
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225465933629541481340220601095 : (((p4 ∨ p3) ∧ True) ∨ ((p5 ∧ (((True ∨ p5) → False) ∧ p5)) ∨ (((p3 → ((False ∧ p2) ∨ False)) ∨ ((True ∨ False) ∨ p1)) ∨ (p2 → p5)))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214171075619439481093631577285 : ((((p5 ∧ p1) → p2) → p1) ∨ (p4 → (((p2 → True) → ((((((p2 → False) ∧ True) → p4) ∧ False) ∨ p4) ∨ False)) ∧ ((False → p2) → p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_732339460906452939459087191975 : ((((False ∧ p1) ∧ ((p1 ∧ ((p3 → True) → (p4 → (False ∨ p5)))) ∧ ((True ∧ False) ∧ (True → (p2 → (p1 ∧ ((True → p3) ∨ p3))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345718728448859187256626754722 : (p3 → ((p2 → (p5 ∧ ((((p1 ∧ True) → (p5 ∨ (p2 ∧ p5))) → ((False ∧ ((p2 ∨ False) → False)) ∨ p1)) ∧ (p3 → (False ∨ p4))))) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137265353446041403756635778519 : ((p1 ∧ (p4 ∧ ((False ∧ ((p3 ∨ (p2 ∧ ((((True ∨ False) ∧ p5) ∨ False) ∧ True))) ∧ p1)) ∧ (p2 ∨ (p5 → p5))))) ∨ (p2 → (False → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_8227007839043182964090114617 : (((((((False ∨ True) ∧ p3) ∨ (p2 → (True ∨ (((False → ((p1 → p4) → p4)) ∧ (True → p2)) ∧ (p4 ∧ p5))))) ∧ p3) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2383343237420459088604214049 : ((p2 ∨ (p3 ∨ ((((True → p5) ∧ (True → p1)) ∨ p5) ∧ False))) ∨ (((p3 ∧ (p1 → (True ∧ (p4 → p2)))) ∨ True) ∧ (p5 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_135675118227983468910142273819 : (((p2 → ((p5 ∧ p2) ∨ ((p5 → p2) ∨ (p4 → (((p1 ∧ p2) ∨ True) ∨ p3))))) → (((p2 → p1) ∧ p3) ∧ p2)) ∨ (p5 → (False → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60093863762719341526310355607 : (((p3 ∨ False) → ((p5 → (((p2 → p3) ∨ (p1 ∨ False)) ∧ (((p2 ∨ p4) ∧ False) ∨ ((p4 ∨ (p1 ∨ True)) ∨ False)))) ∨ (p1 ∨ p2))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h4
    -- One of the premise coincides with the conclusion.
    exact h2
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
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49946091347996574270464644542 : ((((((((((p2 → True) → p1) → p2) → ((False ∨ True) ∧ p3)) → p5) → True) → p5) ∨ (True ∨ False)) ∧ ((False ∨ True) ∨ (False → p3))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350920130096380730398570952596 : (p4 → (((((False ∧ p1) ∧ (True ∨ p3)) ∧ (p5 → ((p2 ∨ (p1 ∨ ((p4 ∨ (p5 → p1)) → p5))) → (False ∨ True)))) ∨ p1) ∨ (True ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114313737902462717257371187973 : (((((True ∧ (p3 ∧ p4)) ∧ p1) ∨ (p1 → (False ∧ (False ∨ (((False ∧ False) → p2) ∧ False))))) ∧ (((p4 → p2) ∨ p2) → True)) ∨ (p2 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66449188953297640165923782388 : ((True → ((((((p5 → False) ∧ False) ∨ (p5 → (p5 → (True ∧ True)))) → (p2 ∨ p1)) ∨ (p2 → (((p4 → p1) → True) → p2))) ∧ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315147371046224252286050761398 : (p3 ∨ (((((p5 ∧ p2) → p2) ∧ p1) ∨ p5) → (((False → p1) → False) → ((((False → (p3 ∨ False)) ∨ p5) → ((p3 ∧ p3) → p5)) ∨ True)))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205528651489119915417783750890 : (((False ∨ p3) ∧ ((True → p5) ∧ p1)) ∨ ((p2 ∨ (p3 ∧ (((p5 → True) ∨ (p4 ∧ (p3 ∨ (p1 → ((p5 ∧ p4) → False))))) → p3))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313322202183600860033560473354 : (p3 ∨ ((p3 ∨ (((p4 ∨ (p5 ∧ (p4 → p4))) ∧ p1) ∨ (True ∧ ((True ∨ (False ∧ (True → ((p4 ∨ (p4 ∨ p2)) → False)))) ∨ p3)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192228566470060240550136145244 : (((((p2 ∧ p1) → (p4 ∨ False)) ∧ (p5 ∨ True)) ∧ p4) → ((p5 ∧ ((p5 ∧ (False ∨ (p5 → False))) ∧ (((p5 ∨ p1) ∧ True) ∧ True))) → False)) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h9 =>
    -- False on the left can always be used.
    apply False.elim h9
  case inr h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h6.left
    let h12 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h13 := h11.left
    let h14 := h11.right
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h15 =>
      -- Conjunctions on the left can always be decomposed.
      let h16 := h1.left
      let h17 := h1.right
      -- Conjunctions on the left can always be decomposed.
      let h18 := h16.left
      let h19 := h16.right
      -- Disjunctions on the left can always be decomposed.
      cases h19
      case inl h20 =>
        -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
        have h21 : p5 := by
          -- One of the premise coincides with the conclusion.
          exact h20
        -- We have shown the premise of h10, we can now drive its conclusion.
        let h22 := h10 h21
        -- False on the left can always be used.
        apply False.elim h22
      case inr h23 =>
        -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
        have h24 : p5 := by
          -- One of the premise coincides with the conclusion.
          exact h15
        -- We have shown the premise of h10, we can now drive its conclusion.
        let h25 := h10 h24
        -- False on the left can always be used.
        apply False.elim h25
    case inr h26 =>
      -- Conjunctions on the left can always be decomposed.
      let h27 := h1.left
      let h28 := h1.right
      -- Conjunctions on the left can always be decomposed.
      let h29 := h27.left
      let h30 := h27.right
      -- Disjunctions on the left can always be decomposed.
      cases h30
      case inl h31 =>
        -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
        have h32 : p5 := by
          -- One of the premise coincides with the conclusion.
          exact h31
        -- We have shown the premise of h10, we can now drive its conclusion.
        let h33 := h10 h32
        -- False on the left can always be used.
        apply False.elim h33
      case inr h34 =>
        -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
        have h35 : p5 := by
          -- One of the premise coincides with the conclusion.
          exact h7
        -- We have shown the premise of h10, we can now drive its conclusion.
        let h36 := h10 h35
        -- False on the left can always be used.
        apply False.elim h36



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_209365630634613429858074415471 : ((p1 → ((False ∧ (p5 ∧ p3)) ∧ p5)) → ((True ∧ (((((p4 ∧ p1) → ((p2 ∧ p5) ∨ p4)) ∧ True) ∧ p3) ∨ ((p4 → p4) ∧ p3))) → p3)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h6.left
    let h9 := h6.right
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- One of the premise coincides with the conclusion.
    exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_731497075372366870011794735225 : ((((True → (p4 → p3)) → (True ∧ (False ∨ ((((p4 ∨ p5) → p3) ∧ ((p4 → p2) ∨ ((p3 ∨ False) → ((p4 ∨ p4) ∨ p4)))) ∨ True)))) ∨ p2) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49797714100590893809049056953 : (((p5 ∨ (p1 → (True → (False → (((((True ∧ p3) → p5) ∨ p1) → (p5 ∧ ((p4 ∨ p2) ∨ p1))) → p5))))) → (p2 ∧ (True → p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_71384286270277426865750197004 : ((((p1 → False) ∧ (((((p1 ∨ (p5 ∨ p4)) → (p5 ∧ p1)) → (p5 ∨ ((p1 → p5) ∧ p2))) → (p2 ∧ (p1 ∧ p4))) ∧ p2)) ∧ p3) → p4) := by
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
  have h8 : (((p1 ∨ (p5 ∨ p4)) → (p5 ∧ p1)) → (p5 ∨ ((p1 → p5) ∧ p2))) := by
    -- Implications on the right can always be decomposed.
    intro h9
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h10
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h11 : p1 := by
      -- One of the premise coincides with the conclusion.
      exact h10
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h12 := h4 h11
    -- False on the left can always be used.
    apply False.elim h12
    -- One of the premise coincides with the conclusion.
    exact h7
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h13 := h6 h8
  -- We need to get the right conjuct of h13 based on <expert-advice>.
  let h14 := h13.right
  -- We need to get the right conjuct of h14 based on <expert-advice>.
  let h15 := h14.right
  -- One of the premise coincides with the conclusion.
  exact h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174467646683154059443791220195 : (((((p1 ∨ p4) ∨ (p3 → p2)) ∨ p5) ∧ (p3 ∨ (False → (False ∨ (p1 ∧ p4))))) → (((p2 ∨ (False ∨ ((False → p1) ∨ p3))) ∨ p3) ∨ p4)) := by
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
        -- Disjunctions on the left can always be decomposed.
        cases h3
        case inl h7 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h7
        case inr h8 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Implications on the right can always be decomposed.
          intro h9
          -- False on the left can always be used.
          apply False.elim h9
      case inr h10 =>
        -- Disjunctions on the left can always be decomposed.
        cases h3
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
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h14 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h14
      case inr h15 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h16
        -- False on the left can always be used.
        apply False.elim h16
  case inr h17 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h18 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h18
    case inr h19 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h20
      -- False on the left can always be used.
      apply False.elim h20



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53984430060861658176179624461 : (((((((p1 ∧ False) → p1) ∧ p5) ∨ (p4 → p3)) ∨ p3) → ((p3 → (((p3 → True) ∧ p5) ∧ False)) ∨ (p4 → ((p3 ∧ p1) → p3)))) ∨ p1) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h4 := h3.left
      let h5 := h3.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- Implications on the right can always be decomposed.
      intro h7
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h11
      -- Implications on the right can always be decomposed.
      intro h12
      -- Conjunctions on the left can always be decomposed.
      let h13 := h12.left
      let h14 := h12.right
      -- One of the premise coincides with the conclusion.
      exact h13
  case inr h15 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h16
    -- Implications on the right can always be decomposed.
    intro h17
    -- Conjunctions on the left can always be decomposed.
    let h18 := h17.left
    let h19 := h17.right
    -- One of the premise coincides with the conclusion.
    exact h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50834925561562777349679285818 : (((((((p5 ∧ (p1 ∧ p4)) ∨ p3) ∧ p2) ∧ ((p2 ∧ p3) ∧ (p4 ∨ (p2 ∧ p2)))) ∧ p4) ∧ (p5 → (False ∧ (False ∨ (p3 ∧ p2))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310426230895006038437926133087 : (p2 ∨ (((((True ∧ p2) → True) → False) → (p1 ∨ p3)) → ((((False → p5) ∧ True) → p1) ∨ (p5 → (((True ∨ (True ∨ True)) ∧ True) ∨ p2))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180790506326804215184300908821 : (((p3 ∨ (p4 ∧ (True → p1))) → (False → ((p1 → p2) → (p2 ∨ p3)))) → ((p4 ∨ ((p3 → (p2 ∧ p3)) → p4)) ∨ (True → (p2 → p2)))) := by
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
theorem thm_5_vars_260001418171511189514702112986 : ((p2 → True) → (((p1 ∧ p2) → (((p2 ∧ (True ∧ p3)) → p2) ∧ (p5 ∨ p1))) → (p3 → ((p4 ∧ ((True ∧ False) ∨ (True → p2))) → p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- False on the left can always be used.
    apply False.elim h9
  case inr h10 =>
    -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
    have h11 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h10, we can now drive its conclusion.
    let h12 := h10 h11
    -- One of the premise coincides with the conclusion.
    exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_664069950604797031809279399 : ((((False → p5) → ((p5 ∨ ((p1 → ((p2 ∨ False) ∧ (True ∧ p1))) ∨ p1)) → (p3 ∧ p3))) ∨ (True ∨ (p2 → (p4 ∨ False)))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178222355202150658617666550355 : (((False → (((p1 ∨ (p2 ∧ False)) ∨ p5) → (True ∨ (p4 ∨ p2)))) → p4) ∨ (p1 ∨ ((False ∧ (((p5 ∧ p5) → (False ∧ p3)) ∨ p3)) → False))) := by
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
theorem thm_5_vars_41019323172020967563827821445 : (((((((p1 ∨ p1) → (p1 ∨ ((p4 → False) ∧ (p2 ∨ (True → ((p4 ∨ True) ∧ True)))))) ∧ (p3 ∧ p3)) → p4) → (p2 → p5)) ∨ True) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_601908192507275936096570051422 : ((((p4 ∧ (True ∧ (p1 ∨ (False ∧ ((p2 ∧ p3) → (p5 → (p5 → ((p3 → (True ∧ (p5 ∧ (p4 ∧ (p2 ∧ p2))))) ∨ p4)))))))) ∧ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_327176174809456037951203444918 : (True → ((False ∨ (p1 ∨ ((p3 ∨ (p3 ∨ p5)) ∨ ((p3 ∧ ((False ∨ p4) ∧ p5)) → ((True ∨ (True → (p1 → (p2 → p2)))) ∧ p5))))) ∨ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h7 =>
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h9 := h2.left
  let h10 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h11 := h10.left
  let h12 := h10.right
  -- Disjunctions on the left can always be decomposed.
  cases h11
  case inl h13 =>
    -- False on the left can always be used.
    apply False.elim h13
  case inr h14 =>
    -- One of the premise coincides with the conclusion.
    exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115369635123788859337801868248 : ((((p3 ∨ (p3 → ((p2 ∧ p4) → p4))) → p2) ∧ ((p5 ∨ False) ∨ ((p3 ∧ (False ∧ (((p1 → True) ∧ p4) → p3))) ∧ p1))) ∨ (p4 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66618871741221731002064806253 : ((True → ((((p1 ∧ p5) ∨ ((((p4 ∧ ((False ∨ True) ∧ p3)) → p2) → True) ∧ p1)) ∨ p3) ∨ ((p5 ∨ (p2 ∧ p2)) → (p5 → p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244255718308849780556766483983 : ((False ∧ True) ∨ (((p3 ∨ ((p4 ∨ p1) → ((True ∧ ((((False ∧ p4) → p3) ∨ p5) → False)) → (p1 ∨ p3)))) → ((p3 ∧ p4) ∧ True)) → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p3 ∨ ((p4 ∨ p1) → ((True ∧ ((((False ∧ p4) → p3) ∨ p5) → False)) → (p1 ∨ p3)))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h7 =>
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h8 : (((False ∧ p4) → p3) ∨ p5) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h9
        -- Conjunctions on the left can always be decomposed.
        let h10 := h9.left
        let h11 := h9.right
        -- False on the left can always be used.
        apply False.elim h10
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h12 := h6 h8
      -- False on the left can always be used.
      apply False.elim h12
    case inr h13 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h13
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h14 := h1 h2
  -- We need to get the left conjuct of h14 based on <expert-advice>.
  let h15 := h14.left
  -- We need to get the left conjuct of h15 based on <expert-advice>.
  let h16 := h15.left
  -- One of the premise coincides with the conclusion.
  exact h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59520604089403586300754527896 : (((p2 → p3) ∨ ((p2 ∧ ((False ∨ False) ∧ (((p5 → p2) ∨ ((p3 → p4) ∧ (p2 → p2))) → (True ∨ p3)))) ∨ (p1 ∧ (p2 ∧ p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310516947532122790463533583749 : (p2 ∨ ((p1 → (False ∨ ((p2 → p4) ∧ p2))) ∨ (((((p5 → p4) → p1) → False) ∧ (False → ((p2 → p3) ∧ (p3 ∨ p1)))) ∨ (True ∨ p1)))) := by
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
theorem thm_5_vars_137203645726950356449753351984 : ((False ∧ (p2 ∨ (((((p2 ∧ (p1 ∧ True)) ∧ ((((True → False) → False) ∧ p3) → p3)) → p4) → p1) → (p5 ∨ False)))) ∨ ((p1 ∧ False) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178793978620027416601700534965 : ((((p1 → False) ∧ p4) ∨ (p5 ∨ ((p5 ∧ (p3 ∨ p4)) → (p1 ∧ p4)))) ∨ (((((p3 ∨ False) → True) ∨ p1) ∨ p4) ∨ (True → (p3 → True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177314820921867727259695794517 : ((p2 ∨ ((((True ∨ (p1 → p2)) ∧ False) → True) ∧ (p5 → (p1 ∨ True)))) ∧ (((True ∧ p2) ∨ True) → (p5 ∨ (p1 ∨ (p3 ∨ (True ∨ p4)))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
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
  case inr h7 =>
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
theorem thm_5_vars_148982846158263173411802485122 : (((p4 ∧ (False ∨ p4)) ∧ ((p4 ∧ ((p1 → ((False ∧ p3) ∨ (p4 → p3))) ∨ (True ∧ p5))) ∨ (p3 ∧ p1))) ∨ (((True → True) ∨ False) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199299612550877920198276424616 : (((((p1 ∨ (p4 ∨ p3)) ∨ True) ∨ True) ∨ p3) → (p4 → (False ∨ ((((p1 → False) ∨ p4) ∧ (p5 → (p5 → (True ∨ False)))) ∧ (True ∨ False))))) := by
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
        -- Disjunctions on the left can always be decomposed.
        cases h5
        case inl h6 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h2
          -- Implications on the right can always be decomposed.
          intro h7
          -- Implications on the right can always be decomposed.
          intro h8
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h9 =>
          -- Disjunctions on the left can always be decomposed.
          cases h9
          case inl h10 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Conjunctions on the right can always be decomposed.
            apply And.intro
            -- Conjunctions on the right can always be decomposed.
            apply And.intro
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h10
            -- Implications on the right can always be decomposed.
            intro h11
            -- Implications on the right can always be decomposed.
            intro h12
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- True on the right can always be proven directly.
            apply True.intro
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h13 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Conjunctions on the right can always be decomposed.
            apply And.intro
            -- Conjunctions on the right can always be decomposed.
            apply And.intro
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h2
            -- Implications on the right can always be decomposed.
            intro h14
            -- Implications on the right can always be decomposed.
            intro h15
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- True on the right can always be proven directly.
            apply True.intro
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- True on the right can always be proven directly.
            apply True.intro
      case inr h16 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h2
        -- Implications on the right can always be decomposed.
        intro h17
        -- Implications on the right can always be decomposed.
        intro h18
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h19 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
      -- Implications on the right can always be decomposed.
      intro h20
      -- Implications on the right can always be decomposed.
      intro h21
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h22 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
    -- Implications on the right can always be decomposed.
    intro h23
    -- Implications on the right can always be decomposed.
    intro h24
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_807545651608033845309449010546 : (((p4 → (((False → p1) ∨ (p2 → (True → True))) → ((((p3 ∨ ((((p3 ∧ p1) ∧ p1) ∧ p3) ∨ (p2 → p2))) ∨ True) ∨ p4) ∨ p5))) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137212158927917206716116922712 : ((False ∧ (p4 → (True → ((False ∨ (p5 ∨ True)) → (((p1 → p5) ∧ ((p2 ∧ p4) → (True → (p4 → False)))) → p3))))) ∨ ((p4 → True) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_631824839806976014487635380145 : ((((((((((p4 → p4) → p1) ∨ True) ∨ p5) → p5) → (p4 → (p1 ∧ ((True ∨ (((p1 → p2) ∧ p2) ∧ True)) → p1)))) → p2) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_605792338969158212188790909828 : ((((p4 → (False ∨ (((((False ∧ ((p5 → p4) ∧ (True ∨ p3))) → ((p2 ∨ (p4 → False)) ∨ (True ∨ p4))) ∧ True) → p5) ∨ False))) ∧ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114210650226525684628501539017 : (((((p2 → p3) ∨ False) ∨ ((p1 → ((p4 ∨ ((True → (True → p1)) → p4)) ∨ False)) ∧ (p2 ∨ p3))) → (False ∧ (p1 ∨ True))) ∨ (False → False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174171682358827762744577152324 : (((True ∧ ((((p4 ∧ p4) ∨ False) ∧ True) ∨ (p1 ∨ (True → p1)))) ∨ (p2 → p1)) → (((p2 ∨ p5) ∧ p4) → ((True ∧ (p5 ∧ False)) ∨ p4))) := by
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
    cases h1
    case inl h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Conjunctions on the left can always be decomposed.
        let h10 := h9.left
        let h11 := h9.right
        -- Disjunctions on the left can always be decomposed.
        cases h10
        case inl h12 =>
          -- Conjunctions on the left can always be decomposed.
          let h13 := h12.left
          let h14 := h12.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h14
        case inr h15 =>
          -- False on the left can always be used.
          apply False.elim h15
      case inr h16 =>
        -- Disjunctions on the left can always be decomposed.
        cases h16
        case inl h17 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h4
        case inr h18 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h4
    case inr h19 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
  case inr h20 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h21 =>
      -- Conjunctions on the left can always be decomposed.
      let h22 := h21.left
      let h23 := h21.right
      -- Disjunctions on the left can always be decomposed.
      cases h23
      case inl h24 =>
        -- Conjunctions on the left can always be decomposed.
        let h25 := h24.left
        let h26 := h24.right
        -- Disjunctions on the left can always be decomposed.
        cases h25
        case inl h27 =>
          -- Conjunctions on the left can always be decomposed.
          let h28 := h27.left
          let h29 := h27.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h29
        case inr h30 =>
          -- False on the left can always be used.
          apply False.elim h30
      case inr h31 =>
        -- Disjunctions on the left can always be decomposed.
        cases h31
        case inl h32 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h4
        case inr h33 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h4
    case inr h34 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185049538892970053454659270531 : (((p5 → False) ∧ (p2 ∨ (((True → p5) ∨ (p4 ∨ p1)) ∧ p3))) ∨ (p4 → (((p4 ∧ (True ∧ (p1 ∨ True))) → False) → (p5 ∨ (False ∨ p4))))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_646361892827996385812279599616 : ((((False → (p3 ∨ (((p5 → ((p3 ∧ (False → (p1 ∧ (True ∧ p2)))) ∨ False)) → ((((p1 → p4) ∧ p5) ∧ p4) → p4)) ∨ p2))) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157001864554391359707989092360 : (((((p1 ∨ True) → (False → p3)) → ((p5 ∧ True) → (p2 ∨ (p2 ∧ (p3 → (True ∨ p3)))))) ∨ p5) ∨ ((p1 ∨ (True → True)) ∨ (p3 → p2))) := by
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
theorem thm_5_vars_41650386158600952807295235448 : (((((p5 ∧ (p3 ∧ p5)) ∨ (p1 ∨ p1)) ∧ ((p1 → (((p2 → ((False → True) ∧ p5)) ∧ True) ∨ (True → p2))) → (p5 ∨ True))) ∨ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228433427902952638573212907724 : ((False ∨ (p5 ∧ p4)) ∨ ((False ∧ False) ∨ (((p4 ∧ (p1 ∨ (p1 → True))) ∧ True) ∨ (((p5 ∧ False) → (p5 ∧ True)) ∨ (False ∨ (p3 → p3)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44217594370820538616920856990 : (((((((p5 → (False ∧ (p4 → False))) ∧ ((p5 ∧ p5) → ((p3 ∧ p5) ∧ False))) ∧ True) ∧ True) ∨ (p1 → (p4 → (p2 ∧ p5)))) → p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_908958765420185953079619603500 : ((((((True → p3) ∨ ((p4 → (((p5 ∨ p3) ∨ True) → True)) ∧ p2)) ∧ (False ∨ (p4 → p3))) ∧ ((False → p3) → ((p2 ∨ p1) ∧ p1))) → p1) ∧ True) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- False on the left can always be used.
      apply False.elim h7
    case inr h8 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h9 : (False → p3) := by
        -- Implications on the right can always be decomposed.
        intro h10
        -- False on the left can always be used.
        apply False.elim h10
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h11 := h3 h9
      -- We need to get the right conjuct of h11 based on <expert-advice>.
      let h12 := h11.right
      -- One of the premise coincides with the conclusion.
      exact h12
  case inr h13 =>
    -- Conjunctions on the left can always be decomposed.
    let h14 := h13.left
    let h15 := h13.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h16 =>
      -- False on the left can always be used.
      apply False.elim h16
    case inr h17 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h18 : (False → p3) := by
        -- Implications on the right can always be decomposed.
        intro h19
        -- False on the left can always be used.
        apply False.elim h19
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h20 := h3 h18
      -- We need to get the right conjuct of h20 based on <expert-advice>.
      let h21 := h20.right
      -- One of the premise coincides with the conclusion.
      exact h21
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_660278466924963703810032269440 : (((((True ∧ (((((p2 ∨ p4) → True) ∧ (((True ∨ p4) ∨ p5) ∨ True)) → (p5 ∧ p3)) ∨ ((p2 → p5) ∨ p1))) ∨ True) → (False ∨ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112520740860735297877538933422 : ((((((((p5 ∨ False) → False) ∨ (((p4 ∨ p5) ∨ (p1 → p3)) ∧ (p1 ∧ False))) ∨ ((p4 ∨ p4) → True)) → p3) → True) → False) ∨ (False → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_638984840572172262531705298607 : (((((p5 ∨ ((p3 ∨ p5) ∧ p3)) ∧ ((p5 → ((p5 ∨ p1) → p2)) ∨ (False → (((False ∨ ((True → p4) → True)) → p3) → p5)))) → p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246703653798291901327325954626 : ((p5 ∧ p4) ∨ (((((p1 → p1) ∧ False) ∧ p4) ∧ (p1 → p2)) ∨ ((p5 ∨ (p5 ∧ ((False ∧ p3) → ((p4 ∧ True) → (False ∨ False))))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_326893096924074506605002574226 : (True → (((p3 ∨ (((((p3 ∧ p1) ∨ p3) ∨ (True → (p5 ∧ p5))) ∧ (p2 ∨ (p5 ∨ p4))) ∨ ((p5 ∧ p4) ∨ (p3 → p3)))) ∨ p4) ∨ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2578389990978681817881640369 : (((p1 ∨ ((p3 → p1) → (p3 ∨ p2))) ∨ p4) → ((p4 → (p1 ∨ p5)) ∨ ((p3 ∧ False) → ((p1 ∨ ((p4 ∧ p3) ∨ p4)) ∧ False)))) := by
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- False on the left can always be used.
      apply False.elim h8
      -- Conjunctions on the left can always be decomposed.
      let h9 := h6.left
      let h10 := h6.right
      -- False on the left can always be used.
      apply False.elim h10
  case inr h11 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h12
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the left can always be decomposed.
    let h13 := h12.left
    let h14 := h12.right
    -- False on the left can always be used.
    apply False.elim h14
    -- Conjunctions on the left can always be decomposed.
    let h15 := h12.left
    let h16 := h12.right
    -- False on the left can always be used.
    apply False.elim h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135827699652977832608025413307 : ((((((p2 ∧ (p1 ∨ False)) ∨ p4) ∨ p5) ∧ ((p3 → p1) ∧ False)) ∧ (((p3 → (False ∧ (p3 ∨ False))) ∨ p2) ∨ p5)) ∨ ((p4 ∨ p1) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_151586029939040792938575439063 : ((((p1 ∨ (False ∨ (False ∨ ((p3 ∨ p4) ∧ True)))) ∨ ((((p1 ∨ p2) ∨ True) ∧ True) → p1)) → (False ∨ p5)) → (p2 ∨ ((True → p3) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147288156197648997298646488619 : ((((p1 → ((((p2 ∨ (p3 ∧ p4)) ∧ ((p1 ∨ p4) ∨ True)) → ((p1 → p2) ∨ p5)) → p4)) ∨ True) ∨ p4) ∨ (p5 ∨ ((p4 ∧ p2) ∨ p1))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305409665148325899129626474155 : (p1 ∨ (((((p4 ∨ True) ∨ p5) ∨ True) → ((p5 ∨ (p4 ∨ p5)) ∧ (True ∨ (p2 ∨ True)))) ∨ (((p3 ∨ p5) ∧ (False ∧ (p5 ∧ True))) → p2))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h3.left
    let h6 := h3.right
    -- False on the left can always be used.
    apply False.elim h5
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h3.left
    let h9 := h3.right
    -- False on the left can always be used.
    apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_798973594293402561401164831629 : (((p1 → ((p3 ∨ p4) ∨ (((p2 ∨ (p5 → ((p3 ∨ True) ∨ (p2 ∨ p2)))) ∧ (False ∨ (p3 → p3))) ∨ (((p3 → p3) → False) ∧ p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_355975309035347689470989654514 : (p5 → (((((False ∧ (((p4 ∧ (p2 ∨ p5)) ∧ ((True ∧ True) ∧ p2)) ∧ p4)) ∧ p4) ∨ p5) ∨ (p2 → p4)) ∧ (p5 ∧ ((p2 ∧ p1) → p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200605975478948699503341558522 : ((True ∧ (p4 → (False ∧ (p5 ∧ (p1 ∨ p2))))) → ((p4 ∨ (((p2 ∧ p2) ∨ p4) ∨ ((False ∧ p2) ∨ ((p4 ∧ False) ∧ p5)))) ∨ (p3 ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305046491586177981713001610917 : (p1 ∨ (((p5 ∨ (((False ∨ p1) → p4) ∨ (p3 ∨ (p5 ∨ ((((p4 ∧ p5) → p5) → p1) ∨ (p1 ∧ p2)))))) ∧ p3) → (p5 ∨ (p1 → p3)))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h7
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h10
        -- One of the premise coincides with the conclusion.
        exact h3
      case inr h11 =>
        -- Disjunctions on the left can always be decomposed.
        cases h11
        case inl h12 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h12
        case inr h13 =>
          -- Disjunctions on the left can always be decomposed.
          cases h13
          case inl h14 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h15
            -- One of the premise coincides with the conclusion.
            exact h3
          case inr h16 =>
            -- Conjunctions on the left can always be decomposed.
            let h17 := h16.left
            let h18 := h16.right
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h19
            -- One of the premise coincides with the conclusion.
            exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50486338527013966656609962005 : (((p3 → (p4 ∨ ((p1 ∧ (p4 ∨ (p4 ∧ p4))) ∧ (p4 ∧ (False ∨ ((p4 → (p4 → p5)) ∨ p1)))))) ∨ (p2 ∨ (True ∧ (True → p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317720782973467673995539288553 : (p4 ∨ ((((p1 ∧ p3) ∨ (True → (True ∨ ((((p5 ∧ p2) → ((p2 → (False ∨ False)) ∨ p2)) ∧ (False → p2)) ∨ p2)))) → (p1 ∧ False)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_647085770536364873188855769508 : ((((p3 → ((p2 → (True → (False ∨ (p3 ∨ (p1 ∨ (p1 → p4)))))) ∧ (((p5 → p1) → (((p5 ∨ p1) ∧ False) ∨ p1)) ∧ p4))) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_131013191598586446334384522423 : (((((p5 → False) ∧ (True ∧ ((p5 ∨ p3) → p5))) ∧ p2) ∨ ((p2 ∨ (p5 → (p5 ∨ ((p2 ∧ p1) ∨ p5)))) ∨ p3)) ∧ (p5 ∨ (True ∨ p1))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_641914040391869938182009097550 : (((((p3 → True) → (((p3 ∧ (((p4 → p1) → (((False ∨ p1) ∧ p1) ∨ p3)) ∧ True)) ∨ p2) → (p3 ∨ (p3 ∨ (p3 ∨ p4))))) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185245646083205294119521451316 : ((p1 ∧ (((((p5 ∨ (True ∨ p3)) ∨ False) → p5) ∧ False) ∧ p4)) ∨ (((((p1 → p3) ∨ p1) ∨ ((p1 ∧ p3) ∨ True)) ∨ True) ∧ (True ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116547180109972933650353343852 : (((False ∨ p5) ∧ ((p2 ∧ (((p5 → (p4 ∧ p3)) ∨ (p2 ∨ p5)) ∨ (True ∧ (p3 → (p1 ∨ p1))))) ∧ ((p5 ∧ p3) ∧ p1))) ∨ (True ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150674561005313302106621197663 : (((False → ((p4 ∧ ((True ∧ p1) ∨ (p3 ∨ (p5 ∨ (((p3 ∨ p5) ∧ p2) → False))))) → (p1 ∨ p1))) ∧ True) → ((p5 → p3) ∨ (p1 ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136643484199753728355676954135 : ((((False ∨ False) → p5) → (((p2 ∧ ((p1 ∧ p5) ∧ (p1 ∨ (p1 → (True ∧ ((p4 ∨ p3) ∨ p3)))))) → False) ∧ p3)) ∨ ((p5 ∨ p2) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_650639013658789111463443596730 : (((((p2 ∨ (((p2 ∧ True) ∨ (p3 → p4)) → (p3 ∨ p2))) ∧ (((p2 ∨ (False → p3)) ∧ (False → p4)) ∧ (p1 ∨ p2))) ∧ (p1 ∨ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_613651576147494309470916368932 : ((((((p1 ∧ (True → (p1 → ((((p1 ∨ False) ∨ p2) ∧ p4) ∨ p1)))) ∧ (((p4 ∨ p3) ∨ p1) → False)) ∧ ((p4 ∨ False) ∧ p4)) ∨ True) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_186481214402401128530473201442 : (((((p4 → p3) → True) → (p3 ∧ (p2 ∧ p1))) ∧ (p3 → p2)) → ((True ∧ p5) → (p5 ∧ ((p5 ∧ (p3 ∧ (p2 ∧ (False ∨ p2)))) ∧ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h1.left
  let h6 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h7 := h2.left
  let h8 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h9 := h1.left
  let h10 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h8
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h11 := h2.left
  let h12 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h13 := h1.left
  let h14 := h1.right
  -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
  have h15 : ((p4 → p3) → True) := by
    -- Implications on the right can always be decomposed.
    intro h16
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h13, we can now drive its conclusion.
  let h17 := h13 h15
  -- We need to get the left conjuct of h17 based on <expert-advice>.
  let h18 := h17.left
  -- One of the premise coincides with the conclusion.
  exact h18
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h19 := h2.left
  let h20 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h21 := h1.left
  let h22 := h1.right
  -- We want to use the implication h21 based on <expert-advice>. So we show its premise.
  have h23 : ((p4 → p3) → True) := by
    -- Implications on the right can always be decomposed.
    intro h24
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h21, we can now drive its conclusion.
  let h25 := h21 h23
  -- We need to get the right conjuct of h25 based on <expert-advice>.
  let h26 := h25.right
  -- We need to get the left conjuct of h26 based on <expert-advice>.
  let h27 := h26.left
  -- One of the premise coincides with the conclusion.
  exact h27
  -- Conjunctions on the left can always be decomposed.
  let h28 := h2.left
  let h29 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h30 := h1.left
  let h31 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h30 based on <expert-advice>. So we show its premise.
  have h32 : ((p4 → p3) → True) := by
    -- Implications on the right can always be decomposed.
    intro h33
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h30, we can now drive its conclusion.
  let h34 := h30 h32
  -- We need to get the right conjuct of h34 based on <expert-advice>.
  let h35 := h34.right
  -- We need to get the left conjuct of h35 based on <expert-advice>.
  let h36 := h35.left
  -- One of the premise coincides with the conclusion.
  exact h36
  -- Conjunctions on the left can always be decomposed.
  let h37 := h2.left
  let h38 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h39 := h1.left
  let h40 := h1.right
  -- We want to use the implication h39 based on <expert-advice>. So we show its premise.
  have h41 : ((p4 → p3) → True) := by
    -- Implications on the right can always be decomposed.
    intro h42
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h39, we can now drive its conclusion.
  let h43 := h39 h41
  -- We need to get the right conjuct of h43 based on <expert-advice>.
  let h44 := h43.right
  -- We need to get the right conjuct of h44 based on <expert-advice>.
  let h45 := h44.right
  -- One of the premise coincides with the conclusion.
  exact h45



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337939225512332835554088461333 : (p1 → ((((True ∧ p5) → ((False → ((p2 → True) ∨ p1)) → p2)) ∧ p5) ∨ ((((p1 ∧ p2) → (p1 ∧ p1)) ∧ (False ∧ (True ∨ p2))) → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117065251980634502889767009699 : (((p5 ∨ p5) → ((p1 ∨ (((p3 ∨ (p4 ∧ (True → p5))) ∧ p5) → (True → (False ∧ p1)))) ∧ (p2 ∨ (True → (False ∨ False))))) ∨ (p2 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111496418658970407334607122493 : (((p3 → ((False ∧ p2) ∧ ((False ∨ ((((True → p5) ∨ False) ∧ (True ∨ (False ∧ (False ∧ p5)))) → (p2 ∨ p4))) → p4))) ∧ p2) ∨ (True ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179388489529161556250385770106 : ((p3 ∨ ((p5 ∨ (p1 → ((p3 → (p2 ∨ (p2 ∧ p5))) → p2))) → p2)) ∨ (p1 → (((True ∧ (p4 ∨ True)) ∨ p5) ∨ (p1 ∧ (p1 ∧ p2))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219559749907118521529015061594 : ((True → ((False ∧ True) ∨ p2)) → (((False ∨ False) ∨ ((((((False → False) ∧ (p4 ∧ (p3 ∨ True))) ∨ p1) → p2) ∨ (p4 → p5)) ∧ p3)) ∨ p2)) := by
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
    -- False on the left can always be used.
    apply False.elim h5
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_696595170127738254845385519235 : ((((((((False → True) ∨ False) ∧ (True → p4)) ∧ (p2 → False)) ∨ True) ∧ (((p3 ∧ ((p5 ∨ ((p2 ∧ p5) ∧ False)) ∧ True)) ∧ p5) ∨ True)) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_731381097113648114742345350145 : ((((p5 ∨ (p1 ∨ True)) → (False ∧ (p2 → ((((((p5 ∨ p3) ∧ (p2 → (True → False))) → p1) → (p4 → p3)) ∨ p5) ∧ (p2 ∧ p4))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_680487252449545865217458008703 : ((((((p3 ∨ p2) ∨ ((False → (p2 ∨ p3)) → (False → p5))) ∧ ((p3 → ((True → False) ∧ p1)) → p4)) → (p1 ∨ ((p4 → p4) ∨ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



