variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_311940646982742580207025882748 : (p2 ∨ (p3 ∨ (((((True ∨ (((p2 ∧ p2) → p3) → (p1 ∧ p5))) ∨ p2) ∧ (p1 ∧ (True ∧ True))) → (p3 ∨ True)) ∨ (False ∧ (p4 → p3))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
      -- Conjunctions on the left can always be decomposed.
      let h6 := h3.left
      let h7 := h3.right
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h3.left
      let h12 := h3.right
      -- Conjunctions on the left can always be decomposed.
      let h13 := h12.left
      let h14 := h12.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h15 =>
    -- Conjunctions on the left can always be decomposed.
    let h16 := h3.left
    let h17 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h18 := h17.left
    let h19 := h17.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114223061918645294328773918742 : ((((p1 ∨ p1) → (((True ∨ (p2 ∧ (False ∨ p1))) → (True ∨ p1)) ∧ (((p2 ∨ p3) ∧ p1) → p2))) → ((p3 ∧ p4) ∧ p3)) ∨ (False → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114193738851575534383323335503 : (((((((p1 ∧ p2) → (p1 ∨ (p1 → False))) → True) ∧ True) → ((p4 ∨ ((p2 ∧ True) ∨ False)) ∧ True)) → (p5 ∧ (p2 ∨ p1))) ∨ (p4 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258807847883546152269759047002 : ((True → False) → (p1 ∨ ((((False → ((p4 ∨ False) ∨ p5)) ∨ (True → (((p3 ∧ p5) ∨ ((False ∧ p3) ∨ (p4 ∧ p5))) ∧ p4))) ∧ p1) → p5))) := by
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
theorem thm_5_vars_53444812020084582883109468263 : ((((True ∨ (p3 ∨ p1)) ∨ ((((p4 ∧ p3) ∧ False) → p3) → p4)) → (((p4 → p3) ∧ (p2 ∧ (True → False))) ∨ (p4 ∨ (p2 ∨ p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52806484425915171526704992618 : ((((p1 ∧ (True ∧ (p4 ∨ (p1 ∧ p5)))) ∧ (p4 → ((p2 ∨ p3) ∧ p2))) → ((False ∧ (p1 ∨ (((p1 ∧ p1) → p1) ∨ p4))) ∨ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148647204886590869775884542357 : ((((((p4 ∨ p3) ∨ False) ∨ p5) ∧ (p1 ∧ p1)) ∧ (((p1 ∧ False) → (True ∨ True)) ∨ (True ∧ (p3 ∨ p2)))) ∨ (True ∨ ((True ∨ p5) ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184465722072518476833912639801 : ((((((p1 ∧ (p3 → False)) ∧ p2) ∨ p5) ∧ False) ∨ (p1 ∧ True)) ∨ ((p4 ∨ ((False ∨ False) ∧ p2)) → ((False ∧ (p2 → p2)) ∨ (p4 ∨ p4)))) := by
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
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- False on the left can always be used.
      apply False.elim h6
    case inr h7 =>
      -- False on the left can always be used.
      apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_666864925069405187141915880422 : (((((True ∨ (True ∧ ((p3 ∧ True) → p4))) ∧ (p2 ∨ ((p5 ∨ False) ∧ ((p5 ∨ p3) ∨ ((p2 ∧ p4) → True))))) ∧ ((p1 ∧ p2) ∨ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342404106264755476646210126628 : (p2 → ((p3 ∨ (((((p2 → p3) ∧ (p1 ∨ p2)) ∧ (False ∨ (p1 ∨ p2))) ∧ p5) ∨ p3)) ∨ ((((p1 → p4) ∨ p2) → p5) ∨ (p3 ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206532380886498277680455674659 : ((True → ((p1 ∨ (True ∧ p4)) ∨ False)) ∨ (((True ∧ (((p5 ∧ ((p1 → p5) ∧ True)) ∨ True) ∨ ((True ∨ p5) ∧ p2))) ∨ p3) ∧ (False ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116465279317195255681654390818 : (((False ∧ p2) ∧ ((p3 ∧ ((True ∨ (((False ∧ p3) → p4) → (p1 ∨ p2))) ∧ (p3 → (p3 ∧ (p4 → False))))) → (False ∨ p5))) ∨ (True ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49017406065866814382550521309 : ((((((p3 ∨ (p5 ∨ (True ∧ p5))) ∨ (((p1 ∧ False) ∨ p2) ∨ ((True → p2) → p3))) ∨ (p2 → p1)) → p2) ∨ (p1 → (p3 ∨ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258845830346338002093508627611 : ((True → p1) → ((False ∧ (((p5 → (False ∧ True)) → ((p4 → False) ∧ p3)) ∨ (p2 ∧ p4))) ∨ ((False ∧ p5) → (((True → p2) ∧ False) ∧ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- False on the left can always be used.
  apply False.elim h4
  -- Conjunctions on the left can always be decomposed.
  let h6 := h2.left
  let h7 := h2.right
  -- False on the left can always be used.
  apply False.elim h6
  -- Conjunctions on the left can always be decomposed.
  let h8 := h2.left
  let h9 := h2.right
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350064745260281094236722391020 : (p4 → ((((p3 → ((True → (p5 ∧ p5)) ∨ (p4 → (((True ∨ True) ∨ (p2 → (False → p5))) → (p3 → False))))) ∧ p4) ∨ (True ∧ p4)) ∨ p3)) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_352893162418337219032861803243 : (p4 → (True ∧ (((p4 → (False ∧ True)) ∧ p4) → ((((p5 → ((p2 ∨ p4) ∨ False)) → (p2 ∧ p5)) ∨ (p3 ∨ p4)) ∨ ((False → p1) ∨ p2))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65361235375904623591658435101 : ((p3 ∨ (((False ∧ (p1 → (False → False))) ∨ (((False ∧ True) ∨ True) → p5)) ∧ ((False ∧ p3) ∧ (p4 ∧ (p2 → ((p1 ∧ p1) ∧ p4)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185558699286264520170216167913 : ((p4 ∨ (((p3 ∨ p1) ∨ (p1 ∧ p4)) ∧ ((p3 ∨ p3) ∨ True))) ∨ ((False ∧ (p5 ∧ p3)) → ((p1 → (p1 ∧ False)) ∨ ((p3 → p4) ∧ True)))) := by
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
theorem thm_5_vars_52001805766867180441656261684 : (((p1 ∧ (((p4 ∨ ((p2 ∧ (p3 ∧ p5)) ∧ False)) ∧ ((p2 ∧ p2) ∧ False)) ∧ True)) ∨ ((p3 → (p3 ∧ ((p3 ∨ False) ∨ p1))) ∨ p1)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_88912523074873635860434114785 : (((p3 ∨ ((p4 → True) ∨ False)) → (((p1 ∨ True) ∧ ((p3 ∧ (((p2 ∨ p1) ∧ p1) → False)) → ((p1 ∨ True) ∨ p2))) ∧ (True ∧ p3))) → p3) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p3 ∨ ((p4 → True) ∨ False)) := by
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
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57647589871824944785390424555 : ((((p1 ∨ True) ∨ False) → ((((p4 ∨ (p2 ∨ ((p1 ∨ p2) ∨ p2))) → False) → ((p1 ∧ ((p5 ∨ True) ∧ False)) ∨ (False ∧ False))) ∧ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351625527146986331751988004008 : (p4 → ((((((True → p2) ∨ ((p5 → p4) → (p5 ∨ False))) ∧ (p4 → p2)) ∧ p3) ∨ p5) ∨ ((False ∨ True) ∨ (((p4 ∨ p3) ∨ p3) ∨ p3)))) := by
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
theorem thm_5_vars_185223550809442698917971684749 : ((False ∧ (((p4 → (True → p2)) ∨ ((p4 → p1) ∨ p1)) → p2)) ∨ (False → ((p3 ∧ p4) ∧ ((p3 ∨ (p3 → False)) ∧ ((False → p4) ∨ True))))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111600097878876421104727626295 : ((((((False ∧ ((((p3 ∧ (p1 → (((p2 ∨ False) ∨ p2) → p1))) ∧ True) ∧ (p1 → p1)) → False)) ∧ p5) ∧ p3) ∨ p3) ∨ True) ∨ (True → False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256605657160735602041361778105 : ((p1 ∨ True) → ((((p4 → p2) → p1) ∨ p3) ∨ (((p3 → (((p1 → p1) ∧ p2) → p4)) ∨ p1) ∨ ((False ∧ p1) ∨ (True ∨ (p1 ∨ p2)))))) := by
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
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
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
theorem thm_5_vars_773516427498396116171391187762 : (((False ∨ ((((((p4 ∨ (p3 → (p5 → (p1 ∧ True)))) ∨ ((p2 ∧ p4) ∨ False)) ∨ False) ∧ p2) ∧ (p4 ∨ ((p1 ∧ p4) ∧ p4))) ∨ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164798927508681076010922393426 : ((((p3 ∨ (p4 ∧ True)) ∧ ((p2 ∧ (p3 ∨ (True ∧ p4))) ∧ ((True ∧ p2) → p2))) ∨ False) ∨ ((False → (p4 ∧ (p4 ∨ False))) ∨ (p2 ∧ p1))) := by
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
theorem thm_5_vars_737726437881012993273175573496 : ((((p5 → p5) ∧ (((p4 ∧ ((p3 → (((p5 ∨ p4) → p2) ∨ (((False ∨ p4) ∨ p3) → p5))) ∨ p4)) ∧ p4) ∨ ((p4 ∧ True) → True))) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135274898866171934404680573265 : (((p3 ∨ (p5 ∨ (((((p5 ∨ p5) → p3) → ((True ∨ p1) ∨ (p5 → p3))) ∨ True) → (p2 → True)))) → (p2 ∧ p4)) ∨ (p2 ∨ (p4 → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_670644822791313109225657493574 : (((((True ∨ p5) → ((p1 ∨ ((p3 ∨ ((p5 → (p5 ∧ (True → p5))) ∧ False)) ∨ p4)) → (p3 ∨ (p1 ∨ True)))) ∨ (p5 → (True ∨ True))) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_724815459973128002509491352409 : ((((p4 ∨ (p5 ∧ p5)) ∧ (((False ∧ False) → (True ∨ p1)) → (p5 → ((False ∧ p2) ∨ ((p3 → ((False ∧ p4) ∧ p5)) → (False ∨ p4)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204154647817946697544675323866 : (((((p5 ∧ p1) ∨ p4) ∨ p2) ∧ p1) ∨ (((p2 ∧ p4) ∧ (p1 → ((p2 ∨ p3) → p5))) → (False → ((p4 ∨ (p4 → (True ∨ p2))) → p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- False on the left can always be used.
    apply False.elim h2
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_808417616024692017327099251226 : (((p4 → (p2 ∨ ((((((p5 ∨ (True ∨ p3)) ∧ (p2 → p3)) ∨ ((p5 → True) → p4)) → (p5 → (p1 → False))) ∧ p2) ∨ (False ∨ True)))) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
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
theorem thm_5_vars_159421666334253807394093103654 : ((((p4 → ((p1 ∨ p4) ∧ ((p4 → p3) ∨ (p4 ∨ ((False ∨ p2) → False))))) ∧ (p3 ∨ p2)) ∧ p5) → ((p3 → False) ∨ (p5 ∧ (p2 ∨ p5)))) := by
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
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h3
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_792507651839182090005235227088 : (((True → ((False ∧ (((p1 → p1) ∧ p2) → ((False ∨ p2) ∨ p4))) ∨ (((True → p1) ∧ True) ∧ ((p2 → True) → ((True ∨ p5) ∨ p4))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190357029968663708713222695350 : ((((p4 → (p2 ∨ p1)) → ((p1 → False) ∨ p2)) ∨ True) ∨ (((False → False) → ((p1 ∨ True) ∨ (p4 ∧ ((False ∧ p1) ∧ (True → p1))))) ∨ True)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_94416503028990527788712300620 : ((p2 ∧ ((True ∨ p1) → ((((p3 → (p3 ∨ (p5 ∨ (p4 ∨ False)))) ∨ p1) ∧ p3) ∧ (((p2 → True) ∧ ((p4 → p1) → True)) → p5)))) → p5) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : (True ∨ p1) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h7 : ((p2 → True) ∧ ((p4 → p1) → True)) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h8
    -- True on the right can always be proven directly.
    apply True.intro
    -- Implications on the right can always be decomposed.
    intro h9
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h10 := h6 h7
  -- One of the premise coincides with the conclusion.
  exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_3196499776667747861460740277 : ((p3 ∧ False) ∨ (((False ∨ ((p3 ∧ (p2 → p4)) ∨ (p1 ∨ ((p5 ∨ (p1 ∧ True)) → p2)))) ∨ ((False ∧ p3) → (True ∧ False))) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_335698710702434676587507603802 : (p1 → (((((p1 → (True → (((p2 ∨ False) → False) ∨ (p2 ∧ p2)))) ∨ p1) → ((p1 → p5) ∧ (False ∨ ((False ∨ p1) ∧ p1)))) ∨ True) ∧ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317140567264879107441198978874 : (p3 ∨ (p5 → (p3 ∨ ((p5 → (((((True ∨ p2) ∧ p3) → p5) ∧ p2) → False)) ∨ (True → (True → ((p2 ∧ True) ∨ (p5 ∨ (p3 ∨ p3))))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_935467176468317906630675206889 : (((((p4 ∨ (False → (True → p3))) ∨ (p3 ∧ p2)) → ((p4 → (p3 ∨ ((p5 → p2) ∧ ((True ∨ (p3 ∧ False)) ∨ (p4 ∨ p3))))) ∧ p5)) → p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p4 ∨ (False → (True → p3))) ∨ (p3 ∧ p2)) := by
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
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h2
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- One of the premise coincides with the conclusion.
  exact h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137753337636880153757630755547 : ((p2 ∨ ((p5 ∧ ((((True → (((p2 ∨ p5) → (p1 → (p2 → p3))) → (p5 → p1))) ∨ p5) ∨ p5) ∧ False)) ∨ True)) ∨ ((p2 ∨ p2) → True)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336465769754323814803721019597 : (p1 → ((p1 → ((p3 → (p1 ∧ (p4 ∨ p2))) ∨ (p1 → ((((p3 → p2) ∧ (p5 → p5)) ∧ (((p2 → True) ∧ p2) ∨ p3)) ∨ p2)))) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_804006259772465073479036858977 : (((p3 → ((((((((False ∨ (True ∨ (False ∧ True))) ∨ p2) ∨ p2) ∧ p1) ∧ True) → True) → (True → (p4 ∨ p5))) ∨ (True → (p3 ∨ p3)))) ∨ p5) ∧ True) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_710426979461566225809728482712 : ((((((p2 ∨ p4) ∨ (True ∨ p4)) → False) ∧ (p2 ∧ ((((((p5 ∧ (False ∨ p5)) ∨ p1) → (True ∨ p5)) ∧ (False ∧ True)) → p2) ∧ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206244694263534028716954397585 : ((False ∨ ((False ∧ (False ∨ p1)) ∧ p4)) ∨ ((((False → (p5 ∨ p2)) ∧ ((p1 ∨ p3) ∧ True)) → p1) ∨ (True ∨ (((True → True) → False) ∧ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_140557663540617667193924024839 : ((((True ∧ ((p1 ∨ p2) ∨ p5)) ∧ (((True → p2) ∨ ((p5 ∧ p4) ∨ p5)) ∧ True)) ∨ (((p1 ∧ p3) ∨ p1) → p3)) → ((p3 ∧ p1) ∨ True)) := by
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
    cases h6
    case inl h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Conjunctions on the left can always be decomposed.
        let h9 := h4.left
        let h10 := h4.right
        -- Disjunctions on the left can always be decomposed.
        cases h9
        case inl h11 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h12 =>
          -- Disjunctions on the left can always be decomposed.
          cases h12
          case inl h13 =>
            -- Conjunctions on the left can always be decomposed.
            let h14 := h13.left
            let h15 := h13.right
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h16 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
      case inr h17 =>
        -- Conjunctions on the left can always be decomposed.
        let h18 := h4.left
        let h19 := h4.right
        -- Disjunctions on the left can always be decomposed.
        cases h18
        case inl h20 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h21 =>
          -- Disjunctions on the left can always be decomposed.
          cases h21
          case inl h22 =>
            -- Conjunctions on the left can always be decomposed.
            let h23 := h22.left
            let h24 := h22.right
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h25 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
    case inr h26 =>
      -- Conjunctions on the left can always be decomposed.
      let h27 := h4.left
      let h28 := h4.right
      -- Disjunctions on the left can always be decomposed.
      cases h27
      case inl h29 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h30 =>
        -- Disjunctions on the left can always be decomposed.
        cases h30
        case inl h31 =>
          -- Conjunctions on the left can always be decomposed.
          let h32 := h31.left
          let h33 := h31.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h34 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
  case inr h35 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_730701891755687394945288652920 : ((((p3 ∧ (p5 ∨ False)) → ((p3 ∧ (p3 ∨ (True ∨ p5))) → ((p3 → ((p2 ∨ (False ∨ p3)) ∧ (p1 ∧ False))) ∨ (p3 ∨ (p1 → p4))))) ∨ p4) ∧ True) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h1.left
    let h7 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h9 =>
      -- False on the left can always be used.
      apply False.elim h9
  case inr h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h1.left
      let h13 := h1.right
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h14 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h12
      case inr h15 =>
        -- False on the left can always be used.
        apply False.elim h15
    case inr h16 =>
      -- Conjunctions on the left can always be decomposed.
      let h17 := h1.left
      let h18 := h1.right
      -- Disjunctions on the left can always be decomposed.
      cases h18
      case inl h19 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h17
      case inr h20 =>
        -- False on the left can always be used.
        apply False.elim h20
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135087437216919871107325486564 : ((((((p4 ∨ (p2 ∨ ((p4 → p5) ∨ False))) ∨ (p4 → p5)) ∨ False) → ((False ∨ (p1 ∧ p5)) ∨ True)) ∨ (p3 → p5)) ∨ (p2 ∧ (p5 ∧ True))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h5 =>
        -- Disjunctions on the left can always be decomposed.
        cases h5
        case inl h6 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h7 =>
          -- Disjunctions on the left can always be decomposed.
          cases h7
          case inl h8 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h9 =>
            -- False on the left can always be used.
            apply False.elim h9
    case inr h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h11 =>
    -- False on the left can always be used.
    apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_499848522063961121244558754921 : (((((p5 ∨ p4) ∨ False) ∨ ((p3 → (((p4 ∧ p5) ∧ False) → p1)) ∧ (((p4 → False) ∨ p2) ∨ ((p2 ∧ p3) → ((p2 ∧ p5) → p2))))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- False on the left can always be used.
  apply False.elim h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h7
  -- Implications on the right can always be decomposed.
  intro h8
  -- Conjunctions on the left can always be decomposed.
  let h9 := h8.left
  let h10 := h8.right
  -- Conjunctions on the left can always be decomposed.
  let h11 := h7.left
  let h12 := h7.right
  -- One of the premise coincides with the conclusion.
  exact h11
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64003947864168026497991244001 : ((False ∨ (((((p4 ∨ True) ∧ ((((p5 → True) ∨ p4) ∨ p3) → p4)) ∧ p3) ∨ (p1 ∧ (False ∧ ((p3 ∧ p1) ∧ False)))) ∧ (p4 ∧ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_603147153605266635241077375958 : ((((p2 ∨ (((p4 ∧ (((p1 → ((True ∧ p1) → p4)) ∧ p2) ∨ (True ∨ (p3 → p2)))) → ((p5 ∧ (p5 → p5)) → p5)) → p3)) ∧ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149926990609806052146794199212 : ((p3 ∨ ((p5 ∨ ((False → (False ∨ p1)) ∧ ((p1 ∧ p5) ∨ p3))) ∧ ((p4 → ((p4 ∨ p4) ∨ True)) ∨ p2))) ∨ (False ∨ ((p1 ∨ p1) → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133801141462219796282123740096 : ((((True ∧ (p2 ∨ True)) → (p2 ∨ (((p4 → ((((p2 → p4) ∧ p4) → p5) ∧ p1)) ∧ (p3 ∧ p3)) ∧ p3))) ∧ False) ∨ (True → (False → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171987055562157185779100726535 : ((((((p5 → (False ∧ (p4 ∨ False))) → (p2 ∧ p2)) → p4) ∧ p4) ∨ (p3 → p2)) ∨ (((True ∧ p5) → ((p3 → (p5 ∨ p2)) ∨ p1)) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h4
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263120276300425101292073231340 : (True ∧ ((((True ∨ ((p2 ∨ False) ∨ (p4 → True))) → (p1 → (True ∨ p5))) ∧ (p3 ∧ ((p5 → p2) ∧ (p5 ∧ (p1 ∧ p4))))) ∨ (p3 ∨ True))) := by
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
theorem thm_5_vars_782572882478111151399088464894 : (((p3 ∨ ((p3 ∨ (((p3 ∧ ((p1 ∧ p4) ∨ p5)) ∨ (True → p3)) ∧ ((((p4 ∧ p3) ∨ p3) → p5) ∧ (p3 → (p1 ∧ p4))))) ∨ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_512231773354594435685039737051 : ((((p2 ∧ p3) ∨ ((False → p5) ∧ (p1 → (((((p2 ∧ p2) → p2) ∧ (p5 ∧ ((p1 ∨ p5) ∧ ((p5 → p3) ∧ p5)))) → p2) ∨ True)))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57721322687043100726825182728 : ((((False ∨ True) → p3) → ((p3 ∨ ((p5 ∧ (True → (p4 → p4))) → (p5 ∨ p4))) ∧ (p2 → (((p4 ∧ True) ∧ (p4 → False)) ∨ p2)))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (False ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156813414394467231043176722704 : (((p1 ∨ (p5 → ((p5 ∨ (False ∧ False)) → (p5 ∧ (p5 ∧ ((False ∨ (p1 ∨ True)) ∨ False)))))) ∧ p2) ∨ (((p5 ∨ p1) ∧ p1) ∨ (True ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_654020639543228045949328426609 : (((((p1 ∨ (p5 ∧ ((False ∨ (p2 → (p3 ∧ (p1 ∨ False)))) → (((False ∨ True) ∨ (True → True)) ∧ (p3 → p5))))) ∧ False) ∨ (p4 → p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193270696638583454262292341407 : (((p4 → (False ∧ p5)) ∧ ((p4 → (p1 ∧ p1)) ∧ p1)) → ((((True ∨ ((False → p1) → (p4 ∧ p2))) ∧ p5) ∧ (p4 ∨ p4)) ∨ (p2 ∨ True))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_594492479692128541546281719761 : ((((((((False → True) → (p2 ∨ p3)) → ((p1 → (p5 ∧ False)) ∨ p3)) ∧ (p1 ∧ p5)) ∨ ((((False ∧ False) → p1) → p1) → True)) ∧ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177945296581974951938972606510 : ((((False ∨ (p1 ∨ False)) ∨ (p4 ∨ (True → (p1 ∨ (True → True))))) ∨ p2) ∨ (((((False ∧ (p3 → p1)) ∧ (p1 ∨ p5)) ∨ p5) → p4) ∨ p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_66596226352431734364552607349 : ((True → (((p4 ∨ (p4 ∨ ((True ∧ (True ∨ True)) ∨ (((p4 ∨ ((p1 ∧ p3) ∧ p5)) ∨ True) ∧ p1)))) ∨ p1) → ((p2 ∨ p3) → p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49524860026656434003179309553 : (((((((True ∨ (p3 → (p2 ∨ True))) → ((p1 ∧ p3) ∧ (p4 → True))) ∨ (p4 ∨ False)) → p1) ∨ (p5 ∨ p3)) → (False ∨ (p2 → p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_251661319741403347697328105349 : ((p3 → p2) ∨ ((p4 ∧ ((p2 ∨ ((p1 → p5) → p2)) ∧ (p5 → ((((p1 ∨ p2) → p4) ∨ (((False → p2) ∧ p5) ∨ False)) ∨ p1)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_699006489691947854848606643209 : ((((False ∨ ((p2 ∨ p4) ∨ (((p3 ∧ p5) ∨ True) ∨ (True ∨ True)))) ∨ (((p5 → p3) → p2) → ((p4 ∨ ((p1 → p1) ∧ False)) ∨ p3))) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_749093484078393676537452345110 : ((((p5 → False) → (((False ∨ p2) → (((p2 → p3) ∨ ((True → p2) ∧ False)) → (((True → (False ∧ False)) ∧ p1) ∧ (p3 ∨ p3)))) ∨ True)) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_646031836023702607224406638103 : ((((True → ((p1 ∧ p3) ∨ (p2 → ((((p4 ∧ (p3 → (p4 → (p4 ∧ p2)))) ∧ (p4 ∨ ((p5 ∧ p4) ∧ p5))) ∨ p1) ∨ p3)))) → False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_610252562670585699114468302035 : (((((((p1 → ((p4 → p5) ∨ (True ∨ p4))) → ((((p4 ∨ (p3 → p3)) ∨ p3) ∧ ((p3 → p3) → p3)) → False)) ∨ True) → p1) ∨ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208058578698133674385769587725 : (((p2 ∨ (False ∨ p5)) ∨ (p3 ∨ p4)) → (p2 → (((p5 ∧ p2) ∨ p5) ∨ (((True ∧ ((True ∨ p3) → (True ∧ (True ∨ p2)))) → p2) ∨ p3)))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h5
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- False on the left can always be used.
        apply False.elim h9
      case inr h10 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h10
  case inr h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h12
    case inr h13 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h14
      -- Conjunctions on the left can always be decomposed.
      let h15 := h14.left
      let h16 := h14.right
      -- One of the premise coincides with the conclusion.
      exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65953531799342299700603237747 : ((p4 ∨ (p3 ∨ (((p5 ∨ p5) ∨ p2) ∧ (((True → p4) ∨ (p4 ∨ ((True ∨ ((p3 ∨ (p2 → p4)) ∧ p1)) → (p5 ∨ p3)))) ∧ p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116209496549619239525357429138 : ((((True ∧ p1) ∨ p1) ∨ (p4 ∨ ((((p2 → (p1 → (p3 ∧ p2))) → p3) ∧ p5) ∧ (True ∧ (True ∨ (p2 ∨ (p2 → True))))))) ∨ (p2 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138443390526734370775416442901 : ((p5 → ((p2 → (p3 → p2)) ∧ ((p1 ∧ ((((p5 ∧ (True ∨ p1)) ∨ p4) → (p3 ∧ p4)) → (p1 → True))) → p4))) ∨ ((p3 ∧ False) → p1)) := by
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
theorem thm_5_vars_148361874584015324548105046663 : (((p1 → ((True → (True ∧ False)) ∨ ((False ∧ ((p4 ∧ False) → p5)) → p3))) ∧ ((p4 ∨ (p1 ∧ False)) ∧ p1)) ∨ (p1 → ((p3 → p3) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_616775791639269270542409908515 : ((((((p5 ∨ p3) → ((p3 ∧ (False ∧ True)) ∧ (False → True))) ∨ ((p5 → (((p2 ∨ p5) ∨ (False ∨ (p1 ∨ False))) → p1)) ∨ p2)) ∨ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_723098154645985292801846239272 : (((((p4 ∨ False) ∨ p2) ∧ ((p3 → ((((p2 ∨ False) ∨ ((p2 ∨ p4) ∧ p2)) ∨ p5) → (p2 → False))) ∨ ((p4 ∧ True) ∧ (False ∨ True)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_577285505780978421635560934295 : (((p3 → ((((((p5 → (((((p2 ∨ p1) → p4) ∨ p1) ∨ p2) ∨ True)) ∧ (p2 ∧ False)) ∧ p5) ∨ p4) ∨ (p5 ∨ True)) ∨ (False ∧ p3))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148001605516152439413928172058 : ((((True → (((p1 ∧ (p1 ∨ ((p5 ∨ p4) ∨ ((p2 ∨ True) ∧ p3)))) ∨ True) ∧ p1)) → p2) ∨ (False → p4)) ∨ (True ∨ ((True ∨ True) → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43316881568541660533672017569 : ((((((p5 ∨ p2) → ((True ∨ ((p5 → ((p5 ∧ p5) ∨ p3)) ∧ p1)) → (False → (((p3 → p2) ∧ p4) ∧ p3)))) ∨ False) ∨ p3) → p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49375980117575481188199349871 : (((p5 → (((p2 → True) ∧ (True ∨ p4)) ∧ ((((True → (p4 ∨ p4)) → False) ∨ (p1 ∧ p1)) → (p2 ∨ p2)))) ∨ ((True → p3) ∨ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328100786654370091974751465914 : (True → (((False ∧ ((((((True ∨ (p1 ∧ p5)) ∧ (True ∧ (p1 → True))) ∧ p2) → p5) → False) ∧ (p5 ∧ False))) ∨ p4) ∨ ((p1 ∨ p4) → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46913224122990611281041941859 : (((((True ∧ ((p5 → ((p4 ∧ (p5 ∧ p3)) ∧ (p5 ∨ False))) ∧ p2)) → ((True ∨ (True → (p2 ∨ p1))) → p4)) ∨ p5) ∨ (p5 ∨ True)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_803830557915366112693852120383 : (((p3 → (((p1 ∨ (p2 ∨ (p2 ∨ (p3 → (p2 ∨ p4))))) ∨ (True → (p4 ∨ ((p3 ∨ True) ∧ ((True → p5) ∨ True))))) ∨ (True → p3))) ∨ p1) ∧ True) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_750479983987907095749870067969 : (((True ∧ (((False ∧ (((True → ((((p1 ∧ False) → (False ∧ p4)) → (p2 → p3)) ∨ p4)) → p3) ∨ True)) → p1) → ((False ∨ p2) ∨ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_591145243186989048509085679412 : (((((((((((p5 → p3) → p5) → False) ∧ p1) ∧ (p2 → p3)) ∧ (False ∧ ((p1 → (p1 → p4)) ∨ True))) ∨ p2) ∧ (p4 ∧ p5)) ∧ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206085940572580383627163154211 : ((p3 ∧ (p2 ∧ (True → (True ∨ p5)))) ∨ ((((p3 → p3) → False) ∧ (p4 → ((False ∨ ((p1 ∧ (p5 → p3)) → (p3 ∨ p2))) ∧ p2))) → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (p3 → p3) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h4
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150606778886836424842952934096 : (((True ∧ (((p3 → ((p1 → p1) → (((False ∧ False) ∧ p1) ∧ p4))) ∧ ((p3 ∧ p1) → p2)) ∨ True)) ∧ p1) → ((p2 ∨ p1) ∨ (True ∧ p4))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h9 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47580482212291201263733332545 : (((p1 → (False ∨ (p2 ∧ ((p5 ∧ p1) ∧ ((p3 ∨ (p2 ∧ ((p5 ∨ ((p1 ∧ p2) ∧ False)) → p4))) → (p4 ∧ False)))))) ∨ (True → True)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200351425515122413628623359367 : (((p5 ∨ p5) ∧ (p4 → (p3 → (p3 ∧ p2)))) → (p2 ∨ (p1 ∨ (False → (p2 → ((p4 → (p3 ∨ (p2 ∧ True))) ∧ (p2 → (False → p2)))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Implications on the right can always be decomposed.
    intro h6
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h7
    -- False on the left can always be used.
    apply False.elim h5
    -- Implications on the right can always be decomposed.
    intro h8
    -- Implications on the right can always be decomposed.
    intro h9
    -- False on the left can always be used.
    apply False.elim h9
  case inr h10 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h11
    -- Implications on the right can always be decomposed.
    intro h12
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h13
    -- False on the left can always be used.
    apply False.elim h11
    -- Implications on the right can always be decomposed.
    intro h14
    -- Implications on the right can always be decomposed.
    intro h15
    -- False on the left can always be used.
    apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117805443463438292449569704568 : ((p4 ∧ ((p3 ∨ (p2 ∧ p2)) ∧ (p1 ∧ (True ∧ (True ∨ ((p3 ∨ ((((p2 ∧ p2) ∧ (p2 → p3)) ∨ False) → False)) → True)))))) ∨ (True → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56272871583823210608729715173 : (((p4 → ((p2 → p2) ∧ p5)) ∨ ((((True → (p2 ∧ (p1 → p1))) ∨ (p1 ∨ ((p4 ∧ p4) ∧ (p2 → p2)))) → p5) → (p1 ∧ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47939412580995316160387950230 : (((((((p1 ∨ (((p4 ∧ False) ∨ (p1 ∧ p2)) → p5)) ∨ p2) ∧ (p2 ∨ p3)) ∧ (True → p5)) ∨ ((p5 ∧ True) ∨ False)) → (p3 ∧ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50147496721484196939341579919 : (((p1 → ((((False ∨ (True ∨ (((False ∨ p4) ∨ p5) ∧ p4))) → False) ∨ (True ∨ (p2 ∧ False))) → p2)) ∧ ((p3 ∧ True) → (False ∨ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_463174799884833647440771668678 : ((((((True ∧ p4) ∧ p3) ∧ ((p5 ∧ ((True → False) ∨ (False → (p5 ∨ p1)))) → p3)) ∨ ((False ∨ True) ∨ (False ∨ ((True → False) ∧ p4)))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118586856625019189238175864092 : ((p4 ∨ (((False ∧ (((p3 ∨ p5) → p2) ∨ ((p3 ∨ p4) ∧ (((False ∧ p1) → p5) ∧ p1)))) → (p4 ∨ (p4 → p4))) → p4)) ∨ (p5 → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110917069772394037395289405809 : ((((p3 ∨ ((((p3 → p4) ∨ p4) ∨ (p2 ∨ ((p2 ∧ (p2 ∧ p5)) → (((p5 → p2) ∧ p5) → p4)))) ∨ False)) → p3) ∧ p3) ∨ (False → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_618889308143259775511847218450 : (((((False → (p4 ∨ False)) ∧ (((((p1 ∧ p5) → (False → (p4 ∧ True))) ∨ p4) ∨ (p4 → (True → False))) → ((False → True) → p5))) ∨ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_826819689940831682657284510935 : (((((p4 → p2) → (((False ∧ True) ∨ (((p3 ∨ True) → p5) ∧ (p4 → p5))) ∧ ((p2 ∧ ((p2 ∨ p5) ∧ False)) ∧ (p3 ∧ True)))) ∧ p2) → False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (p4 → p2) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h4
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- We need to get the left conjuct of h7 based on <expert-advice>.
  let h8 := h7.left
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- We need to get the right conjuct of h9 based on <expert-advice>.
  let h10 := h9.right
  -- False on the left can always be used.
  apply False.elim h10
  -- True on the right can always be proven directly.
  apply True.intro



