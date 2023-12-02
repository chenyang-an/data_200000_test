variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_196818904218533468305452213750 : (((False ∧ (((p2 ∨ p5) ∨ p2) → p2)) ∧ p1) ∨ (((p3 ∨ False) ∧ False) ∨ (p4 ∨ (p1 → ((((p1 → True) → (p5 ∧ p5)) → p5) ∧ p1))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (p1 → True) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h3
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- One of the premise coincides with the conclusion.
  exact h6
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_623823822858238984370305048706 : ((((p1 ∨ ((p1 ∧ p2) ∨ (((True → p3) ∨ False) ∧ ((((True ∨ p1) → p5) ∨ ((p2 → (True ∧ (False ∧ p3))) ∧ False)) ∨ p3)))) ∨ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_261313524002453338068576046648 : ((p5 → False) → (((((((p3 → (p4 → p4)) ∧ False) ∨ p2) → (((p4 ∨ p3) ∧ p3) ∨ (p3 → (p3 → (False ∨ p2))))) → p4) ∨ p4) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_798262130105721771516288253320 : (((p1 → ((p2 ∧ ((p2 ∨ False) ∧ (p4 ∧ (p5 ∧ ((False ∨ p1) ∨ ((True → True) → p1)))))) ∨ ((p2 → p1) ∨ (p1 ∧ (p2 → p4))))) ∨ False) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165340217184042571744294543388 : ((((((p1 ∧ False) → p5) → (p4 ∧ p5)) ∨ (True → (p3 → p4))) ∧ ((False ∨ p1) → p4)) ∨ ((((False → p3) ∨ p2) → True) ∨ (False ∧ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112871387589816673512187672284 : (((((p1 ∨ False) → False) → (p3 → ((p5 → p1) ∨ (True → ((p2 → (False ∨ (p3 → ((p2 → p1) ∧ p3)))) ∧ p3))))) → p5) ∨ (True → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351541134227264351289233297674 : (p4 → (((p4 ∨ True) → (((False ∨ ((True ∧ p3) ∨ p5)) ∨ (p1 ∨ p3)) ∨ ((p3 ∧ p3) ∧ p3))) ∨ ((p5 ∧ False) ∨ ((p1 ∧ p1) ∨ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191726431368325359279547862683 : ((False ∨ ((((False ∨ (p5 ∧ p4)) ∧ p2) ∨ True) ∧ p5)) ∨ (p5 ∨ (False → ((((((p1 ∨ (p4 ∨ p4)) ∧ False) ∨ p2) → p4) ∧ p3) ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_264290861371193209013397663894 : (True ∧ ((((True → (p2 ∨ p1)) → False) ∧ p2) → (((p4 ∧ p2) ∧ (p4 ∨ (((p1 ∧ (p2 → p1)) ∧ p5) ∨ p5))) ∨ (p5 ∧ (True → p5))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (True → (p2 ∨ p1)) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h4
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_621795341746707172040920431935 : ((((p1 ∧ (((p5 ∧ (((False ∨ True) ∧ ((p1 → (p3 ∧ p1)) ∧ ((p5 ∧ p2) ∧ (p3 ∨ p3)))) ∧ p1)) ∧ p1) ∨ (p4 ∨ True))) ∨ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_631520518133574669754418506655 : ((((((p2 ∨ ((p2 ∨ (p1 → p1)) ∧ ((p1 ∨ False) ∨ (((p5 → (False → False)) ∨ p3) ∨ p2)))) ∧ (p5 → (p1 ∧ False))) → p5) → False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68612449448098916837202316423 : ((p4 → (((((False → p3) → ((((False ∨ p3) → p2) → (True ∧ True)) → p3)) ∧ (p4 → p4)) ∧ (((p1 → p2) → p1) → True)) ∨ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164749474401705189690115249500 : ((((((p1 → ((False ∧ ((p5 ∨ p5) → p1)) ∧ False)) ∨ p5) → p5) → (p4 ∧ p5)) ∨ False) ∨ (False ∨ ((True ∨ p1) ∧ (True ∨ (p3 ∧ False))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_481089372154861877969969249668 : (((((False → p3) ∧ (((p5 → p4) → p5) → False)) ∨ (((p5 ∨ (p2 ∨ True)) → p2) → (((p2 ∨ p4) ∨ p4) ∨ ((p3 ∧ p1) ∨ p2)))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p5 ∨ (p2 ∨ True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200453961084983898729232325684 : (((p1 → True) ∨ (((p3 → p1) ∧ p5) → p1)) → (((p5 ∨ (p4 → ((True ∧ (True ∨ False)) ∧ p5))) ∧ ((p2 → (p3 → p5)) ∧ p3)) ∨ True)) := by
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
theorem thm_5_vars_134773362077895378585146333928 : (((True ∧ (p4 ∨ (p1 ∧ ((p5 ∧ p3) ∧ ((p5 ∧ (((True ∨ p2) ∧ ((p3 ∧ p5) ∧ p4)) → False)) ∧ p3))))) → False) ∨ (p3 ∨ (p5 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136655558734715764542079518151 : (((p1 ∧ (p3 ∨ p1)) → ((False → (p3 → ((p4 ∧ ((p2 ∧ ((p4 ∧ p4) ∧ p2)) ∨ (p3 → p5))) → p4))) → p2)) ∨ ((True ∨ True) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_627644444944980708661904826128 : (((((((((((p4 → True) → (True → (p3 ∧ True))) → p3) → ((True → p5) → p2)) → p2) → False) ∧ ((True → True) → p4)) ∧ p2) → p5) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h6 : (((((p4 → True) → (True → (p3 ∧ True))) → p3) → ((True → p5) → p2)) → p2) := by
    -- Implications on the right can always be decomposed.
    intro h7
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h8 := h4 h6
  -- False on the left can always be used.
  apply False.elim h8
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_318095826595367855140745858076 : (p4 ∨ (((((((True ∨ p4) ∧ (p5 ∧ (p2 ∨ True))) ∧ p2) ∨ (p4 → True)) ∨ ((p3 ∨ (p4 → p4)) ∧ (p3 ∨ (p2 ∨ p4)))) → p3) → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((((True ∨ p4) ∧ (p5 ∧ (p2 ∨ True))) ∧ p2) ∨ (p4 → True)) ∨ ((p3 ∨ (p4 → p4)) ∧ (p3 ∨ (p2 ∨ p4)))) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_224144832879215253174799880786 : ((True → (True ∧ True)) ∧ (p3 → ((p1 ∧ ((p1 → (p4 ∨ p5)) → (((p5 ∨ (p2 ∧ p2)) ∨ (p4 ∧ p2)) → False))) ∨ (True ∨ (p4 ∨ p3))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110792610631067173638025963550 : ((((((p1 ∨ False) → (p2 → (p4 → (p5 → ((p3 ∧ (p4 ∧ p4)) ∧ (p4 ∧ (p4 ∨ (p1 ∧ p5)))))))) → False) ∨ p3) ∧ p4) ∨ (p1 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164845302554468425142672306745 : (((p4 ∧ ((p4 ∨ ((p2 ∨ ((p1 ∧ p3) → p1)) ∧ (p5 ∨ p3))) → (p2 ∨ p1))) ∨ p3) ∨ (p5 ∨ (p2 ∨ (True ∨ ((p5 ∧ p3) ∨ p3))))) := by
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
theorem thm_5_vars_135057130631730067276731369560 : ((((((p4 ∨ (p1 → (True ∨ (p3 ∨ ((p1 ∧ True) ∧ (False ∧ (p5 → p1))))))) → p5) → True) → p5) ∨ (True ∨ p1)) ∨ (p1 ∧ (p4 → True))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114110853708063250375217814963 : (((p1 ∨ (((((p1 ∧ p2) ∨ False) ∨ (p1 ∨ p3)) → (((True ∨ p3) ∨ p4) → p3)) ∨ (p3 → True))) ∨ (p5 ∨ (p4 ∧ p3))) ∨ (p5 ∨ False)) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158370277729782079619407565046 : (((p4 ∨ True) ∧ (True → (((p3 → True) → ((p4 → (False ∧ (False ∧ p1))) → p1)) → (p1 → p2)))) ∨ (((True ∨ True) → (p5 → p5)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_943900774961952116296280934529 : ((((True → ((p3 ∨ p3) ∨ p3)) ∧ ((((True ∨ ((((p2 ∨ (p3 → p1)) → False) → (p5 → (p5 ∧ p1))) ∨ p5)) → p1) ∨ p2) ∨ False)) → p3) ∧ True) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h6 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h7 := h2 h6
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Disjunctions on the left can always be decomposed.
        cases h8
        case inl h9 =>
          -- One of the premise coincides with the conclusion.
          exact h9
        case inr h10 =>
          -- One of the premise coincides with the conclusion.
          exact h10
      case inr h11 =>
        -- One of the premise coincides with the conclusion.
        exact h11
    case inr h12 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h13 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h14 := h2 h13
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h15 =>
        -- Disjunctions on the left can always be decomposed.
        cases h15
        case inl h16 =>
          -- One of the premise coincides with the conclusion.
          exact h16
        case inr h17 =>
          -- One of the premise coincides with the conclusion.
          exact h17
      case inr h18 =>
        -- One of the premise coincides with the conclusion.
        exact h18
  case inr h19 =>
    -- False on the left can always be used.
    apply False.elim h19
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_318614745184394986470711452126 : (p4 ∨ (((p2 ∧ (p1 ∧ p5)) ∨ ((True ∧ p5) → (((((False ∨ (False ∧ (True ∧ (True ∨ p3)))) ∨ p3) ∨ False) ∨ False) ∨ False))) ∨ (p3 → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_792968272123161382139819658738 : (((True → ((p3 → True) ∧ (p4 ∨ (p4 ∨ (p1 ∨ ((((((((p1 ∨ False) → p1) ∧ (True → p2)) ∧ p5) → True) ∧ p2) ∨ p1) ∧ False)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_745675725430526949240918433880 : ((((True ∨ p4) → ((p4 ∨ (((p5 ∨ (((p5 ∨ (False → p4)) → (False ∨ p2)) ∨ True)) → (p4 ∧ (True ∧ p4))) ∧ p3)) ∨ (p1 → p1))) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_588301647316031370542431414986 : (((((((p4 ∨ (p4 ∨ p3)) ∧ False) ∧ (p2 → ((p5 ∨ False) ∧ (p1 → ((False ∨ (p1 ∧ (p1 → (True ∨ p1)))) ∧ p5))))) ∨ p2) ∧ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_745700568161183549390030011177 : ((((True ∨ p4) → (p3 → ((((((p1 ∨ p4) → True) ∧ p2) → p5) → (((p4 → (True → p4)) → ((p3 → p4) ∨ False)) ∨ p3)) ∧ p3))) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h6 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h7 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_615908931846279424014385904551 : (((((p2 ∨ ((((p4 ∧ (True ∧ p4)) → (True ∨ (p1 → p5))) → p5) ∧ p3)) ∨ ((True ∨ True) → (True ∧ (p2 ∧ (False → p5))))) ∨ True) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_47034125663781929244162599694 : (((((((((p2 ∧ ((p1 ∨ (False ∧ p3)) ∨ p5)) → False) → p3) ∨ False) ∨ (p3 ∨ (p5 ∧ True))) ∨ p4) ∧ (p5 ∨ p4)) ∨ (False → p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_657828469707944468613183782978 : ((((False ∧ ((True ∧ (((p1 → p1) → (False ∧ p4)) ∨ (p3 ∨ ((p5 ∨ False) → ((True ∧ True) → p5))))) ∧ (p5 ∨ p2))) ∨ (p2 → p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_352459512809263276033625915236 : (p4 → (((False ∧ False) → True) → ((((p2 ∧ ((p3 → True) ∧ (p2 → (p3 ∧ p4)))) ∧ (p1 ∨ p5)) ∨ False) → ((True → p3) ∨ (p3 ∨ False))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h11 =>
      -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
      have h12 : p2 := by
        -- One of the premise coincides with the conclusion.
        exact h7
      -- We have shown the premise of h10, we can now drive its conclusion.
      let h13 := h10 h12
      -- We need to get the left conjuct of h13 based on <expert-advice>.
      let h14 := h13.left
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h14
    case inr h15 =>
      -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
      have h16 : p2 := by
        -- One of the premise coincides with the conclusion.
        exact h7
      -- We have shown the premise of h10, we can now drive its conclusion.
      let h17 := h10 h16
      -- We need to get the left conjuct of h17 based on <expert-advice>.
      let h18 := h17.left
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h18
  case inr h19 =>
    -- False on the left can always be used.
    apply False.elim h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204113485981507889232333580297 : (((((p5 ∨ p2) ∨ False) ∧ p2) ∧ p4) ∨ (p1 ∨ ((p4 ∨ p4) → (p4 ∧ ((True → (p3 ∧ p3)) ∨ (False → (((p3 ∧ p4) → p5) ∨ p2))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- False on the left can always be used.
    apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184189413325440869977025911812 : ((((((p2 ∧ p5) → (p2 ∧ (False → p4))) ∧ p1) ∧ p2) → p5) ∨ ((p2 → ((p2 → (p3 ∧ (False → p1))) ∨ False)) → ((True ∨ p4) ∨ p1))) := by
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
theorem thm_5_vars_113058375024713234630677452299 : (((p2 ∨ ((p3 ∨ (p3 ∨ (False ∧ ((True ∧ (((p4 → (p2 ∧ p1)) → p5) ∧ (False → p2))) ∧ False)))) → (True ∧ False))) → p5) ∨ (True ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152392285349446999429696936469 : (((((True ∧ p5) ∨ p1) → p5) → (((p3 ∨ (False ∧ ((p3 → p3) → (False ∧ p2)))) → p5) ∧ (p2 ∧ p2))) → (p5 → ((p5 → p1) ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_127727344033554860712746696182 : ((True → (((((p4 ∧ p5) ∨ ((p5 → p2) → False)) → (True → (((p3 → True) → p2) → (p2 ∧ p5)))) ∨ (True → p4)) ∧ False)) → (p4 ∨ p2)) := by
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
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137339047116743889689813275541 : ((p2 ∧ (p5 ∨ (p4 ∨ (((p1 → ((p3 → (p5 ∨ p5)) → True)) → ((p4 ∨ (p5 → True)) ∨ False)) ∧ (False ∧ p1))))) ∨ (p1 → (False ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37994891018369297010107993667 : (((((p2 ∧ (False → (False ∧ p1))) → (False ∧ (p4 ∧ (((False ∧ False) ∧ ((p4 → p5) ∨ p1)) ∨ (True ∨ True))))) ∨ (p2 → p1)) ∧ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150070426214014512655918440572 : ((True → ((p2 ∧ (p5 ∨ ((p5 ∧ p4) ∨ p2))) ∨ (p3 ∨ ((p5 ∧ False) → (p5 ∧ (p1 → (p4 → True))))))) ∨ (p2 ∨ (p1 ∧ (p2 ∨ p5)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
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
  -- False on the left can always be used.
  apply False.elim h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- Implications on the right can always be decomposed.
  intro h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53235344958744767332467142922 : ((((p4 ∧ (p5 ∧ p3)) ∧ (((p5 → (False → p5)) ∧ False) ∨ p1)) ∨ (((True ∨ p3) ∨ ((p3 ∨ (p5 ∨ p2)) ∧ p4)) ∨ (p2 ∧ p1))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_918933700098361699975907624619 : (((((p1 ∨ (((((True ∨ p1) ∨ p4) → (p5 ∧ p2)) → p2) ∨ p1)) → False) ∧ ((p4 → p3) ∧ ((p4 ∨ (p5 → p5)) ∧ (True → p4)))) → False) ∧ True) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h8 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h9 : (p1 ∨ (((((True ∨ p1) ∨ p4) → (p5 ∧ p2)) → p2) ∨ p1)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h10
      -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
      have h11 : ((True ∨ p1) ∨ p4) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h8
      -- We have shown the premise of h10, we can now drive its conclusion.
      let h12 := h10 h11
      -- We need to get the right conjuct of h12 based on <expert-advice>.
      let h13 := h12.right
      -- One of the premise coincides with the conclusion.
      exact h13
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h14 := h2 h9
    -- False on the left can always be used.
    apply False.elim h14
  case inr h15 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h16 : (p1 ∨ (((((True ∨ p1) ∨ p4) → (p5 ∧ p2)) → p2) ∨ p1)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h17
      -- We want to use the implication h17 based on <expert-advice>. So we show its premise.
      have h18 : ((True ∨ p1) ∨ p4) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h17, we can now drive its conclusion.
      let h19 := h17 h18
      -- We need to get the right conjuct of h19 based on <expert-advice>.
      let h20 := h19.right
      -- One of the premise coincides with the conclusion.
      exact h20
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h21 := h2 h16
    -- False on the left can always be used.
    apply False.elim h21
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_221734934430616651189423452489 : (((False ∧ p4) → p2) ∧ (p4 → (((((p3 ∨ p2) ∧ (p3 ∨ (p1 ∧ ((True ∧ p4) ∨ p2)))) → False) ∨ (False → (p4 ∨ p3))) ∧ (p3 ∨ True)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h2
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h5
  -- False on the left can always be used.
  apply False.elim h5
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_659688829982997426308185090938 : ((((((p4 ∧ (p5 ∧ False)) → (((p4 ∧ p4) → ((True → p4) ∧ ((p5 ∨ p2) → p2))) ∧ (p1 ∧ (False ∧ p2)))) ∧ p2) → (p1 → p1)) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186011520785612566845900843517 : (((p1 → ((p5 ∧ p2) ∧ (((False ∧ p5) ∨ p4) → False))) ∧ True) → ((p3 ∧ (p2 → p1)) ∨ (((True ∧ (p4 → True)) ∨ (p3 → p4)) ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134055521117425418176336093454 : ((((p5 ∨ (((((p2 → (False → (p5 ∨ p2))) → p3) ∧ p3) ∧ (p3 ∨ (p5 → p2))) ∨ (False ∨ p5))) ∨ p2) ∨ p5) ∨ (False → (False ∧ p2))) := by
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
theorem thm_5_vars_178072474331999424616724831702 : ((((p1 ∨ (((p5 ∧ p5) → p1) ∧ ((p4 → p3) → True))) ∨ False) → p2) ∨ ((True ∨ (False → (((p2 ∨ p1) → p3) → (p5 ∨ p3)))) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_706453596335643566599574726593 : ((((p3 ∨ ((False ∨ ((p3 ∨ p1) ∨ p1)) ∨ p2)) ∧ ((True ∨ ((p3 → (p4 ∧ p4)) ∨ ((((p1 → p2) → p3) → p2) ∧ False))) → p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51820657872260495362670628410 : (((p1 → (((True ∧ (False ∧ p2)) ∧ p3) ∨ (((p1 ∨ (p1 ∨ True)) ∧ p5) ∨ p1))) ∧ ((True ∨ (p1 ∧ (False ∨ (p2 ∨ p2)))) → p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62735228404626788585883565194 : ((p4 ∧ (((((p2 ∨ (p1 ∨ p5)) ∧ p3) → (False ∨ ((p2 ∧ (p5 ∧ (True ∨ True))) ∧ (p2 ∧ (p5 ∨ p5))))) ∧ p5) ∨ (p4 ∨ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_777988320109351489260821155828 : (((p1 ∨ (((p4 ∧ True) ∨ p2) → ((p4 ∧ (p5 → ((p1 ∧ (True → (p4 ∧ ((p3 ∧ p5) ∨ p1)))) ∨ False))) → ((True ∨ p1) ∧ p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117746225388444541991073332927 : ((p4 ∧ ((((((((False → (p5 ∨ p2)) ∨ True) → p1) ∧ True) → ((False ∨ p1) ∨ p4)) → (False ∨ (p5 → False))) ∨ p3) ∨ True)) ∨ (True ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_761970877941729754065400404597 : (((p3 ∧ (((p5 ∧ p2) → (p4 → (p3 → ((True ∧ ((p3 ∧ p2) → ((p4 → (p2 → p4)) → True))) ∨ ((True → p2) ∨ p2))))) → p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197685523727939375166585952210 : (((True ∨ ((p5 → False) ∧ True)) → (p4 ∨ p2)) ∨ ((p5 ∨ True) ∨ (p5 → ((((p2 ∨ p1) → p2) → (p5 ∨ (p1 ∧ (p2 → True)))) ∧ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_355637579527997882967442772259 : (p5 → ((p1 → (p4 ∨ (((((((p5 → (True ∧ p2)) → False) ∧ (p2 ∧ p3)) ∧ p3) ∧ ((p3 ∨ p4) → p4)) ∨ p3) ∧ False))) ∨ (p5 ∨ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_196981100915358155986449683072 : (((((p3 → (p3 → True)) → p1) → p3) ∨ p2) ∨ (False ∨ (((p5 ∧ (p2 → (p5 → p3))) ∨ p1) ∨ (False → (p3 → (p5 ∨ (p3 → p3))))))) := by
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
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_657007987161546630494742167541 : (((((p5 → (p1 ∧ (p2 ∧ p1))) → (((p4 ∧ (((False → (True ∨ p3)) ∨ False) → p4)) ∨ (p4 → (p4 → False))) → p3)) ∨ (p3 → p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180538759643844083700574034964 : ((((p5 ∨ p1) ∧ ((p5 ∨ (p5 ∧ p3)) ∧ p1)) ∨ (p5 ∨ (p2 ∨ p4))) → ((p4 ∧ p5) ∨ (False → (((p3 → p1) ∨ p3) ∧ (p4 ∨ p4))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
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
      cases h6
      case inl h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h9
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- False on the left can always be used.
        apply False.elim h9
        -- False on the left can always be used.
        apply False.elim h9
      case inr h10 =>
        -- Conjunctions on the left can always be decomposed.
        let h11 := h10.left
        let h12 := h10.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h13
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- False on the left can always be used.
        apply False.elim h13
        -- False on the left can always be used.
        apply False.elim h13
    case inr h14 =>
      -- Conjunctions on the left can always be decomposed.
      let h15 := h4.left
      let h16 := h4.right
      -- Disjunctions on the left can always be decomposed.
      cases h15
      case inl h17 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h18
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- False on the left can always be used.
        apply False.elim h18
        -- False on the left can always be used.
        apply False.elim h18
      case inr h19 =>
        -- Conjunctions on the left can always be decomposed.
        let h20 := h19.left
        let h21 := h19.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h22
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- False on the left can always be used.
        apply False.elim h22
        -- False on the left can always be used.
        apply False.elim h22
  case inr h23 =>
    -- Disjunctions on the left can always be decomposed.
    cases h23
    case inl h24 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h25
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- False on the left can always be used.
      apply False.elim h25
      -- False on the left can always be used.
      apply False.elim h25
    case inr h26 =>
      -- Disjunctions on the left can always be decomposed.
      cases h26
      case inl h27 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h28
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- False on the left can always be used.
        apply False.elim h28
        -- False on the left can always be used.
        apply False.elim h28
      case inr h29 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h30
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- False on the left can always be used.
        apply False.elim h30
        -- False on the left can always be used.
        apply False.elim h30



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_775092891017896756162854414257 : (((False ∨ ((p4 ∨ p2) ∧ (((p3 → False) ∧ ((p5 ∨ (p5 ∨ p4)) ∨ (p5 ∨ ((((p3 ∧ True) ∧ p2) ∧ p2) → (p4 ∨ p1))))) ∨ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135819006234140965592012692779 : ((((p4 ∨ (((p3 ∨ p2) → p2) ∨ (False → (True ∨ False)))) ∨ p4) ∧ ((True ∧ (False ∨ ((p1 ∨ True) → p1))) ∧ p1)) ∨ (p1 → (p1 ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115813640175361784333101729158 : ((((True ∧ False) ∧ (True → True)) ∧ (((False ∨ p3) ∨ (p5 ∨ (p1 ∧ ((p1 ∨ ((p3 ∨ p5) ∧ (p5 ∨ p3))) ∧ p3)))) ∨ p5)) ∨ (p3 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_691868325188696693942637716039 : ((((False → ((p5 → (True ∧ p2)) ∨ ((((p2 ∨ p1) ∧ (True → p2)) ∧ p1) → p3))) → (((p2 ∧ (True ∧ False)) ∧ p2) ∨ (p3 → p3))) ∨ p5) ∧ True) := by
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
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148796278987456512793462422019 : ((((((p5 ∧ p5) → p3) ∧ p1) ∧ p1) → (p3 → ((p3 ∧ True) → (((p3 → p3) → (p3 ∧ False)) ∧ p1)))) ∨ ((False → (p5 ∨ p1)) ∧ True)) := by
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
theorem thm_5_vars_877299693954877702728624932016 : (((((p2 ∧ ((p2 ∧ (True ∧ (p3 → p1))) → p4)) ∧ (((False ∨ False) ∨ (p4 ∨ p4)) ∧ ((p1 ∧ p1) ∧ (p1 → False)))) ∧ (p5 → True)) → p5) ∧ True) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h8 := h5.left
  let h9 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- False on the left can always be used.
      apply False.elim h11
    case inr h12 =>
      -- False on the left can always be used.
      apply False.elim h12
  case inr h13 =>
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h14 =>
      -- Conjunctions on the left can always be decomposed.
      let h15 := h9.left
      let h16 := h9.right
      -- Conjunctions on the left can always be decomposed.
      let h17 := h15.left
      let h18 := h15.right
      -- We want to use the implication h16 based on <expert-advice>. So we show its premise.
      have h19 : p1 := by
        -- One of the premise coincides with the conclusion.
        exact h18
      -- We have shown the premise of h16, we can now drive its conclusion.
      let h20 := h16 h19
      -- False on the left can always be used.
      apply False.elim h20
    case inr h21 =>
      -- Conjunctions on the left can always be decomposed.
      let h22 := h9.left
      let h23 := h9.right
      -- Conjunctions on the left can always be decomposed.
      let h24 := h22.left
      let h25 := h22.right
      -- We want to use the implication h23 based on <expert-advice>. So we show its premise.
      have h26 : p1 := by
        -- One of the premise coincides with the conclusion.
        exact h25
      -- We have shown the premise of h23, we can now drive its conclusion.
      let h27 := h23 h26
      -- False on the left can always be used.
      apply False.elim h27
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206495645196705438827160623514 : ((p5 ∨ ((p5 ∨ p1) ∧ (p2 ∨ p1))) ∨ (False → (((((p2 → p4) → p5) ∨ (p3 ∨ p4)) ∧ (p5 ∧ p5)) ∧ (p1 → (p5 ∨ (p4 → False)))))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324908409234408446252778219667 : (p5 ∨ ((p3 ∧ p2) ∨ (p4 ∨ (((((p5 ∧ ((p1 ∨ False) ∧ p5)) ∧ False) ∧ (p2 ∧ (p5 ∧ (p1 ∧ p2)))) → p5) → ((p2 ∧ p2) ∨ True))))) := by
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
theorem thm_5_vars_197100220830365713318271454614 : (((p4 ∧ (p5 ∧ ((p3 → True) → p4))) ∨ p4) ∨ (True ∨ ((((p4 → p4) ∨ False) ∧ p4) → ((p3 ∨ p3) ∧ (p5 ∧ ((True ∧ p2) ∧ False)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147440812635824210620888478554 : ((((True → p4) ∧ ((p1 ∧ ((p4 ∨ p5) ∨ p1)) → ((True → p5) ∨ ((True ∨ p5) ∨ (True ∧ p3))))) ∨ p2) ∨ (p3 ∨ ((False → p5) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_642995142544110146576182016564 : ((((p2 ∧ ((p5 ∧ p4) ∧ (p4 → (((True ∧ (p1 ∨ ((p3 ∨ ((p5 → p2) ∧ p2)) ∨ p4))) ∨ True) → (p4 → (p5 ∨ p1)))))) → False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200739126402844462249534999502 : ((p3 ∧ ((p2 → False) ∧ (p5 ∨ (True ∨ False)))) → (((p5 ∨ ((p4 ∧ p4) ∨ p3)) ∧ False) ∨ ((True ∨ (p3 → False)) ∧ ((False → p2) ∨ p3)))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h9 =>
      -- False on the left can always be used.
      apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_683070485164256627446504332053 : ((((False ∧ (False ∨ (((False → p4) ∨ (p2 → False)) → ((p3 → ((p2 → p3) ∨ p5)) → p2)))) ∧ (p4 ∨ ((True ∨ p5) ∨ (p5 ∨ p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257145904647105486112567987348 : ((p2 ∨ p1) → ((p1 ∨ ((p3 ∨ ((p4 ∧ False) ∨ ((p1 ∧ False) ∨ (p3 ∨ p1)))) ∨ True)) → ((((False → (p4 ∧ p4)) → False) → p3) ∨ p2))) := by
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
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h5 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h6
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h7 : (False → (p4 ∧ p4)) := by
        -- Implications on the right can always be decomposed.
        intro h8
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- False on the left can always be used.
        apply False.elim h8
        -- False on the left can always be used.
        apply False.elim h8
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h9 := h6 h7
      -- False on the left can always be used.
      apply False.elim h9
  case inr h10 =>
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
          exact h13
        case inr h14 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Implications on the right can always be decomposed.
          intro h15
          -- One of the premise coincides with the conclusion.
          exact h12
      case inr h16 =>
        -- Disjunctions on the left can always be decomposed.
        cases h16
        case inl h17 =>
          -- Conjunctions on the left can always be decomposed.
          let h18 := h17.left
          let h19 := h17.right
          -- False on the left can always be used.
          apply False.elim h19
        case inr h20 =>
          -- Disjunctions on the left can always be decomposed.
          cases h20
          case inl h21 =>
            -- Conjunctions on the left can always be decomposed.
            let h22 := h21.left
            let h23 := h21.right
            -- False on the left can always be used.
            apply False.elim h23
          case inr h24 =>
            -- Disjunctions on the left can always be decomposed.
            cases h24
            case inl h25 =>
              -- Disjunctions on the left can always be decomposed.
              cases h1
              case inl h26 =>
                -- Show the right disjunct based on <expert-advice>.
                apply Or.inr
                -- One of the premise coincides with the conclusion.
                exact h26
              case inr h27 =>
                -- Show the left disjunct based on <expert-advice>.
                apply Or.inl
                -- Implications on the right can always be decomposed.
                intro h28
                -- One of the premise coincides with the conclusion.
                exact h25
            case inr h29 =>
              -- Disjunctions on the left can always be decomposed.
              cases h1
              case inl h30 =>
                -- Show the right disjunct based on <expert-advice>.
                apply Or.inr
                -- One of the premise coincides with the conclusion.
                exact h30
              case inr h31 =>
                -- Show the left disjunct based on <expert-advice>.
                apply Or.inl
                -- Implications on the right can always be decomposed.
                intro h32
                -- We want to use the implication h32 based on <expert-advice>. So we show its premise.
                have h33 : (False → (p4 ∧ p4)) := by
                  -- Implications on the right can always be decomposed.
                  intro h34
                  -- Conjunctions on the right can always be decomposed.
                  apply And.intro
                  -- False on the left can always be used.
                  apply False.elim h34
                  -- False on the left can always be used.
                  apply False.elim h34
                -- We have shown the premise of h32, we can now drive its conclusion.
                let h35 := h32 h33
                -- False on the left can always be used.
                apply False.elim h35
    case inr h36 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h37 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h37
      case inr h38 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h39
        -- We want to use the implication h39 based on <expert-advice>. So we show its premise.
        have h40 : (False → (p4 ∧ p4)) := by
          -- Implications on the right can always be decomposed.
          intro h41
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- False on the left can always be used.
          apply False.elim h41
          -- False on the left can always be used.
          apply False.elim h41
        -- We have shown the premise of h39, we can now drive its conclusion.
        let h42 := h39 h40
        -- False on the left can always be used.
        apply False.elim h42



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_15072061642019277873927183864 : (((p2 ∧ ((False ∨ ((p4 ∨ (((p3 → False) ∧ p3) ∧ p3)) ∧ p3)) ∨ ((True ∧ p3) → ((p3 → (p4 → True)) ∨ p1)))) ∨ (p2 → p2)) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149337796036253913409692386441 : (((False ∨ p5) → (((p2 ∨ True) ∨ False) → (p4 ∨ (p3 → (((((p2 ∧ p1) ∧ False) ∧ True) ∨ p4) ∨ p3))))) ∨ ((p1 → (p2 → p1)) → p5)) := by
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
    cases h3
    case inl h4 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h5 =>
        -- False on the left can always be used.
        apply False.elim h5
      case inr h6 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h7
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h7
    case inr h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h9 =>
        -- False on the left can always be used.
        apply False.elim h9
      case inr h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h11
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h11
  case inr h12 =>
    -- False on the left can always be used.
    apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49111373052376437539954170226 : ((((((p3 ∨ p3) → ((p4 ∨ ((p4 → (p3 ∧ p5)) ∨ True)) → p4)) ∧ p2) ∨ (p5 → (True → (p4 ∧ p2)))) ∨ (p1 ∨ (p2 ∨ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115564881500079680580396952377 : ((((False ∨ (p2 ∧ (p4 ∧ p2))) ∨ False) ∧ ((((p3 ∨ ((False ∧ p3) → (False ∧ (p5 ∧ True)))) ∨ (p5 ∨ p1)) ∧ True) ∨ p4)) ∨ (True ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_776075455253478509532388939590 : (((False ∨ (p5 → (((False → (False ∨ p4)) ∨ (p5 ∧ ((p4 ∧ (True ∨ (False ∧ True))) ∧ (p5 → ((p1 ∧ (p5 → p4)) ∧ True))))) → False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336224040679773928326662903646 : (p1 → ((((p3 → (True → (p2 ∧ ((True → (((False → p4) ∧ p2) → ((False → p1) → p5))) ∧ True)))) ∨ True) ∨ ((p2 → p5) → p3)) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116394886852837860925173802879 : (((p2 ∧ (p5 ∨ p1)) → ((((((p4 → (p3 ∨ p2)) ∨ (p5 ∧ True)) ∨ False) ∧ False) ∧ False) ∨ (((False ∨ p4) ∧ False) → p5))) ∨ (False ∧ p4)) := by
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
      -- False on the left can always be used.
      apply False.elim h8
    case inr h9 =>
      -- False on the left can always be used.
      apply False.elim h7
  case inr h10 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h11
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h14 =>
      -- False on the left can always be used.
      apply False.elim h14
    case inr h15 =>
      -- False on the left can always be used.
      apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_757767930556072015172887076993 : (((p1 ∧ (False ∨ (False ∧ ((((p5 ∨ (p4 ∧ (((p4 → p3) ∧ False) ∨ ((p1 ∨ p2) → p1)))) ∨ ((p1 ∨ True) ∨ p1)) ∧ p5) → p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57902985410418706996014683875 : (((p4 ∨ (p2 ∧ p4)) → ((True ∧ (True ∧ (p1 ∨ ((p1 → p3) → ((False ∧ False) ∨ p2))))) ∨ ((((p3 → False) ∧ p4) ∨ p3) ∨ p4))) ∨ p5) := by
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
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336479937986333546698373690506 : (p1 → ((p4 → (((((p2 → ((p5 ∨ p2) ∧ (((p1 ∨ ((p1 → (p3 → False)) → p3)) ∧ p3) ∧ p5))) ∧ True) → p5) ∨ p1) ∨ True)) ∨ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192072899153509438042511709176 : ((p3 → (False ∧ ((True ∧ (True ∧ p1)) ∧ (p2 → p3)))) ∨ (((True → p3) ∨ ((p1 ∨ (p1 ∨ False)) → ((p4 → p5) ∧ (p4 → p2)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178360321813767027942666620305 : (((p1 → (((p3 → p1) ∧ ((False ∧ True) ∧ p4)) ∨ False)) ∨ (p3 ∨ p1)) ∨ (((p3 → p4) ∨ p5) ∨ (True ∨ (p1 ∨ (p3 → (p2 → False)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_320292612551543755367967633540 : (p4 ∨ ((p4 ∧ p4) ∨ (True → (((((p5 ∧ p4) → p3) ∧ (p2 ∧ (p2 ∨ (p1 ∧ ((False → True) ∨ (p3 → p5)))))) → p3) → (p3 ∨ True))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_76676705869032071699595200358 : ((((((p4 ∧ False) ∨ ((p5 → False) ∨ ((True → p2) ∨ p5))) ∨ (p4 ∨ (p5 ∨ True))) ∨ (p4 ∨ ((p1 ∧ (p4 ∧ p5)) → p5))) → p2) → p2) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((((p4 ∧ False) ∨ ((p5 → False) ∨ ((True → p2) ∨ p5))) ∨ (p4 ∨ (p5 ∨ True))) ∨ (p4 ∨ ((p1 ∧ (p4 ∧ p5)) → p5))) := by
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
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_255864626438088974377228228218 : ((True ∨ p1) → (((p1 ∧ p1) ∧ ((p5 → (p1 → (p3 ∧ (((p1 ∧ (p4 → False)) ∨ False) ∧ (p3 → False))))) ∧ p2)) ∨ (False → (False ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_153455691835711887965462090213 : ((p4 ∨ ((p2 → p5) ∨ ((((p5 ∨ ((p1 → p4) ∨ (p4 ∧ (p1 ∨ True)))) ∧ (True ∧ p1)) ∨ p4) ∧ True))) → (((p4 ∧ False) ∨ True) ∨ p3)) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
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
        cases h9
        case inl h11 =>
          -- Conjunctions on the left can always be decomposed.
          let h12 := h10.left
          let h13 := h10.right
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h14 =>
          -- Disjunctions on the left can always be decomposed.
          cases h14
          case inl h15 =>
            -- Conjunctions on the left can always be decomposed.
            let h16 := h10.left
            let h17 := h10.right
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h18 =>
            -- Conjunctions on the left can always be decomposed.
            let h19 := h18.left
            let h20 := h18.right
            -- Disjunctions on the left can always be decomposed.
            cases h20
            case inl h21 =>
              -- Conjunctions on the left can always be decomposed.
              let h22 := h10.left
              let h23 := h10.right
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- True on the right can always be proven directly.
              apply True.intro
            case inr h24 =>
              -- Conjunctions on the left can always be decomposed.
              let h25 := h10.left
              let h26 := h10.right
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- True on the right can always be proven directly.
              apply True.intro
      case inr h27 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119826311670997238283743192035 : (((((p5 ∨ (p3 ∨ False)) → ((((p3 ∧ ((True → p5) ∧ ((True ∧ p3) ∧ (False → False)))) ∧ True) ∨ False) ∨ p2)) → False) ∧ p2) → (False ∨ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : ((p5 ∨ (p3 ∨ False)) → ((((p3 ∧ ((True → p5) ∧ ((True ∧ p3) ∧ (False → False)))) ∧ True) ∨ False) ∨ p2)) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
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
        -- One of the premise coincides with the conclusion.
        exact h3
      case inr h9 =>
        -- False on the left can always be used.
        apply False.elim h9
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h10 := h2 h4
  -- False on the left can always be used.
  apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48201990196079437308492309534 : ((((p1 ∧ False) → (((((((p2 ∧ False) ∧ p4) ∨ p4) → p3) ∨ p2) → (p1 ∨ ((True ∨ (p2 ∨ True)) → False))) → p2)) → (p3 → p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_493606740391245179800038899605 : (((((p2 ∧ (p4 → p5)) ∧ p4) → (((p2 ∧ True) → (((p3 ∧ p3) → p2) ∨ p1)) ∧ ((p4 → ((p1 ∨ False) ∧ p1)) ∨ (p3 → True)))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h9
  -- Conjunctions on the left can always be decomposed.
  let h10 := h9.left
  let h11 := h9.right
  -- One of the premise coincides with the conclusion.
  exact h7
  -- Conjunctions on the left can always be decomposed.
  let h12 := h1.left
  let h13 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h14 := h12.left
  let h15 := h12.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h16
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148884383590152342839157371731 : ((((True → (False → p1)) → p2) ∨ (p3 → ((False ∨ False) ∨ (p2 ∨ ((p5 ∧ p5) → ((p2 → p4) ∨ p5)))))) ∨ (((p2 ∨ True) ∧ p4) → p5)) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40826940314002787377113522338 : ((((False → ((((p5 ∧ (((p5 ∧ (p4 ∧ p1)) ∨ p5) ∨ True)) ∨ (((True ∨ True) → (False ∨ p2)) → p5)) ∧ False) → p1)) → False) ∨ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147919567416084818877847261569 : (((((p3 ∨ p5) ∧ ((((p3 ∨ p3) ∧ (p3 ∧ p1)) ∨ p5) ∧ p2)) ∨ (True ∨ (p2 ∨ True))) ∧ (True ∨ p5)) ∨ ((p2 → False) ∧ (p4 ∨ p1))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314004904420082906821324488836 : (p3 ∨ ((True ∧ (p1 ∨ (((p2 ∨ p2) → (False ∧ ((((True → (p4 ∧ p5)) → (False ∧ (p1 ∨ p2))) ∨ p2) ∨ p3))) → False))) ∨ (p2 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_4461347039248278466790174706 : (p2 → ((p3 ∧ (p4 ∧ ((p3 ∧ (p4 → (False ∧ (p2 → (p5 ∨ ((False ∨ (True → (p5 ∨ p5))) ∧ p4)))))) ∧ p5))) ∨ (p5 → p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185791361948954262002755096074 : ((p5 → ((False ∨ (False ∧ (p4 → (False → (p4 ∨ False))))) ∨ p2)) ∨ ((False → p2) → (p2 → ((p1 ∨ (False ∧ ((p4 ∧ p1) ∨ p3))) ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



