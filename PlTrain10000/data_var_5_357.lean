variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64357703108583701733913771598 : ((p1 ∨ ((((True → (p5 ∨ (((((p5 ∧ p2) ∨ True) ∨ p4) → p5) ∧ (p3 ∨ (p4 ∧ p5))))) ∧ (p4 ∧ True)) ∨ (p5 ∨ True)) ∨ False)) ∨ p4) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187822897876621121873398570674 : ((p4 → ((p1 ∧ p2) → ((p3 ∧ p2) ∧ (True → (p2 ∧ True))))) → (p5 → ((True → p1) → (((p1 ∨ ((p2 → p1) ∨ p4)) ∧ p5) ∨ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_713048628863118880062957504747 : ((((p4 ∧ ((p1 ∧ (p2 → False)) ∧ p5)) ∨ ((p3 ∨ False) ∧ ((p3 ∧ (p2 → (False → ((False ∨ (p5 → (p3 ∨ True))) ∧ True)))) ∧ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_745612745373552803595745626562 : ((((True ∨ p2) → (True ∧ ((p2 → p4) → (((True → p2) → (True → (False → (p5 → True)))) → ((True → False) → ((p2 ∨ p3) ∧ True)))))) ∨ p3) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h5 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h6 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h7 := h4 h6
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h8
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_797392565622644077666571120192 : (((p1 → (((True → p1) ∧ ((p1 ∧ (p5 → False)) → (True → ((((((p2 ∨ False) ∨ p5) ∨ p2) ∧ p4) ∨ (p1 → p4)) ∨ p1)))) ∨ p5)) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64129662283553873569084263042 : ((False ∨ (((p3 ∧ p4) → (p5 ∧ p1)) ∨ ((((p1 → p3) ∨ (p1 ∨ (p4 ∧ p1))) → p4) ∧ ((p2 ∨ (True → False)) ∨ (p4 → False))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_238045482193822834387438038909 : ((True ∨ p1) ∧ (p3 → (((((p1 ∧ ((p3 → p1) ∧ p3)) ∨ p2) ∧ (p2 ∨ p4)) ∧ (((p2 ∨ p3) ∨ (p1 → (p4 ∧ p3))) ∧ p3)) ∨ p3))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136646159458398614034742566366 : ((((p4 ∨ p4) → p1) → (p4 → (((p3 ∧ p1) ∨ p1) ∧ ((((p2 ∧ p4) ∨ True) → (False → p1)) → (p3 ∨ p5))))) ∨ ((p1 ∨ p4) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_729783473911456470883758726835 : (((((p5 → False) ∨ False) → ((p5 ∨ (False ∨ p4)) → ((((p5 ∨ ((p2 ∨ p3) ∧ p1)) ∧ (p2 ∧ False)) ∨ ((False ∨ p5) ∨ p5)) ∨ p4))) ∨ p4) ∧ True) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h4 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h5 =>
      -- False on the left can always be used.
      apply False.elim h5
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- False on the left can always be used.
      apply False.elim h7
    case inr h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h8
      case inr h10 =>
        -- False on the left can always be used.
        apply False.elim h10
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_9921534979078876470566327862 : (((p1 ∧ (p1 ∨ ((((False ∧ (p2 ∧ True)) ∨ (True ∧ p2)) → ((True ∨ p3) ∧ p4)) → (((p4 → p2) → False) → (False ∧ p3))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158939277784631140854508380789 : ((p2 ∨ ((p5 ∨ ((True → False) ∨ (((p4 ∧ (p1 ∨ p1)) → p5) ∧ (p3 ∧ p1)))) ∧ (p2 ∧ p5))) ∨ (True → ((p5 ∨ p5) ∨ (p5 → p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_69234369293402837030010268808 : ((p5 → ((((p3 ∧ False) → p3) → False) → ((((((p2 → (p3 ∧ p5)) ∧ p4) ∨ p4) ∨ (p5 → p4)) ∨ p5) ∧ (p2 ∨ (p2 ∧ True))))) ∨ False) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : ((p3 ∧ False) → p3) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- False on the left can always be used.
    apply False.elim h6
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h7 := h2 h3
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_764124547118515001770710218202 : (((p3 ∧ (p4 → ((((p1 ∨ (p5 ∨ (p4 ∧ True))) ∨ ((p4 ∨ (((p5 → p4) ∧ p2) ∨ (p2 ∧ p5))) → p1)) ∧ (False ∨ p2)) ∧ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218034545358788883420245243183 : (((p1 ∨ p3) ∧ (p5 ∨ p3)) → (((((False ∨ p4) → (((False ∧ p1) ∧ (((p4 ∨ (p1 ∧ p3)) ∧ p4) → p1)) ∨ p5)) ∧ p1) → False) ∨ True)) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h8 =>
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
theorem thm_5_vars_342285396420541405918138633225 : (p2 → (((((True ∧ (p4 → ((p3 ∨ p4) ∧ p5))) ∨ False) ∨ p3) ∨ ((False ∧ (p4 ∧ p4)) ∨ p4)) ∨ (False → (p5 ∨ (False ∨ (p2 → False)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54058587744082147155577377408 : ((((p3 → (p1 ∨ (p3 ∨ p3))) → (p1 ∨ (p2 → p1))) → (p5 ∧ (False ∧ ((p3 ∧ p5) → (((p4 ∨ (p4 ∨ False)) ∧ p3) ∨ True))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_80844996803512453184644054140 : (((((p4 ∨ p5) → (((True ∨ (p4 → p3)) ∧ False) ∧ ((False ∨ p3) ∧ (p4 ∨ ((False ∨ p3) → True))))) ∧ True) ∧ ((False → p1) → p4)) → False) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h6 : (False → p1) := by
    -- Implications on the right can always be decomposed.
    intro h7
    -- False on the left can always be used.
    apply False.elim h7
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h8 := h3 h6
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h9 : (p4 ∨ p5) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h8
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h10 := h4 h9
  -- We need to get the left conjuct of h10 based on <expert-advice>.
  let h11 := h10.left
  -- We need to get the right conjuct of h11 based on <expert-advice>.
  let h12 := h11.right
  -- False on the left can always be used.
  apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257426729958275143850274986178 : ((p3 ∨ True) → (((((p5 → (p2 ∨ p2)) → (((p4 → ((False → (p2 ∨ True)) ∧ p1)) → (True ∨ p4)) ∧ (False ∨ p4))) ∧ p1) ∨ True) ∨ p1)) := by
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
theorem thm_5_vars_111940725113951890420586231730 : ((((((p1 ∧ p3) ∧ (((True → True) ∧ False) ∨ False)) → p5) → (((p4 ∨ (p3 ∧ p2)) ∧ (p2 → p3)) ∧ (False → True))) ∨ True) ∨ (False → p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172763570847052211512253604647 : (((True ∨ p1) → (((False → p3) → p3) ∨ ((p1 ∧ False) ∨ (p2 ∧ (p3 ∨ p3))))) ∨ (((p5 → False) → (False → p1)) ∨ (p2 ∧ (p4 → p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_670318626203015217974492313920 : (((((p5 ∧ (p1 ∧ False)) ∧ ((((p1 → False) → True) ∧ (((((False → p1) ∨ False) ∧ p1) ∨ p2) → p5)) ∨ False)) ∨ (False → (p4 → p4))) ∨ p3) ∧ True) := by
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
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58984895817080662351284797463 : (((p3 ∧ True) ∨ ((((p4 ∧ p5) ∨ ((True → (p2 → (((True → p1) ∧ False) → (p2 ∨ ((p1 ∧ p2) → p4))))) ∨ True)) → p3) ∨ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_125042067681036623445758987815 : ((((True → True) → p5) ∧ (p1 ∨ ((False ∨ False) ∨ (False ∨ (((p4 ∧ (p1 ∧ (p4 → p1))) ∧ ((p2 → p3) → p3)) ∧ p4))))) → (True ∧ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h5 : (True → True) := by
      -- Implications on the right can always be decomposed.
      intro h6
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h7 := h2 h5
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- False on the left can always be used.
        apply False.elim h10
      case inr h11 =>
        -- False on the left can always be used.
        apply False.elim h11
    case inr h12 =>
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- False on the left can always be used.
        apply False.elim h13
      case inr h14 =>
        -- Conjunctions on the left can always be decomposed.
        let h15 := h14.left
        let h16 := h14.right
        -- Conjunctions on the left can always be decomposed.
        let h17 := h15.left
        let h18 := h15.right
        -- Conjunctions on the left can always be decomposed.
        let h19 := h17.left
        let h20 := h17.right
        -- Conjunctions on the left can always be decomposed.
        let h21 := h20.left
        let h22 := h20.right
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h23 : (True → True) := by
          -- Implications on the right can always be decomposed.
          intro h24
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h25 := h2 h23
        -- One of the premise coincides with the conclusion.
        exact h25



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231424141665250478040868506336 : (((p1 → p5) ∨ p3) → ((p3 → p4) ∨ (p1 → ((p2 ∨ ((((p4 → (p4 → p1)) ∧ ((p2 ∧ p4) ∧ p2)) ∧ p3) ∨ (True → p2))) ∨ True)))) := by
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
theorem thm_5_vars_263932733311695820654898117246 : (True ∧ ((p4 ∧ (p2 ∧ ((p2 ∨ p3) ∨ (False ∨ ((True ∧ (False → p5)) ∨ p2))))) → (((True → (p5 ∨ (p4 → (p3 ∧ p1)))) → False) ∨ p2))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- False on the left can always be used.
      apply False.elim h10
    case inr h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- Conjunctions on the left can always be decomposed.
        let h13 := h12.left
        let h14 := h12.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h4
      case inr h15 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133822260795291846187114028163 : ((((False ∨ p3) ∨ ((p2 → (p3 → p5)) ∨ (False ∧ (True ∧ (p1 ∨ (True ∧ ((p1 ∨ p4) ∧ (p4 ∧ p2)))))))) ∧ True) ∨ ((True → p5) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323849224821331812973435610553 : (p5 ∨ ((p1 → (((p1 → p3) ∨ False) ∨ ((p1 ∨ (p2 ∨ (p1 ∧ ((p5 ∨ p3) ∨ p3)))) ∧ p3))) → (p1 → ((p5 ∧ (p3 → False)) → False)))) := by
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
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h6 : p3 := by
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h7 : p1 := by
      -- One of the premise coincides with the conclusion.
      exact h2
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h8 := h1 h7
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
        have h11 : p1 := by
          -- One of the premise coincides with the conclusion.
          exact h2
        -- We have shown the premise of h10, we can now drive its conclusion.
        let h12 := h10 h11
        -- One of the premise coincides with the conclusion.
        exact h12
      case inr h13 =>
        -- False on the left can always be used.
        apply False.elim h13
    case inr h14 =>
      -- Conjunctions on the left can always be decomposed.
      let h15 := h14.left
      let h16 := h14.right
      -- Disjunctions on the left can always be decomposed.
      cases h15
      case inl h17 =>
        -- One of the premise coincides with the conclusion.
        exact h16
      case inr h18 =>
        -- Disjunctions on the left can always be decomposed.
        cases h18
        case inl h19 =>
          -- One of the premise coincides with the conclusion.
          exact h16
        case inr h20 =>
          -- Conjunctions on the left can always be decomposed.
          let h21 := h20.left
          let h22 := h20.right
          -- Disjunctions on the left can always be decomposed.
          cases h22
          case inl h23 =>
            -- Disjunctions on the left can always be decomposed.
            cases h23
            case inl h24 =>
              -- One of the premise coincides with the conclusion.
              exact h16
            case inr h25 =>
              -- One of the premise coincides with the conclusion.
              exact h16
          case inr h26 =>
            -- One of the premise coincides with the conclusion.
            exact h16
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h27 := h5 h6
  -- False on the left can always be used.
  apply False.elim h27



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51144743155106866712136501092 : ((((((False → ((False ∨ p3) → (True ∧ p2))) ∧ (False → False)) ∧ (p2 → (False ∧ p4))) → False) ∨ ((p2 ∧ (p3 → p5)) ∨ (p4 → p4))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_632442513038390629427020026082 : (((((p1 ∨ (p1 ∧ (True ∨ ((p2 ∨ (((p4 ∨ p2) ∨ (p5 ∨ (True → (True → p3)))) ∧ ((False ∨ p2) ∨ False))) ∧ False)))) → p4) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50723320384612642339810608479 : ((((p5 ∧ p5) → (((True ∨ (p3 ∧ False)) ∧ (True ∧ p4)) → ((((p3 ∨ p2) → p5) → p3) ∨ p2))) → (((p4 → p4) → False) ∨ True)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118767998495271967087382011106 : ((p5 ∨ (p1 ∧ (p4 ∨ (p1 ∨ (((p2 ∨ p2) ∨ ((p5 → ((p2 ∨ p1) ∨ p3)) → p2)) ∧ ((p5 ∨ False) ∧ (p5 ∨ p4))))))) ∨ (p4 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_69126077277688550998783773331 : ((p5 → ((((((p4 ∧ p1) → (((p3 ∨ p4) ∨ (p1 ∧ p3)) → (True ∨ p5))) → False) ∨ (True ∨ p1)) → (p2 ∧ True)) → (False ∨ p2))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : ((((p4 ∧ p1) → (((p3 ∨ p4) ∨ (p1 ∧ p3)) → (True ∨ p5))) → False) ∨ (True ∨ p1)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60379749820166124535316849055 : (((p3 → p2) → ((p2 ∨ (False ∧ (p2 ∨ ((p2 → (((p4 ∨ ((p2 ∨ p5) ∧ (p4 ∧ False))) ∨ (p5 ∨ p5)) → p5)) ∧ p4)))) ∨ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52495534407472775975605304853 : (((p4 → (False ∧ (p5 → (True → (True ∨ (p5 ∧ (p1 ∨ (True → True)))))))) ∧ (p1 ∨ (((p2 ∨ p2) ∨ p5) ∨ (True ∧ (p1 → False))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_71534401278426055796088526606 : ((((False → True) → ((True ∧ ((False ∨ ((((False ∧ p4) ∧ ((p1 ∧ False) ∨ p1)) → (p3 ∧ (p4 → p2))) ∧ True)) ∨ p4)) ∧ p5)) ∧ p2) → p5) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (False → True) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h4
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190875347387934707728733058160 : ((((p5 ∧ (False ∧ p5)) → (p1 → p1)) → (False ∧ p3)) ∨ ((p2 → p2) ∨ ((((p4 ∨ (p4 → p5)) ∧ p3) → ((p4 → p4) ∨ p5)) → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_318857180052848245153603615385 : (p4 ∨ ((((((((p1 ∧ ((p4 ∨ False) ∧ (p3 ∨ p4))) → p5) → p2) → p4) ∧ ((True → p4) ∨ p2)) ∨ False) → p3) ∨ ((False → p3) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_693601566061760476250898638619 : (((((p3 → (True → ((p1 ∨ ((p5 → p3) ∨ (p4 ∧ p1))) → False))) ∧ True) ∨ ((True ∧ p2) ∨ (((p3 → p5) ∨ p3) → (p5 → p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191838075221988000911246190609 : ((p3 ∨ (((p5 ∧ p2) ∧ p4) ∧ (p5 ∨ (p3 ∧ True)))) ∨ ((False → ((p3 ∨ ((True ∧ (p3 → (False ∨ p5))) ∧ (p1 → True))) → False)) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- False on the left can always be used.
    apply False.elim h1
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- False on the left can always be used.
    apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227954220724437172348669840832 : ((p3 ∧ (p4 ∧ p3)) ∨ (((((((p1 ∧ (p1 ∧ (p5 ∧ p1))) ∨ p4) ∧ p3) ∨ (((p4 ∨ p4) ∧ False) → False)) ∨ p2) ∨ (p4 ∧ p2)) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- False on the left can always be used.
    apply False.elim h3
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_625106058108083483644078090011 : ((((True → (((False ∨ p2) ∨ (p2 ∨ (((p3 ∧ (p4 → (p1 ∨ (p1 ∨ (True → False))))) ∨ (p2 → p2)) ∨ p3))) ∨ (p5 ∧ p3))) ∨ False) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185015850954473610165517359503 : (((p1 ∨ p3) ∧ (p2 ∧ ((False ∧ p2) ∧ ((p4 → p1) ∨ p2)))) ∨ (p5 → (p1 → ((False → False) ∧ (p2 ∨ ((p3 ∧ (p4 ∨ False)) → True)))))) := by
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
  -- False on the left can always be used.
  apply False.elim h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49628548354712018314537934194 : (((((False → (True ∨ (p5 ∧ p5))) → p2) ∨ ((p1 ∧ (p5 → (p5 → (p3 → (False → True))))) → (p4 ∧ p4))) → ((p1 ∨ p1) → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225828554653343086976693782573 : (((True ∧ p4) ∨ p2) ∨ (p3 → (((False → (p5 ∧ False)) ∧ (p5 → ((p1 ∨ p4) ∨ ((((p1 → p1) ∧ p2) ∨ p5) ∨ p2)))) ∨ (p1 → p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_749963669916501230915174140236 : (((True ∧ ((((p5 → False) ∧ ((((p5 ∨ ((((p3 ∨ p2) ∨ p5) ∨ p2) ∨ False)) → p3) ∨ p4) → (p3 ∨ p4))) ∨ (p2 → p3)) → p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248138923893516161313054893198 : ((p2 ∨ False) ∨ ((p3 ∧ ((False ∨ (p5 ∨ (p3 ∨ True))) ∨ (p2 ∨ ((((p5 ∨ (((p3 ∨ p4) ∨ True) → p1)) ∧ True) ∨ p3) → True)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_654871070171144149261922079579 : ((((((((p5 ∧ (p3 ∧ (((p2 → (False → p5)) → p5) ∨ p3))) ∨ p1) → p2) ∨ ((True ∨ (True → p1)) ∧ p2)) → p1) ∨ (p3 → p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64802236299880676142543802941 : ((p2 ∨ ((p5 ∧ (((False ∨ False) ∧ True) ∨ (((p3 ∧ p2) ∨ ((((p5 ∧ (p3 ∧ p3)) ∨ p3) ∧ p1) ∨ p4)) → (p5 ∧ p1)))) ∨ True)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51270414939293696383882766156 : (((True ∧ ((((((p3 → p4) ∧ p1) ∨ ((p5 ∧ (p2 ∧ p3)) → p3)) ∨ p1) → p3) ∧ False)) ∨ (p4 → ((p1 ∨ p4) ∧ (p2 ∨ p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198518882010857401518686570806 : ((False ∨ ((((p3 → True) ∧ False) ∨ False) ∨ p4)) ∨ (((p3 ∧ True) ∨ ((False ∨ True) ∧ (False → (((True ∨ False) ∧ (p1 ∨ p1)) → p4)))) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
      -- False on the left can always be used.
      apply False.elim h1
    case inr h7 =>
      -- False on the left can always be used.
      apply False.elim h1
  case inr h8 =>
    -- False on the left can always be used.
    apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64737203300119130724068912241 : ((p2 ∨ ((((p4 ∧ p1) ∨ (((p5 ∨ (p4 ∨ p5)) ∨ (p2 → (((p2 → ((p1 → True) → p1)) ∧ p2) → p1))) → p5)) ∨ p2) ∧ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_242998529500565808444987403116 : ((p4 → True) ∧ ((p4 → (False → ((p5 ∨ ((True ∧ p3) → p2)) ∨ True))) → (((False → p4) ∨ (p1 ∧ False)) → (((p3 ∧ p2) ∨ True) ∨ False)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
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
    -- False on the left can always be used.
    apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_175370829731279953199502884644 : ((True → (((((p3 ∨ p2) ∧ (p4 ∧ (p3 ∧ False))) ∧ p3) ∨ (p4 → p1)) ∨ False)) → ((p2 ∨ (True → (p3 ∧ p5))) ∨ ((True ∨ False) ∨ False))) := by
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
theorem thm_5_vars_147362703593140582591622330983 : (((((p4 → p1) → ((p5 ∨ p1) ∧ ((p3 ∧ (p3 ∧ p1)) ∨ (p4 ∧ p1)))) → ((True ∨ p5) → p3)) ∨ True) ∨ (p5 ∨ (p4 ∧ (p1 ∨ p5)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42579324539209762946153117489 : (((p2 ∨ (((((p1 ∧ (True ∨ p4)) → True) ∧ (((p1 ∧ p1) ∧ (True ∧ False)) → (p4 ∨ p2))) → p4) ∨ (True ∨ (p2 ∨ p2)))) ∨ p3) ∨ p1) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68520214948861266261789412730 : ((p3 → (True → (((True → True) ∧ (p2 ∧ ((((False ∨ p2) → p4) ∧ (p1 → True)) → p4))) ∨ (((True ∨ False) → p1) → (False → p4))))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_778137914660527480890763019843 : (((p1 ∨ ((p2 ∨ p1) ∨ (((((True → (p2 → p4)) ∨ p1) → (True → p3)) ∨ (p5 → (p2 → ((p5 ∨ (p4 ∨ p1)) ∨ True)))) ∨ p5))) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60358710898395705902265326377 : (((p2 → p5) → (((p1 ∨ (p4 → (p3 ∨ False))) → (p5 → (((p3 ∨ p2) ∧ (p5 ∨ True)) → p2))) → (p4 ∧ (False → (p4 ∧ False))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_327795402526476497323877812463 : (True → ((((p5 ∧ p3) → ((p1 → (((p4 → p4) ∧ (True → (p3 ∧ p5))) → (False ∧ p4))) ∨ ((p1 → True) → p3))) ∧ True) ∨ (True ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_613043818380361146832596868143 : ((((((((((p5 ∨ p1) ∨ p3) → (False ∧ ((p1 ∧ p4) ∨ (p2 ∧ (p2 → True))))) → (p2 ∨ p4)) → p3) ∨ p1) → (p1 ∧ False)) ∨ True) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_148213427586471397323023260662 : (((p2 → (((((p3 ∨ False) ∧ p4) → p1) → ((p1 ∨ p3) ∧ (p4 ∨ False))) ∧ p1)) ∧ (p3 → (True → p1))) ∨ ((False → (False ∨ p2)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114603326888172971669567314246 : (((p5 ∧ ((p2 → p1) → (p4 → ((p4 ∧ p3) → (p2 ∧ ((False ∨ p1) ∧ True)))))) ∧ ((False → (p5 ∨ p5)) ∨ (p1 → p3))) ∨ (p4 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231052883193757671054870680451 : (((True ∨ p2) ∨ p3) → ((p3 ∧ (p4 ∨ (p5 ∧ (True ∧ (p5 ∧ p2))))) ∨ ((((False → p1) ∨ p1) ∨ (False → (p2 ∧ (p5 ∧ p4)))) ∨ p2))) := by
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h4
      -- False on the left can always be used.
      apply False.elim h4
    case inr h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h7
    -- False on the left can always be used.
    apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_684952317016467148971012724005 : ((((p2 ∧ (False ∨ (((True ∨ ((((True ∨ (False ∨ True)) ∧ p3) → p3) ∧ p5)) ∨ p3) → False))) ∨ (False ∧ (False ∧ ((p3 → p1) ∧ True)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57106679595862825252842438277 : ((((False ∨ p4) ∧ p2) ∨ ((True ∨ (False → (p2 ∨ (p2 ∨ (True → (p4 ∨ True)))))) → ((((True ∨ p5) → p3) ∧ p5) ∧ (p3 → p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_688578261337029423107866925198 : ((((p2 ∨ ((p5 ∨ p3) → ((((p3 ∧ (False → p1)) ∧ p3) ∧ p2) ∧ (False ∨ p2)))) ∧ (False → ((p5 ∨ (p5 → (p1 → False))) ∨ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_693963188367635485308563891029 : ((((((((p1 ∧ (False → p5)) ∨ p3) ∨ p3) → (p5 → p1)) ∨ (p1 ∧ p4)) ∨ (((p2 ∨ ((False ∧ (p2 → p5)) → p1)) ∧ p2) → p2)) ∨ p4) ∧ True) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187786401616193032994648695388 : ((p3 → (((p5 → (p5 ∧ p1)) → p4) ∧ (p3 ∧ (False ∧ p4)))) → (p3 ∨ (True → ((p5 ∨ ((True ∧ p1) ∧ (p3 → (p2 ∨ p2)))) ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185563696928479705939745424020 : ((p4 ∨ ((p1 → p2) ∧ ((p4 → (True ∧ (p1 ∨ p1))) → p1))) ∨ (((p1 ∧ ((p1 ∨ p2) ∧ (False ∧ True))) ∧ (p4 ∧ (p5 ∨ True))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180727177671392176613952137450 : (((p2 → ((p1 → p2) ∧ p5)) ∧ (p5 → (((p1 ∨ p2) → p1) ∨ p5))) → ((p3 → ((((p5 ∧ True) ∨ p1) ∧ p2) → p1)) ∨ (p2 ∨ True))) := by
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
theorem thm_5_vars_148684546765867673840592191773 : ((((False ∧ p3) ∧ ((p2 ∨ p4) → (True ∨ p3))) ∨ (False ∧ (((((p1 → p3) ∧ False) → p3) → True) ∧ False))) ∨ (p3 ∨ (p3 → (False → p5)))) := by
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
theorem thm_5_vars_111289041148417391278367454155 : ((((p4 → True) → (p5 ∧ (p3 → (p2 ∨ (((True ∨ (p3 ∨ p5)) ∧ p4) ∧ ((p4 ∨ p2) ∧ (p5 ∧ (False → False)))))))) ∧ p1) ∨ (p1 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328531281174398296930543969823 : (True → ((p2 ∧ ((((True → ((p3 ∨ False) → ((p4 ∧ p2) ∨ False))) ∨ p5) ∧ p5) ∧ p1)) ∨ (p2 ∨ ((p4 → p3) → ((p4 → True) ∨ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152020223063070988322879822254 : (((((True → ((p2 ∨ p2) ∨ (True → False))) → p4) ∨ p1) ∧ (p4 ∨ (((True ∨ p3) ∧ (p2 ∨ p5)) ∨ False))) → (((True ∨ False) → False) → p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h7 : (True ∨ False) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h8 := h2 h7
      -- False on the left can always be used.
      apply False.elim h8
    case inr h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Conjunctions on the left can always be decomposed.
        let h11 := h10.left
        let h12 := h10.right
        -- Disjunctions on the left can always be decomposed.
        cases h11
        case inl h13 =>
          -- Disjunctions on the left can always be decomposed.
          cases h12
          case inl h14 =>
            -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
            have h15 : (True ∨ False) := by
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h2, we can now drive its conclusion.
            let h16 := h2 h15
            -- False on the left can always be used.
            apply False.elim h16
          case inr h17 =>
            -- One of the premise coincides with the conclusion.
            exact h17
        case inr h18 =>
          -- Disjunctions on the left can always be decomposed.
          cases h12
          case inl h19 =>
            -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
            have h20 : (True ∨ False) := by
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h2, we can now drive its conclusion.
            let h21 := h2 h20
            -- False on the left can always be used.
            apply False.elim h21
          case inr h22 =>
            -- One of the premise coincides with the conclusion.
            exact h22
      case inr h23 =>
        -- False on the left can always be used.
        apply False.elim h23
  case inr h24 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h25 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h26 : (True ∨ False) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h27 := h2 h26
      -- False on the left can always be used.
      apply False.elim h27
    case inr h28 =>
      -- Disjunctions on the left can always be decomposed.
      cases h28
      case inl h29 =>
        -- Conjunctions on the left can always be decomposed.
        let h30 := h29.left
        let h31 := h29.right
        -- Disjunctions on the left can always be decomposed.
        cases h30
        case inl h32 =>
          -- Disjunctions on the left can always be decomposed.
          cases h31
          case inl h33 =>
            -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
            have h34 : (True ∨ False) := by
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h2, we can now drive its conclusion.
            let h35 := h2 h34
            -- False on the left can always be used.
            apply False.elim h35
          case inr h36 =>
            -- One of the premise coincides with the conclusion.
            exact h36
        case inr h37 =>
          -- Disjunctions on the left can always be decomposed.
          cases h31
          case inl h38 =>
            -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
            have h39 : (True ∨ False) := by
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h2, we can now drive its conclusion.
            let h40 := h2 h39
            -- False on the left can always be used.
            apply False.elim h40
          case inr h41 =>
            -- One of the premise coincides with the conclusion.
            exact h41
      case inr h42 =>
        -- False on the left can always be used.
        apply False.elim h42



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205390661865696954663863576968 : ((((p1 ∧ p3) → p1) → (p2 ∨ p3)) ∨ (False → (((False → (p3 ∨ ((p1 → (False ∨ p1)) ∧ True))) ∧ p5) ∧ (p4 → (p1 ∨ (True ∧ True)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- False on the left can always be used.
  apply False.elim h1
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_261407118766832867037534623837 : ((p5 → p1) → ((True ∧ True) ∧ (((((False → p4) → False) ∨ p1) ∧ ((((((p4 → p3) → (True → p5)) ∨ p1) ∨ False) ∨ p5) ∧ p1)) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346363908810329344065876080605 : (p3 → (((True → False) → (p3 ∧ ((p2 ∧ ((((p2 ∨ p3) ∧ False) ∨ False) ∧ True)) ∨ (((p2 ∧ (p5 ∧ p5)) ∨ False) ∨ p4)))) ∨ (False → p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_708490102178114152190627485229 : ((((((((True ∨ p1) → p4) ∧ p4) ∨ p3) ∨ True) → (((((p3 ∧ p1) ∨ (True ∧ True)) → (False ∨ p4)) ∧ ((p1 ∨ p1) ∧ p3)) ∨ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_798242288760778953557087678448 : (((p1 → ((p3 → (True → (((p3 → p3) ∨ (p2 ∧ True)) ∨ ((p4 → (p5 ∨ p1)) ∧ True)))) ∧ (((False ∧ False) ∧ False) ∨ (p5 ∧ p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_681983104753125581214539296384 : (((((((p2 ∨ ((p4 ∨ p2) → False)) ∨ (True ∨ False)) → (((p4 → p1) → False) → False)) ∨ p3) ∧ ((True ∧ True) → (True → (True ∧ True)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_693922636746202083338473602191 : ((((((False → (p1 → (p3 ∧ p2))) → ((False ∨ p3) → p2)) ∧ (p2 ∨ p5)) ∨ (p3 → ((p5 ∧ p2) → (((p4 ∨ False) → True) ∨ True)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147460285973191132972676217767 : ((((p3 → False) → (((((p5 ∧ p4) ∨ p2) ∧ (p5 → p2)) → (p3 ∨ (p1 ∨ (p2 ∨ p1)))) ∧ p4)) ∨ True) ∨ (p5 ∧ (p4 → (p1 → p5)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218923890146411993049537479967 : ((p3 ∧ (p1 ∧ (p2 ∨ p2))) → ((p1 → ((p1 ∧ (False ∨ (True ∧ (p5 ∨ (True ∨ (p5 ∧ (False → False))))))) ∧ p5)) ∨ (p2 ∨ (False ∨ True)))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_712897874376369716467561063852 : ((((True ∧ ((p3 ∨ (p3 ∧ False)) ∨ p3)) ∨ (((p1 ∧ p3) ∨ ((p4 → (False ∨ False)) → True)) ∨ ((False ∨ (p5 ∨ False)) ∧ (p3 → True)))) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_79181877638792691606995834509 : (((((p2 ∨ (((p4 ∨ (p5 ∨ True)) → ((p1 ∧ p2) ∨ False)) ∨ (p4 ∧ (p5 → ((False → p1) ∨ p5))))) → False) ∧ p4) ∨ (False ∧ False)) → False) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h5 : (p2 ∨ (((p4 ∨ (p5 ∨ True)) → ((p1 ∧ p2) ∨ False)) ∨ (p4 ∧ (p5 → ((False → p1) ∨ p5))))) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h4
      -- Implications on the right can always be decomposed.
      intro h6
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h6
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h7 := h3 h5
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- False on the left can always be used.
    apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64649873962803648231140512350 : ((p1 ∨ (p5 ∧ ((True ∨ (False ∨ (p1 ∧ (p1 ∨ False)))) → (((p2 ∨ False) ∧ ((((p1 → (True ∧ True)) → p1) ∨ p4) ∧ p5)) ∨ p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_302569784268581413794133208249 : (False ∨ (p1 ∨ (((p5 → True) ∧ ((p2 ∨ (False ∨ (False ∧ (p1 ∧ (p2 ∧ (True ∨ ((p3 ∨ (False → False)) → True))))))) ∨ True)) ∨ (p2 ∨ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43833133781999644850096567293 : (((((((p5 → p5) ∧ ((p4 ∨ p3) ∨ (True ∧ (True ∨ ((((False ∨ p3) → p5) ∨ True) → True))))) → p4) ∨ False) ∧ (p5 → p4)) → p4) ∨ p5) := by
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
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h5 : ((p5 → p5) ∧ ((p4 ∨ p3) ∨ (True ∧ (True ∨ ((((False ∨ p3) → p5) ∨ True) → True))))) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h6
      -- One of the premise coincides with the conclusion.
      exact h6
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h7 := h4 h5
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h8 =>
    -- False on the left can always be used.
    apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206299651292595914307935975854 : ((p1 ∨ ((True → (p4 → p2)) ∨ p4)) ∨ (((p3 ∨ ((p3 → (p2 ∧ (True ∨ (p2 ∨ (False ∧ (p5 → False)))))) ∧ (False ∨ True))) ∧ False) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147120255618144303620509212043 : ((((False ∨ p5) ∨ ((p1 ∧ (False ∧ ((p5 → (p3 ∨ ((p5 ∨ p5) ∨ p3))) → p3))) ∨ (p2 → p2))) ∧ True) ∨ ((p3 ∨ (False ∧ p2)) → p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336772713578016936051580497080 : (p1 → (((False → p2) ∧ (p2 ∧ (p5 → (p5 → ((True ∨ ((p5 → p5) ∨ ((p4 ∧ p1) ∧ (False ∧ (p3 → (False → False)))))) ∨ True))))) → p2)) := by
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
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111665836165742567766784919647 : ((((p2 ∨ ((p1 → (p4 ∧ ((p1 → (p2 → p1)) ∧ False))) ∧ ((p3 ∨ (p1 ∨ (p5 ∧ (True → p3)))) → p2))) ∨ False) ∨ p4) ∨ (p1 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336265514172603810387146492402 : (p1 → (((p5 ∨ ((True ∧ (p4 → (p2 → (p1 ∨ (p5 ∧ False))))) ∧ (p5 ∧ p3))) ∨ (((p1 → p4) → (p5 ∧ False)) ∨ (p4 ∧ p5))) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_221933718706132801661882017103 : (((p5 ∧ p4) → p5) ∧ ((p5 ∨ (p4 ∨ (False ∨ ((p2 → p2) ∧ (p1 → ((p2 ∧ (True ∧ p3)) ∨ p5)))))) → ((p1 → p4) ∨ (True ∨ p2)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
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
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- False on the left can always be used.
        apply False.elim h9
      case inr h10 =>
        -- Conjunctions on the left can always be decomposed.
        let h11 := h10.left
        let h12 := h10.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_717678124679759807466924530369 : ((((((p4 ∧ False) ∧ p4) ∧ p1) ∨ ((((((p3 ∨ p4) → ((p1 ∧ p3) → p5)) ∨ True) → False) ∨ True) ∨ (((p3 ∨ True) → p5) → p2))) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234590644798148089549530243712 : ((p3 → (p1 ∨ p4)) → (((((p5 ∧ p3) ∨ p2) → p4) ∨ True) ∨ ((p2 → p3) ∧ ((True ∧ p5) ∨ ((True ∨ (p1 ∧ (True ∧ False))) ∨ p4))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_591825760698056615137826762840 : (((((((p3 ∨ (((True ∧ (p3 ∧ (p2 → (p5 → p1)))) → (False ∨ p3)) ∨ False)) ∨ p2) → ((False ∧ False) ∧ p1)) ∨ (p3 → p5)) ∧ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246012428908547118293040470936 : ((p4 ∧ False) ∨ ((((p1 ∧ False) ∧ p4) ∨ ((False ∧ (p5 → (((True → (p1 ∧ p2)) ∨ (((True → p4) ∨ True) ∧ p3)) → p2))) ∨ True)) ∨ p1)) := by
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
theorem thm_5_vars_149011406863439518305444333257 : ((((p4 → p4) ∧ p1) ∨ (p4 ∨ (p5 ∨ ((p3 → p5) ∧ (((p3 ∨ (p3 ∨ p1)) ∨ p4) → (p4 ∨ True)))))) ∨ (((True ∨ True) ∨ True) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173991517623713562701100614942 : ((((p1 ∨ True) ∨ (p4 → (((True ∨ (p2 → p5)) → p2) ∧ (p3 ∨ p3)))) → False) → ((p5 ∧ True) → ((p3 ∧ (p3 ∧ (p1 ∧ p4))) ∧ p2))) := by
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
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h5 : ((p1 ∨ True) ∨ (p4 → (((True ∨ (p2 → p5)) → p2) ∧ (p3 ∨ p3)))) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h5
  -- False on the left can always be used.
  apply False.elim h6
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h7 := h2.left
  let h8 := h2.right
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h9 : ((p1 ∨ True) ∨ (p4 → (((True ∨ (p2 → p5)) → p2) ∧ (p3 ∨ p3)))) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h10 := h1 h9
  -- False on the left can always be used.
  apply False.elim h10
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h11 := h2.left
  let h12 := h2.right
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h13 : ((p1 ∨ True) ∨ (p4 → (((True ∨ (p2 → p5)) → p2) ∧ (p3 ∨ p3)))) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h14 := h1 h13
  -- False on the left can always be used.
  apply False.elim h14
  -- Conjunctions on the left can always be decomposed.
  let h15 := h2.left
  let h16 := h2.right
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h17 : ((p1 ∨ True) ∨ (p4 → (((True ∨ (p2 → p5)) → p2) ∧ (p3 ∨ p3)))) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h18 := h1 h17
  -- False on the left can always be used.
  apply False.elim h18
  -- Conjunctions on the left can always be decomposed.
  let h19 := h2.left
  let h20 := h2.right
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h21 : ((p1 ∨ True) ∨ (p4 → (((True ∨ (p2 → p5)) → p2) ∧ (p3 ∨ p3)))) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h22 := h1 h21
  -- False on the left can always be used.
  apply False.elim h22



