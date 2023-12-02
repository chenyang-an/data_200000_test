variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_226046675784846377132468333488 : (((p5 ∧ p1) ∨ p1) ∨ ((p1 ∨ (p4 ∨ ((False → ((True → True) → False)) ∧ True))) ∧ (p1 ∨ ((False → p4) ∨ ((True → (p2 ∨ p4)) → True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167813469403473459786643993741 : (((((p1 → False) → True) ∧ (p4 ∧ ((p3 ∨ p2) ∨ p1))) ∧ (((p3 ∨ p4) ∧ True) → False)) → (p2 ∨ ((p4 → p4) → ((p4 ∨ p2) → p2)))) := by
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
  cases h7
  case inl h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h10 : ((p3 ∨ p4) ∧ True) := by
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h9
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h11 := h3 h10
      -- False on the left can always be used.
      apply False.elim h11
    case inr h12 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h12
  case inr h13 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h14 : ((p3 ∨ p4) ∧ True) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h6
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h15 := h3 h14
    -- False on the left can always be used.
    apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165574933417958891968262199302 : (((((p4 ∨ p2) → (p5 ∧ p1)) → (p5 → p4)) ∨ ((p1 ∨ (False ∨ False)) ∧ (True ∧ p1))) ∨ ((p2 ∨ (p3 ∧ (True → (p4 → p5)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50577227752864991420194312999 : ((((((p4 ∨ True) → False) → ((p5 ∨ (p5 ∧ False)) ∨ ((p3 → (p3 ∨ (p5 ∧ p3))) → True))) → False) → ((p5 ∧ False) ∨ (p3 → False))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p4 ∨ True) → False) → ((p5 ∨ (p5 ∧ False)) ∨ ((p3 → (p3 ∨ (p5 ∧ p3))) → True))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h2
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_937059730732341314488670631120 : (((((p4 → (False ∨ (p1 ∨ p2))) → p1) ∧ (p2 ∧ ((True ∨ (p1 → (p2 ∧ (p3 → (True → p3))))) ∨ ((True ∨ p2) → (True ∨ p4))))) → p1) ∧ True) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h8 : (p4 → (False ∨ (p1 ∨ p2))) := by
        -- Implications on the right can always be decomposed.
        intro h9
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h4
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h10 := h2 h8
      -- One of the premise coincides with the conclusion.
      exact h10
    case inr h11 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h12 : (p4 → (False ∨ (p1 ∨ p2))) := by
        -- Implications on the right can always be decomposed.
        intro h13
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h4
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h14 := h2 h12
      -- One of the premise coincides with the conclusion.
      exact h14
  case inr h15 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h16 : (p4 → (False ∨ (p1 ∨ p2))) := by
      -- Implications on the right can always be decomposed.
      intro h17
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h18 := h2 h16
    -- One of the premise coincides with the conclusion.
    exact h18
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_739228018807153046648587593945 : ((((p4 ∧ p1) ∨ ((((p5 ∧ True) ∧ True) ∧ (True ∨ (p1 ∨ False))) ∨ ((p1 ∨ ((False ∨ (True ∨ (p1 ∧ False))) ∨ p1)) ∧ (p1 → p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_641839584414895287401446064662 : (((((False → False) → ((p4 ∧ ((p2 ∧ (p5 ∨ ((p3 ∨ (p1 ∨ p5)) → ((p5 → (p1 ∧ (p2 ∧ p3))) → True)))) ∨ True)) ∨ True)) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_917096006068868422903369371115 : ((((((p5 ∧ (True ∨ (p1 ∧ (p3 → (True ∨ (p5 ∧ (p1 ∨ p3))))))) ∧ p1) ∨ True) → (((p2 → (p2 → True)) → (p1 → p3)) ∧ False)) → p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p5 ∧ (True ∨ (p1 ∧ (p3 → (True ∨ (p5 ∧ (p1 ∨ p3))))))) ∧ p1) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- False on the left can always be used.
  apply False.elim h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171916666735620256277676180987 : (((p4 → ((p4 → (((False ∨ p2) ∧ p4) ∧ ((p3 ∧ True) → False))) ∧ p5)) → p2) ∨ ((False → ((True → p3) ∧ ((p1 ∨ True) ∧ False))) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148317035196528447335024134374 : (((p2 ∨ (p5 → (p2 ∧ ((((False ∨ (False ∨ True)) → p3) → (p1 → True)) ∨ p4)))) → ((p5 → p5) → p3)) ∨ (((p2 ∨ p5) ∧ False) → p2)) := by
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
theorem thm_5_vars_699529682942690410639006512572 : (((((True ∨ (((p3 → (False ∨ (p2 → False))) ∧ False) → p3)) ∨ p4) → (p3 → ((p1 ∧ (True ∨ (((True ∨ False) ∨ p4) ∨ p3))) ∧ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_92372704241679047127133458422 : (((p1 ∨ True) → ((p2 → p2) ∧ ((((((p4 ∧ p5) ∨ p1) ∧ p1) → ((False ∧ p5) ∧ (p1 ∨ ((p5 ∨ p1) ∨ p5)))) ∧ p5) ∧ p1))) → p1) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p1 ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117875507031344489751252216720 : ((p5 ∧ (((((p1 → False) ∧ (p2 ∧ True)) → (p4 ∨ ((p2 → ((False ∨ (p2 ∧ p4)) ∧ p2)) → (True ∨ True)))) ∨ p5) → False)) ∨ (False → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_255806061947073763099337478828 : ((True ∨ False) → ((((True → (p3 → p2)) → (p4 → (p4 → True))) → ((p3 ∨ (p2 ∨ (False ∧ p4))) ∨ False)) ∨ (p1 ∨ (p3 → (p5 → p5))))) := by
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
    -- Implications on the right can always be decomposed.
    intro h4
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56327184330086830826353282546 : ((((p5 → (p2 ∧ True)) ∧ p4) → (p1 ∧ (((p3 ∨ (p2 ∧ ((p3 ∧ (p1 ∨ False)) → (p5 ∧ p2)))) ∨ p4) ∧ (p5 ∨ (p4 → p1))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44505284369185970821766976386 : ((((p2 → (p5 ∧ (p1 ∨ ((True ∨ (p1 ∧ True)) ∨ True)))) ∧ ((((p5 ∧ p1) ∧ True) → (p5 ∧ ((p1 ∧ p2) ∨ p1))) ∧ p1)) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111946716106289236414029897249 : (((((p3 ∧ (True ∧ (p5 ∨ (True ∨ p1)))) ∨ p2) ∧ ((((p5 ∧ True) → True) ∧ ((p5 ∧ p5) ∧ (p2 → p4))) → p4)) ∨ p1) ∨ (True → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179298124921888058033181155715 : ((False ∨ ((((((p5 ∧ (p3 ∨ p4)) ∧ False) ∨ p1) → p1) ∧ p2) → p4)) ∨ (True ∨ (False ∨ ((p4 ∧ (p2 → (True → True))) ∨ (p3 ∨ p2))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_445463150750185110281547513075 : (((((((((p4 → ((p5 → p2) ∧ p2)) ∧ p3) ∧ True) → (False ∨ (p4 → (False ∨ (p2 ∧ p5))))) → False) ∨ True) → (p2 ∨ (False → p1))) ∧ True) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50288324739377437526379274256 : ((((True → (((((True → p4) ∧ p1) ∨ p2) → ((p2 ∧ p3) ∨ (p5 ∧ p5))) ∧ False)) → (p2 ∧ p3)) ∨ (p1 ∨ (p4 → (True ∧ p4)))) ∨ p1) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172264777225918771833458699258 : ((((p2 ∨ (((p2 ∧ p2) ∧ p1) ∨ p2)) ∨ True) ∨ (((p2 ∧ p4) → False) → True)) ∨ (True ∨ (((((p5 → p4) → True) ∨ False) ∨ p5) ∧ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_352265765197934812475579567433 : (p4 → ((((p4 ∨ p1) ∨ True) ∨ p5) → (((((False → (p4 ∧ True)) → ((p2 ∧ p4) ∧ False)) → p1) ∨ False) ∨ ((True → True) ∧ (p4 ∨ p4))))) := by
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
      cases h4
      case inl h5 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Implications on the right can always be decomposed.
        intro h6
        -- True on the right can always be proven directly.
        apply True.intro
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h1
      case inr h7 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Implications on the right can always be decomposed.
        intro h8
        -- True on the right can always be proven directly.
        apply True.intro
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h1
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h10
      -- True on the right can always be proven directly.
      apply True.intro
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h1
  case inr h11 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h12
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181335496426250957371943399406 : ((True ∨ (p2 ∨ (p2 → ((((p1 ∨ True) ∨ (True ∨ False)) ∨ False) ∨ p1)))) → ((((True → True) ∨ p2) → p3) ∨ ((False ∧ True) → (p4 ∨ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- False on the left can always be used.
    apply False.elim h4
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- False on the left can always be used.
      apply False.elim h9
    case inr h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h12
      -- Conjunctions on the left can always be decomposed.
      let h13 := h12.left
      let h14 := h12.right
      -- False on the left can always be used.
      apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158007111687532574781763353836 : (((((p5 ∨ (p4 ∨ p3)) ∨ p4) ∧ p2) ∧ (p3 ∨ ((p4 ∧ p3) ∨ (False ∧ (p3 ∨ (p2 → p2)))))) ∨ (((p5 ∨ False) ∨ True) ∧ (False → False))) := by
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
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55448168067586042607292654976 : (((((p4 ∧ p1) → (p5 ∧ False)) → p2) → ((p2 ∧ (p4 ∨ p4)) ∨ ((p4 ∨ p4) ∧ ((True ∨ ((p5 ∨ p1) → False)) ∨ (False → p5))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_335997200736337355101124583814 : (p1 → ((False ∨ (p2 ∨ (((((p2 → (True → False)) ∧ (p3 → False)) ∨ p2) ∨ (p1 → ((p1 ∧ p1) → (p1 ∨ (False ∨ p2))))) ∨ False))) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
  intro h2
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_254816582387197502762508789340 : ((p3 ∧ p5) → ((((((((p5 → (False → p2)) ∨ p1) → p1) ∨ (p2 → p1)) ∨ True) ∧ ((p3 ∧ (p2 ∨ p3)) ∧ p4)) ∨ (p5 → True)) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_720485596556586382781161380695 : (((((p2 ∨ (True ∧ p5)) ∨ p4) → ((p2 ∧ (p5 ∧ p5)) ∨ (True ∨ (True ∧ (False ∨ ((p1 ∨ (True ∧ (p5 ∧ (False → p3)))) ∧ p3)))))) ∨ p1) ∧ True) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h4 =>
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_353925673442470157300594226019 : (p4 → (p2 → ((((p4 ∧ p1) ∨ False) → p3) → (((((((p1 → (False ∨ p4)) ∧ p1) ∨ p1) ∧ ((p1 → False) ∧ False)) ∨ p1) ∨ False) ∨ p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187731953879153342668347767701 : ((p1 → ((p4 ∧ True) ∨ (((p3 ∨ (p4 ∧ True)) ∨ p1) → p5))) → (p2 → (((True ∨ p1) ∧ (p5 ∧ (p4 ∨ (p5 → p4)))) → (p4 ∨ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h9
    case inr h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h7
  case inr h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h5.left
    let h13 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h14 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h14
    case inr h15 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_196942781320881156006323377909 : ((((((p5 ∧ p5) ∨ p4) ∨ p2) ∨ p3) ∨ False) ∨ ((p1 ∨ p5) → ((((p1 ∧ ((False ∧ True) ∨ (p1 → False))) ∧ p5) → (True ∧ p2)) ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- True on the right can always be proven directly.
    apply True.intro
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
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
      apply False.elim h9
    case inr h11 =>
      -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
      have h12 : p1 := by
        -- One of the premise coincides with the conclusion.
        exact h6
      -- We have shown the premise of h11, we can now drive its conclusion.
      let h13 := h11 h12
      -- False on the left can always be used.
      apply False.elim h13
  case inr h14 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h15
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Conjunctions on the left can always be decomposed.
    let h16 := h15.left
    let h17 := h15.right
    -- Conjunctions on the left can always be decomposed.
    let h18 := h16.left
    let h19 := h16.right
    -- Disjunctions on the left can always be decomposed.
    cases h19
    case inl h20 =>
      -- Conjunctions on the left can always be decomposed.
      let h21 := h20.left
      let h22 := h20.right
      -- False on the left can always be used.
      apply False.elim h21
    case inr h23 =>
      -- We want to use the implication h23 based on <expert-advice>. So we show its premise.
      have h24 : p1 := by
        -- One of the premise coincides with the conclusion.
        exact h18
      -- We have shown the premise of h23, we can now drive its conclusion.
      let h25 := h23 h24
      -- False on the left can always be used.
      apply False.elim h25



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_746116005994836434075938441433 : ((((p1 ∨ p1) → (((p3 ∨ (p2 → (True → False))) ∨ (p1 ∨ False)) ∧ (p4 ∧ ((((True ∧ p1) → p3) ∧ (p1 ∧ (True → p1))) ∧ p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204830199635596377877450901666 : ((((False ∨ (p1 → p5)) ∨ True) → False) ∨ (((p1 ∨ False) ∨ ((p3 ∨ (p3 → True)) ∨ True)) ∨ (((False → (p5 → p2)) → p1) → (p3 ∧ p5)))) := by
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
theorem thm_5_vars_49036771150865677670674544242 : ((((p3 ∧ ((p1 ∨ (p3 ∧ ((((True → ((p2 ∧ p1) ∧ False)) ∧ p4) ∧ p4) ∨ (p4 → False)))) → p4)) → False) ∨ (p1 → (p2 ∨ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_153790195952577923283262059054 : ((p4 → (p1 ∨ ((p2 ∧ ((p3 ∧ p4) → (((p5 ∧ (p3 → False)) ∧ p3) ∧ p1))) ∨ (p4 ∧ (p1 ∧ p3))))) → (((p5 ∧ p4) ∨ True) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206328262664866935163804675892 : ((p1 ∨ (p5 ∨ (p4 ∧ (p2 → p2)))) ∨ (((((p2 ∧ p3) ∧ (False ∧ (p5 → p4))) → p4) → ((p1 ∧ (True → p2)) ∨ False)) → (p3 ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p2 ∧ p3) ∧ (False ∧ (p5 → p4))) → p4) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h5.left
    let h9 := h5.right
    -- False on the left can always be used.
    apply False.elim h8
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h10 := h1 h2
  -- Disjunctions on the left can always be decomposed.
  cases h10
  case inl h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h12
  case inr h14 =>
    -- False on the left can always be used.
    apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116413170844168309307824118188 : (((p1 ∨ (p2 ∨ p3)) → (((((p4 ∨ (((True ∧ False) ∨ False) ∨ (p1 → p4))) ∧ p4) ∨ (p4 ∧ p2)) → p5) → (p5 ∨ True))) ∨ (p5 ∨ p4)) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54273742700303176521653409689 : ((((p5 → (p2 ∨ p1)) ∧ (p5 ∨ (p2 → p3))) ∧ (p2 ∧ (False ∧ (p1 ∧ ((p1 ∨ (p4 ∨ p1)) ∨ (True → (True ∧ (p1 ∨ p3)))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171648821397333641663000656370 : ((((p4 → p1) → (((True ∨ p1) → ((p3 → p3) ∧ False)) ∨ (False → p2))) ∨ p2) ∨ ((p1 ∨ p3) ∧ ((p5 ∨ (p5 → p1)) ∧ (False ∧ True)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_637290912551087846866805577804 : ((((((p3 ∨ (p3 ∨ (p3 ∨ p3))) → (p2 ∧ (p5 → (p4 ∨ p4)))) → ((((p3 → ((p1 ∨ p3) ∨ p3)) → p4) → p3) ∧ p4)) → False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_695039647346757894969057003069 : (((((p2 ∧ (p5 → ((p1 → p4) → (p3 ∧ ((False → p5) ∨ p1))))) ∧ p5) → ((((p2 → (False → p4)) ∧ False) → p5) ∧ (p1 ∨ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258099296035179675789138295125 : ((p4 ∨ p3) → ((p5 ∨ (p3 → (((((p4 → ((p2 → (True ∧ (p2 ∧ p2))) ∨ (p4 ∧ p1))) → p1) ∨ True) ∨ p3) ∨ (False ∨ p1)))) ∨ p3)) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_195612045800033001719457736908 : (((True ∨ False) ∧ (False → (p1 → (p3 → True)))) ∧ ((((p1 → p3) → (p3 → True)) → ((True → p4) ∧ (p1 ∨ (True → p1)))) ∨ (False ∨ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_266094531859414563968994472197 : (True ∧ (p2 → ((p5 ∧ p2) → ((p2 → (False ∨ False)) → (((p4 ∧ p1) ∧ (((p4 → p1) ∨ p4) → (((p2 → False) → p2) ∧ p4))) ∨ True))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_183863380834667860449072221557 : (((((p1 ∧ (p4 → p3)) ∨ True) ∨ (p2 ∨ (p1 → True))) ∧ p4) ∨ ((False ∨ (p5 ∧ ((p4 ∨ p3) ∨ (p1 → (True → True))))) ∨ (p4 → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337398312664738907932630620629 : (p1 → ((p1 → ((p3 ∧ (p5 → True)) ∨ (p5 ∨ (p2 ∧ (((False → p4) ∧ p2) ∨ (p3 ∨ ((False ∨ p3) ∨ p4))))))) ∨ ((p2 ∨ False) → p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h4 =>
    -- False on the left can always be used.
    apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313092541488073334589463245783 : (p3 ∨ (((((True ∨ ((p4 → False) → ((((p2 ∨ p2) → True) ∨ ((p4 → True) → p3)) → (True → p5)))) ∧ p3) → p4) → (p4 ∨ p1)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_224455519583281479670014103462 : ((p1 → (p5 ∨ p1)) ∧ (True ∧ ((p4 ∨ (((True → (False ∨ p3)) ∧ p2) ∧ True)) ∨ (((p4 ∧ (((True ∧ p5) ∧ p4) → p4)) ∧ p1) → True)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_72109045669035405549227455813 : (((True → (((((p4 → p3) → (True ∧ p4)) → ((False ∧ ((False → True) ∨ p2)) → False)) ∨ (((p1 ∨ p3) ∨ p4) → False)) ∧ p2)) ∧ p1) → p2) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114661345592459447593784063296 : (((((p1 → p1) ∧ p4) ∧ ((p4 ∧ ((True → (False → (p3 → p5))) ∨ False)) ∨ p1)) ∨ (False ∨ (p2 → (False ∨ (p4 → p1))))) ∨ (p1 → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149628901756912753675096839417 : ((p4 ∧ ((p3 ∨ (((True ∧ False) ∧ ((True ∧ p1) → ((p1 → True) → p5))) ∧ ((p2 → True) ∧ p4))) ∧ p5)) ∨ ((False ∧ True) ∨ (False ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_743752873939616777872691539610 : ((((True ∧ p4) → ((p1 ∨ (p2 → (((p4 → p4) → p3) ∧ (p3 → (p2 ∧ False))))) ∨ (p2 ∨ (((p5 → p5) → (p4 → p1)) ∨ p4)))) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225975571194596595027414119458 : (((p3 ∧ p2) ∨ p3) ∨ (p4 → (((p3 → (p5 ∨ p4)) ∧ ((True ∧ True) ∧ ((p3 ∨ True) ∨ True))) ∨ ((False ∨ p4) ∨ (False → (p1 ∨ p5)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_919443715265680853605794789464 : (((((True → p5) ∧ ((False ∧ (((p1 ∨ False) → p4) → (p3 → p3))) → p1)) ∧ (True ∧ ((p5 → (False ∧ True)) ∧ ((False ∨ p3) → False)))) → p2) ∧ True) := by
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
  let h6 := h3.left
  let h7 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h7.left
  let h9 := h7.right
  -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
  have h10 : p5 := by
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h11 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h12 := h4 h11
    -- One of the premise coincides with the conclusion.
    exact h12
  -- We have shown the premise of h8, we can now drive its conclusion.
  let h13 := h8 h10
  -- We need to get the left conjuct of h13 based on <expert-advice>.
  let h14 := h13.left
  -- False on the left can always be used.
  apply False.elim h14
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167245041796407237054498766583 : (((p4 → ((((p1 ∧ p1) ∨ p4) ∧ False) → ((True → (p4 ∨ False)) ∨ (p1 ∧ p1)))) ∨ p3) → ((p4 → (False ∨ (p2 → p5))) ∨ (p4 → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156958006487507713119447179938 : (((((p3 ∨ (False → p1)) ∧ (p3 ∧ ((p4 → True) → (p4 ∧ p5)))) ∨ ((False → p4) → p5)) ∨ False) ∨ (((p3 ∧ p1) ∧ p2) → (True ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233189821181417237834926165323 : ((p5 ∧ (p4 ∨ p3)) → ((p2 → p4) → (p2 ∨ (((p3 ∨ (True ∧ (True ∨ p5))) ∧ p1) ∨ ((p1 ∨ (p2 → p1)) ∨ (p5 → (False → p1))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- Implications on the right can always be decomposed.
    intro h7
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- Implications on the right can always be decomposed.
    intro h10
    -- False on the left can always be used.
    apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_675118041699093116215101548314 : ((((((((True ∧ ((((p3 → p2) ∨ p5) ∨ (p5 → p4)) ∨ p4)) ∨ (p5 ∨ p1)) ∨ p5) → p2) ∨ p5) ∧ (p5 ∧ (True ∨ (p3 ∨ p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_255911974930150823126668800918 : ((True ∨ p2) → (((p5 → False) → ((((p1 ∧ False) ∧ p4) ∨ (True → p3)) ∨ (p3 ∨ ((p2 → ((p2 → p4) → (p1 → False))) → True)))) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h6
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59058207276476418844682283407 : (((p4 ∧ p5) ∨ (((p4 ∨ p4) ∧ (p3 ∨ (((p1 ∨ p3) ∧ False) ∨ ((True ∨ (p1 ∨ p3)) → ((p2 ∧ True) → (p3 ∨ p3)))))) ∨ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48849760017099169611901353964 : (((p2 ∨ (((((p5 → p2) ∧ (((p1 → p3) ∧ p5) ∨ (p1 ∨ p2))) ∨ False) ∨ p3) ∨ (p3 ∧ (p4 ∧ p5)))) ∧ (True ∧ (p5 ∧ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225515639091925102835578177398 : (((p5 ∨ p4) ∧ p5) ∨ (((p2 ∧ (p2 → ((((True → (p1 ∨ (False ∨ p1))) ∧ p5) → p1) ∧ p4))) ∨ p2) → ((p4 → p3) ∨ (p2 → p2)))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_140319683541687782215128683036 : (((False → (((((((True → False) ∧ True) ∧ True) ∨ p5) → p3) → p4) ∨ ((p4 ∨ p4) ∧ p2))) ∧ ((p1 ∨ p3) → p1)) → ((p5 → p4) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_89392328625556438453173389612 : (((p2 → (False ∧ p1)) ∧ ((p2 ∧ (False ∨ (p3 ∨ (p5 → (p2 ∧ ((((p5 ∨ p4) ∧ p5) ∧ ((p5 ∨ False) ∨ False)) ∨ p1)))))) ∧ True)) → p4) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h11 : p2 := by
        -- One of the premise coincides with the conclusion.
        exact h6
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h12 := h2 h11
      -- We need to get the left conjuct of h12 based on <expert-advice>.
      let h13 := h12.left
      -- False on the left can always be used.
      apply False.elim h13
    case inr h14 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h15 : p2 := by
        -- One of the premise coincides with the conclusion.
        exact h6
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h16 := h2 h15
      -- We need to get the left conjuct of h16 based on <expert-advice>.
      let h17 := h16.left
      -- False on the left can always be used.
      apply False.elim h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50777900212170538396582765416 : (((p2 ∨ (True → (((p4 ∧ p5) ∨ (p5 ∨ (p4 ∧ (p3 → (p3 ∧ (p5 ∨ p3)))))) → (p1 → True)))) → ((True → p3) ∨ (True ∨ p3))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112002792848244183591968377068 : ((((p2 ∧ (False ∧ (True ∧ p2))) ∨ ((p2 ∨ True) → ((((True → p5) → ((p2 ∨ p2) ∧ p4)) → p2) ∨ (p5 → True)))) ∨ p5) ∨ (p1 ∨ p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345518249880317982554352606549 : (p3 → ((((((False → ((False ∧ p1) → p1)) ∧ False) ∨ (p5 ∧ p2)) ∧ p2) ∨ ((p2 ∨ ((p2 ∧ p2) → ((False ∨ True) ∧ p2))) ∨ p2)) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h5 := h2.left
  let h6 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_703587998678799548392522549259 : ((((p3 → ((p2 → p4) → (((p3 → True) ∨ p2) → False))) ∨ (p1 → (p3 ∨ (((p4 ∨ (p3 → (p1 ∨ p2))) ∨ (True → p2)) ∨ p2)))) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_173521505589578357199503644623 : (((((p3 → (p3 ∨ ((p5 → p1) ∨ p2))) ∧ False) ∨ (p1 → (False ∧ p1))) ∧ p1) → (p4 → ((p2 ∨ p2) ∨ ((p1 ∧ True) ∧ (p3 ∧ p3))))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
    have h9 : p1 := by
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h8, we can now drive its conclusion.
    let h10 := h8 h9
    -- We need to get the left conjuct of h10 based on <expert-advice>.
    let h11 := h10.left
    -- False on the left can always be used.
    apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60953535760298942566192688728 : ((False ∧ ((((p2 ∧ (((True → (p5 ∨ (p5 → p2))) ∧ p5) ∧ (p4 ∧ p4))) → ((p4 → ((False → p4) ∧ False)) ∨ p1)) → False) ∨ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111922672878688042034545244539 : ((((((p4 ∧ (p1 ∨ p3)) ∨ p3) ∨ (p3 ∨ ((p2 ∨ p3) → p1))) → (p2 ∧ ((p2 ∨ ((False ∧ True) ∨ False)) ∨ p5))) ∨ True) ∨ (p3 ∨ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_139338712845793814923069036343 : (((p3 ∨ (True → (((p2 ∨ ((p2 → ((p5 → p1) ∨ (False → (True ∧ p2)))) ∧ p3)) ∨ False) ∧ (False ∧ p3)))) ∨ p1) → (p1 → (False ∨ p1))) := by
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
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156934380804457784899003005503 : ((((p2 ∧ (((((p1 ∧ (p5 ∧ (p4 ∧ False))) ∧ p1) → False) ∧ p4) → p2)) ∧ (True ∨ p3)) ∨ p1) ∨ (((p3 ∧ False) ∨ p5) ∨ (p3 → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213596076481580351228005651476 : ((((p2 → p4) ∧ p5) ∨ False) ∨ ((((p4 ∨ False) ∧ True) ∧ (((p2 → p4) ∨ ((p1 ∨ True) ∧ p1)) ∧ p2)) → ((p2 → False) ∨ (p2 → True)))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h7 := h3.left
    let h8 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h14 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h15
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h16 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h17
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h18 =>
    -- False on the left can always be used.
    apply False.elim h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_915054470156080031273440694001 : ((((False ∨ ((((True → p2) ∧ (False ∧ ((p3 → p4) → False))) ∨ p4) ∧ (p2 → p2))) ∧ (True → (((p2 ∧ (p1 ∨ p5)) ∨ True) ∨ p2))) → p4) ∧ True) := by
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
    -- False on the left can always be used.
    apply False.elim h4
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
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- False on the left can always be used.
      apply False.elim h11
    case inr h13 =>
      -- One of the premise coincides with the conclusion.
      exact h13
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338423691964955461570609624576 : (p1 → ((True ∨ (p3 ∨ (p3 ∧ p2))) → ((p1 ∨ ((p1 ∨ p2) ∨ p1)) ∧ (((False → ((p5 ∧ p5) ∨ p5)) ∨ (p3 ∧ p3)) → (p5 ∨ p1))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h1
  -- Implications on the right can always be decomposed.
  intro h9
  -- Disjunctions on the left can always be decomposed.
  cases h9
  case inl h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h12 =>
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h1
      case inr h14 =>
        -- Conjunctions on the left can always be decomposed.
        let h15 := h14.left
        let h16 := h14.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h1
  case inr h17 =>
    -- Conjunctions on the left can always be decomposed.
    let h18 := h17.left
    let h19 := h17.right
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h20 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h21 =>
      -- Disjunctions on the left can always be decomposed.
      cases h21
      case inl h22 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h1
      case inr h23 =>
        -- Conjunctions on the left can always be decomposed.
        let h24 := h23.left
        let h25 := h23.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_657759945063169551179250345665 : ((((True ∧ (((((p2 ∨ p1) ∧ p1) ∨ (p3 ∨ ((p1 → p4) ∨ True))) ∧ (True ∧ p1)) ∧ ((p5 → p1) ∨ (p4 → p5)))) ∨ (p4 → True)) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_809035606835143490886008097655 : (((p5 → (((p2 → p1) → ((p4 ∧ (p4 → (p4 → ((p1 ∧ (((p1 ∨ ((True → p1) ∧ True)) ∧ p3) → p4)) ∧ p3)))) → p3)) ∧ p5)) ∨ p5) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h6 : p4 := by
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h7 := h5 h6
  -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
  have h8 : p4 := by
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h7, we can now drive its conclusion.
  let h9 := h7 h8
  -- We need to get the right conjuct of h9 based on <expert-advice>.
  let h10 := h9.right
  -- One of the premise coincides with the conclusion.
  exact h10
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204697419949691054550595105444 : (((p3 ∨ (p5 ∧ (False ∨ p1))) ∨ False) ∨ (((p2 ∧ p5) → (p3 ∨ ((False ∧ p4) ∨ ((p5 → (p1 → ((False ∧ p1) ∨ p3))) ∧ p4)))) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_594160515980174868885984829054 : ((((((((p5 → True) ∧ p1) → False) ∧ ((True ∨ (p2 ∧ (p5 → (p5 ∧ (False → p3))))) ∧ p4)) → (p2 → (p5 ∧ (True ∧ p5)))) ∧ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58731976320063513626592787067 : (((p3 → p3) ∧ (((False → ((p5 ∧ False) ∨ (p3 ∨ (p3 → (p3 ∨ p5))))) ∧ ((p1 ∧ True) → (p5 ∨ ((False ∧ p4) ∨ False)))) ∨ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53028750964566808272528638476 : (((((p5 ∧ p2) ∨ p3) ∧ ((False ∨ p1) ∨ (p3 ∨ (p2 → p4)))) ∧ (p5 ∨ (((p2 ∧ ((p1 ∧ False) ∧ (p4 → p5))) → p1) → p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164924485007118960879542118213 : (((((True ∨ ((((p1 → p1) ∨ p2) ∧ True) → (True → p2))) ∧ (p1 → True)) ∨ p4) → p1) ∨ ((p5 → (((True ∨ p2) ∨ p1) ∧ p4)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_702912487046119418542865035610 : ((((((p3 ∧ p1) ∨ p2) ∧ (((p4 → True) ∧ True) ∧ p3)) ∨ ((((p2 → p2) ∨ p1) ∧ ((p3 ∧ (p2 ∨ p4)) ∧ p5)) ∨ (False ∨ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308750094758290243024611220233 : (p2 ∨ ((p5 → ((p3 ∧ (p5 ∨ p4)) ∧ ((False → (((p4 ∧ False) ∧ (p2 ∨ ((p2 ∨ (p4 ∨ p4)) ∧ p3))) → p2)) → (p5 → p2)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187335377263820915327430283019 : ((p2 ∧ ((((p3 → p2) ∨ p5) ∧ (True ∨ p3)) → (p2 ∧ False))) → ((p1 ∨ ((((p2 ∧ p1) ∧ p1) ∨ True) → ((p5 ∧ p1) ∧ p1))) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136081606893218220719792770922 : (((p2 ∨ (p1 → (True ∨ ((False ∧ p3) ∧ p2)))) ∧ ((p3 ∨ (((False ∨ p5) ∨ p5) ∨ p1)) ∨ ((False ∨ False) → p1))) ∨ (p5 → (p1 ∨ p3))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- False on the left can always be used.
    apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118627757249001844937261626070 : ((p4 ∨ ((p5 ∧ (p2 → (True → p1))) ∧ (p4 → (((p5 ∨ (False ∨ (p4 ∨ (True → True)))) ∧ p2) ∨ (p3 → (True ∨ p2)))))) ∨ (p3 → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_90937509523523260601065759519 : (((True → p3) ∧ (((p2 → ((p5 ∨ p4) → (p1 ∧ p2))) ∨ ((p3 ∧ p4) → (False ∨ (p2 ∨ p5)))) → (False ∧ (p3 ∨ (p3 ∧ False))))) → p3) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_253024700183285658896624801148 : ((True ∧ p3) → (((False ∨ p1) ∧ p4) ∨ (((p4 ∧ p5) ∨ ((p1 → p2) → ((p4 → ((True → (p5 → False)) ∨ p1)) → p5))) ∨ (p2 ∨ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_591822085179792790179356823155 : ((((((p1 ∧ (p1 ∨ (((p2 → (((p3 ∧ p3) ∧ (p5 → False)) → False)) → p2) ∧ p2))) ∨ (p1 ∨ (p1 ∨ p3))) ∨ (p5 → p3)) ∧ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54304890595349532568713542021 : ((((p2 → p4) ∨ ((p4 ∧ (p5 ∧ p5)) ∨ p1)) ∧ (True → (((((True ∧ p4) ∧ (True ∧ (True ∧ (p4 ∧ False)))) ∧ p3) ∨ False) ∨ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160564201208967342153997522801 : (((((True → (p1 ∧ (p3 ∧ True))) → (True ∧ p4)) → (p2 ∧ p3)) → (p2 ∧ (False ∧ (True ∨ True)))) → ((True ∧ p2) → (p4 → (p3 → p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h2.left
  let h6 := h2.right
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h7 : (((True → (p1 ∧ (p3 ∧ True))) → (True ∧ p4)) → (p2 ∧ p3)) := by
    -- Implications on the right can always be decomposed.
    intro h8
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h6
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h9 := h1 h7
  -- We need to get the right conjuct of h9 based on <expert-advice>.
  let h10 := h9.right
  -- We need to get the left conjuct of h10 based on <expert-advice>.
  let h11 := h10.left
  -- False on the left can always be used.
  apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_668940112263520465955202466543 : (((((p2 ∨ ((p1 ∧ (((p5 → (((True → p3) → p4) ∧ ((True → p4) → True))) ∧ p5) ∧ p5)) ∨ p3)) ∨ True) ∨ (p3 ∨ (p4 ∧ True))) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_182621107379148336669965433596 : ((((True → p4) ∨ (True ∧ (p5 ∧ False))) ∨ (p5 ∨ (True ∨ p2))) ∧ ((((False ∧ p1) → p1) ∧ (p2 ∧ p3)) → (((False ∨ False) ∨ p3) ∨ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47217365714211112956092680123 : ((((((p2 ∧ (True ∧ p3)) → ((True ∨ False) → True)) ∨ p2) → (((((p1 ∧ p4) ∨ (p4 ∧ p5)) ∧ p5) ∧ p5) ∧ True)) ∨ (p1 ∧ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219999675007982959462140452454 : ((p5 → (p5 ∨ (p1 → True))) → ((((p5 → p2) ∧ p1) ∨ p3) ∨ (((p3 ∧ p1) ∨ (p5 → p3)) → (p3 → (((p1 ∨ p5) → p4) ∨ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
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
theorem thm_5_vars_232021238637778767895586248057 : (((p3 ∨ True) → p4) → (p5 → ((((p4 ∧ p3) ∨ (False ∧ p5)) ∨ (p5 ∧ p3)) ∨ ((((p4 ∧ p4) → p3) ∧ (False ∨ True)) ∨ (True ∧ p5))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66619983302480865924135995149 : ((True → ((((((p3 → p1) → p4) ∧ (p1 ∧ p5)) → p2) → (p4 → ((p1 ∨ p3) ∧ p3))) ∨ (p1 → ((True ∧ p3) → (p5 → p5))))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_780195724969200223115326463996 : (((p2 ∨ (((((p1 ∨ (p3 ∨ p4)) ∨ p2) → ((p2 ∨ (p3 → (False ∧ p3))) ∧ (p4 ∨ p3))) ∧ (False → p1)) ∨ (p3 ∨ (p4 → p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



