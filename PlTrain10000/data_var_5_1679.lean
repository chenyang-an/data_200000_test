variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68320678100247445707935043639 : ((p3 → ((((p1 ∧ p3) → (p5 ∧ False)) ∨ ((p4 → True) → ((p5 ∧ p3) ∧ (p3 → p4)))) ∨ (True ∧ (False → (p2 → (True → p2)))))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219859779980655384002975770634 : ((p3 → (False ∨ (p4 → False))) → ((False ∨ ((((((p2 → (p5 ∧ p1)) ∨ p4) ∨ True) → p3) → (p1 ∧ p4)) ∧ (True → p2))) ∨ (p1 → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_216042860404302965512481171792 : ((p5 ∨ ((p4 → p5) → p5)) ∨ ((p2 ∨ (((p5 ∨ p2) ∧ ((((p1 ∧ p4) ∧ p4) ∧ (True ∨ (True ∧ p4))) → False)) → p4)) ∨ (True ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165268701086335754844305726704 : ((((False → (p5 ∧ (p4 ∨ (p1 ∧ ((p4 → True) ∨ (True → p1)))))) ∨ p4) → (p4 ∨ False)) ∨ ((p2 → (True ∨ True)) ∨ (p5 → (True → p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_202532350541223354172981606223 : (((True ∧ (p3 ∧ True)) ∨ (False → p2)) ∧ ((((p4 ∧ (False ∧ ((True → p3) ∧ p4))) ∨ p5) ∨ (((p1 → (False ∨ False)) ∨ False) → p5)) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_804358189779136124527155225248 : (((p3 → (((((p1 ∨ (True ∨ (p5 ∧ (True ∨ p2)))) ∧ p4) ∧ p3) → p3) → ((True ∧ (p1 → p3)) ∧ ((True → p1) ∨ (True ∨ p5))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_151930291910966163972300459274 : (((((p4 ∧ (p4 → p5)) → (p1 → p3)) ∨ ((False → False) → p1)) ∧ (True → ((p5 → True) ∧ (p5 ∨ p2)))) → ((p4 ∧ p3) → (False ∨ p3))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177981873857352407851351205010 : (((p2 ∧ ((p1 ∧ p3) ∧ ((p2 ∧ False) ∨ (p1 → (False → p3))))) ∨ True) ∨ (((True → True) ∧ (((p1 → False) → p2) → (True ∧ False))) ∨ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_751034986677008161347405971050 : (((True ∧ (((False → p1) → (True → p5)) ∧ (True ∧ ((p5 → (((True ∨ p4) → ((p3 ∧ (p4 → (p3 ∧ False))) ∧ True)) → p5)) → p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67884854754420156712569657790 : ((p2 → ((p1 ∨ ((p1 ∨ ((p2 ∧ p5) ∧ False)) ∧ (p1 ∨ ((((p3 ∧ True) ∨ p4) ∧ True) ∨ p1)))) ∨ (((True ∧ True) ∧ p3) ∨ p2))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_229203687971194739210667908162 : ((True → (p2 → p4)) ∨ ((False → (True ∧ ((p1 ∧ (p2 ∨ p5)) → p1))) → (((True ∧ p3) ∧ ((False → (True ∨ p3)) → p1)) ∨ (True ∨ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51271166091771741727947359516 : (((True ∧ ((((p4 ∨ (((p3 ∧ True) ∧ (p4 ∧ p3)) ∨ p1)) → False) ∨ (False → p1)) → p2)) ∨ (p2 ∨ (p4 → (p5 ∨ (True ∨ False))))) ∨ p1) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172589078828747556141660334787 : ((((p4 → p1) ∨ True) → ((p5 ∧ ((p1 ∨ False) → ((p5 ∨ True) ∧ False))) ∨ p4)) ∨ (True ∧ ((p3 ∧ (p3 → p4)) → ((True ∧ p4) ∨ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : p3 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193301718156506976553445010148 : (((False ∧ (p2 ∧ p3)) ∨ ((True → p1) ∨ (p5 ∧ True))) → ((p3 ∨ ((p5 → ((p2 ∧ True) ∨ ((True ∨ p1) ∧ p5))) ∧ (False ∨ True))) ∨ p3)) := by
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h7
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
      -- One of the premise coincides with the conclusion.
      exact h7
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
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
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h11
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
      -- One of the premise coincides with the conclusion.
      exact h11
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304693393991620264246437372914 : (p1 ∨ (((p5 ∨ (((p5 ∧ ((False → False) ∨ (p1 ∧ False))) ∨ True) → (True → (True ∧ ((p5 → p5) ∧ (p2 ∨ p1)))))) ∨ p3) ∨ (True ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160361416375331077932534156472 : ((((((p2 ∧ (p1 ∨ p5)) ∨ (p1 ∧ (p3 → True))) → (True ∨ p1)) → p5) ∧ ((False ∨ p3) → p3)) → ((False ∨ (p2 ∨ (p5 ∧ True))) ∧ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (((p2 ∧ (p1 ∨ p5)) ∨ (p1 ∧ (p3 → True))) → (True ∨ p1)) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h10 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h14 := h2 h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h14
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h15 := h1.left
  let h16 := h1.right
  -- We want to use the implication h15 based on <expert-advice>. So we show its premise.
  have h17 : (((p2 ∧ (p1 ∨ p5)) ∨ (p1 ∧ (p3 → True))) → (True ∨ p1)) := by
    -- Implications on the right can always be decomposed.
    intro h18
    -- Disjunctions on the left can always be decomposed.
    cases h18
    case inl h19 =>
      -- Conjunctions on the left can always be decomposed.
      let h20 := h19.left
      let h21 := h19.right
      -- Disjunctions on the left can always be decomposed.
      cases h21
      case inl h22 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h23 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h24 =>
      -- Conjunctions on the left can always be decomposed.
      let h25 := h24.left
      let h26 := h24.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  -- We have shown the premise of h15, we can now drive its conclusion.
  let h27 := h15 h17
  -- One of the premise coincides with the conclusion.
  exact h27



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323007524525446258392230896646 : (p5 ∨ ((True → ((((False → p5) ∨ p3) ∨ (False → ((p5 → ((p4 ∨ p5) ∧ (True ∧ p1))) ∨ (False ∧ ((p5 ∧ p5) ∧ p5))))) ∧ p1)) → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338688731183155798575053545127 : (p1 → ((p1 ∨ p4) ∧ ((((p2 ∨ ((True ∧ p3) → (p3 → ((p4 ∧ (p4 ∧ p2)) ∨ True)))) → p5) → ((p5 ∨ p1) ∧ p5)) ∨ (p3 ∨ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_787717726231236145796121328770 : (((p4 ∨ (p5 ∨ ((p4 ∧ (False ∧ True)) ∨ ((True → (p5 → (p5 → (((True ∧ p1) ∧ False) → ((p4 ∨ True) → True))))) ∧ (p3 ∨ True))))) ∨ p2) ∧ True) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307791715712545552360903764691 : (p1 ∨ (p4 → ((p3 → ((p1 ∨ p1) → ((p2 ∨ p5) → (((p4 → p4) → (p5 → p2)) ∨ (((p3 ∧ p2) → p1) ∨ (p2 ∧ p2)))))) ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h5
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h5
      -- One of the premise coincides with the conclusion.
      exact h5
  case inr h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h10
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- One of the premise coincides with the conclusion.
      exact h9
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
      exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301005034035363113915018504398 : (False ∨ ((p5 ∧ (((((p2 → p3) ∨ False) ∨ (p4 ∨ p5)) ∨ p3) ∨ p5)) → (((p5 ∧ p5) ∧ False) ∨ ((p3 ∧ ((p2 ∧ p4) ∨ False)) ∨ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Disjunctions on the left can always be decomposed.
        cases h6
        case inl h7 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h2
        case inr h8 =>
          -- False on the left can always be used.
          apply False.elim h8
      case inr h9 =>
        -- Disjunctions on the left can always be decomposed.
        cases h9
        case inl h10 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h2
        case inr h11 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h11
    case inr h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
  case inr h13 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180737084485837571389602951263 : ((((True ∨ (p2 ∧ p5)) ∨ True) ∨ (p5 ∧ (((p5 → p3) → p1) ∧ p5))) → ((((p4 → False) → ((p3 ∨ p3) → True)) → (False ∧ True)) ∨ True)) := by
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
        -- Conjunctions on the left can always be decomposed.
        let h6 := h5.left
        let h7 := h5.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191804623329790237975492009032 : ((p2 ∨ ((((p2 ∧ p2) ∧ p5) → p5) → (p5 ∧ True))) ∨ ((((((p3 ∨ p1) ∧ (True → p5)) ∨ (p4 ∧ p4)) ∧ p5) → (p3 ∨ True)) ∨ p5)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134116485369430984305354583891 : ((((((p2 → (p2 ∨ ((((p2 ∨ (p3 ∨ p5)) ∧ p3) ∧ p3) → (p4 ∨ True)))) → p3) ∧ False) ∨ (p5 ∧ p4)) ∨ p1) ∨ (p1 ∨ (False → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_745525046065531542022480410891 : ((((True ∨ False) → ((True ∧ ((p4 ∧ (p5 ∨ p3)) ∨ ((False ∨ False) ∨ p1))) ∨ ((True ∨ p1) ∧ (p3 ∨ (((p1 ∨ False) ∧ False) → p2))))) ∨ p5) ∧ True) := by
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
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- False on the left can always be used.
      apply False.elim h5
    case inr h7 =>
      -- False on the left can always be used.
      apply False.elim h7
  case inr h8 =>
    -- False on the left can always be used.
    apply False.elim h8
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314656112717681316799872411149 : (p3 ∨ (((p2 → ((True ∧ p5) ∧ p5)) → (((p4 ∨ ((p4 ∨ True) ∧ p3)) ∧ True) ∧ True)) ∨ (p4 ∨ (True ∨ ((True ∨ (p1 → p4)) → False))))) := by
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
theorem thm_5_vars_172631003228132023811349281844 : (((p4 ∧ False) ∧ ((True ∧ ((False ∧ (p4 → ((False ∨ True) ∧ p2))) → p5)) → p3)) ∨ (((False → p2) ∨ False) ∨ ((True ∨ p3) → (p4 → p3)))) := by
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
theorem thm_5_vars_238174896846528750236535939441 : ((True ∨ p4) ∧ (((((p4 ∧ p1) ∨ ((False ∨ p2) ∧ ((False ∧ (True ∨ (p3 → ((p3 ∧ p4) → (p4 → True))))) ∨ p2))) ∧ False) ∧ True) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181983756870267512192351512389 : (((((p5 ∨ (p1 → (p4 ∧ p3))) ∨ (False → True)) → p2) ∨ True) ∧ (p5 ∨ (True ∨ (p5 ∨ (((p1 ∧ p1) ∧ True) ∧ (p1 → (p5 → True))))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_314480499756511054409783099908 : (p3 ∨ ((True ∧ (True → ((((((p1 → p5) ∧ (False → False)) ∧ p1) ∨ (p3 ∧ (True → False))) ∧ p4) ∧ False))) → (p2 ∨ ((p2 ∧ p1) → False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184380517141646664738421487987 : (((False → (((p1 ∨ p1) ∨ p1) → (p4 → (True ∧ p5)))) → False) ∨ ((p4 → ((p2 → (False → ((p4 ∨ (True ∧ p3)) ∨ p3))) ∧ p1)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65001194424978028678542282900 : ((p2 ∨ (((p5 ∧ p2) → p3) → (((p3 ∨ (p4 ∧ p1)) ∨ ((p1 ∧ True) ∨ (p3 ∨ True))) ∧ (False → (p1 → ((True ∨ p4) ∨ p1)))))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191898014517148172735773645194 : ((p5 ∨ ((p2 ∧ (p4 ∧ (p1 → (p5 → p5)))) → p3)) ∨ ((((p5 ∨ (p2 ∧ p1)) ∨ p3) ∧ True) ∨ ((p5 ∧ (False ∧ p2)) → (False → p1)))) := by
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
theorem thm_5_vars_186280240772821882153934186612 : ((((((((p5 → True) ∨ True) ∧ p5) ∧ p1) ∧ p3) → p5) → False) → (p1 ∧ (p2 ∨ ((False ∨ p4) → ((((p1 → p2) ∧ p1) ∧ p5) ∨ p3))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((((((p5 → True) ∨ True) ∧ p5) ∧ p1) ∧ p3) → p5) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h10 =>
      -- One of the premise coincides with the conclusion.
      exact h9
    case inr h11 =>
      -- One of the premise coincides with the conclusion.
      exact h9
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h12 := h1 h2
  -- False on the left can always be used.
  apply False.elim h12
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h13 : ((((((p5 → True) ∨ True) ∧ p5) ∧ p1) ∧ p3) → p5) := by
    -- Implications on the right can always be decomposed.
    intro h14
    -- Conjunctions on the left can always be decomposed.
    let h15 := h14.left
    let h16 := h14.right
    -- Conjunctions on the left can always be decomposed.
    let h17 := h15.left
    let h18 := h15.right
    -- Conjunctions on the left can always be decomposed.
    let h19 := h17.left
    let h20 := h17.right
    -- Disjunctions on the left can always be decomposed.
    cases h19
    case inl h21 =>
      -- One of the premise coincides with the conclusion.
      exact h20
    case inr h22 =>
      -- One of the premise coincides with the conclusion.
      exact h20
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h23 := h1 h13
  -- False on the left can always be used.
  apply False.elim h23



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_432629835925507334866822105392 : ((((p3 → (((p4 ∧ (True ∨ p4)) ∨ (True → p4)) → ((((True ∧ ((p3 → False) → False)) ∧ (p4 ∨ True)) ∧ p4) ∧ p2))) ∨ (False ∨ True)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_725232475019740064510775669160 : ((((p2 → (False → p2)) ∧ ((p1 ∧ (((p4 → (p5 ∧ (p1 ∨ p4))) ∧ (p1 → p4)) → ((((p1 ∧ p2) ∧ p4) → p4) ∧ False))) ∨ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193693285419186124584324398683 : ((p1 ∧ ((p4 ∨ True) ∨ (True ∧ ((True → p5) → p1)))) → ((p3 ∧ (p5 ∧ (p5 → (p2 ∨ True)))) ∨ (p1 ∧ (p1 ∧ (p3 → (p4 → p1)))))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h2
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h2
      -- Implications on the right can always be decomposed.
      intro h6
      -- Implications on the right can always be decomposed.
      intro h7
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h2
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h2
      -- Implications on the right can always be decomposed.
      intro h9
      -- Implications on the right can always be decomposed.
      intro h10
      -- One of the premise coincides with the conclusion.
      exact h2
  case inr h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h2
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h2
    -- Implications on the right can always be decomposed.
    intro h14
    -- Implications on the right can always be decomposed.
    intro h15
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_786144134964907901888204940280 : (((p4 ∨ (((((p2 ∨ ((p1 → (p1 ∧ False)) ∧ (p2 ∧ (p1 → p3)))) → p1) → (p2 ∧ (False → True))) → p3) ∨ (p3 ∨ (p4 ∧ p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58596362921910250705523306296 : (((False → False) ∧ (((((p1 → ((((True ∨ p5) ∨ p1) → p1) ∧ (p3 → p1))) ∨ (p5 ∨ p4)) → ((p5 ∨ p5) → p1)) → p1) ∧ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164090840345706094859939482358 : ((p2 ∨ (((((p2 → (p3 ∨ p3)) ∧ ((True ∧ p3) ∧ p4)) ∧ False) ∧ (True ∨ p3)) → p2)) ∧ ((p4 ∨ p3) ∨ ((p3 ∨ (True ∧ p3)) ∨ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Conjunctions on the left can always be decomposed.
  let h8 := h7.left
  let h9 := h7.right
  -- Conjunctions on the left can always be decomposed.
  let h10 := h8.left
  let h11 := h8.right
  -- False on the left can always be used.
  apply False.elim h5
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340878479982048925312183800850 : (p2 → (((p3 ∨ (True → (True ∧ ((((p5 ∧ False) ∨ ((False ∨ p1) ∨ p4)) → False) ∨ p1)))) ∨ (((p4 ∨ p1) ∧ True) ∨ (False → p3))) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217503931113420225925475064727 : ((((p2 ∨ p2) ∧ p5) → p1) → (((p4 ∧ (False → p3)) ∧ (p2 ∧ p4)) → ((p3 ∧ ((True → (p3 → p5)) ∨ (p1 ∨ (False ∨ True)))) → p3))) := by
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
  cases h5
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h2.left
    let h8 := h2.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h7.left
    let h10 := h7.right
    -- Conjunctions on the left can always be decomposed.
    let h11 := h8.left
    let h12 := h8.right
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h13 =>
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h14 =>
      -- Conjunctions on the left can always be decomposed.
      let h15 := h2.left
      let h16 := h2.right
      -- Conjunctions on the left can always be decomposed.
      let h17 := h15.left
      let h18 := h15.right
      -- Conjunctions on the left can always be decomposed.
      let h19 := h16.left
      let h20 := h16.right
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h21 =>
      -- Disjunctions on the left can always be decomposed.
      cases h21
      case inl h22 =>
        -- False on the left can always be used.
        apply False.elim h22
      case inr h23 =>
        -- Conjunctions on the left can always be decomposed.
        let h24 := h2.left
        let h25 := h2.right
        -- Conjunctions on the left can always be decomposed.
        let h26 := h24.left
        let h27 := h24.right
        -- Conjunctions on the left can always be decomposed.
        let h28 := h25.left
        let h29 := h25.right
        -- One of the premise coincides with the conclusion.
        exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_616416015513611541394163965569 : ((((((((True → p1) ∧ (((p4 ∧ p2) ∨ p4) → p4)) ∨ p3) → True) → (p4 ∨ (((p1 ∨ ((p5 → p5) → p3)) → p3) ∨ True))) ∨ p5) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114685931651460945189387259349 : (((p5 ∨ ((True ∧ ((((p3 → ((p1 → p5) ∧ True)) ∧ p1) ∨ p2) ∨ p5)) ∨ p4)) ∨ (((p5 → True) → False) ∧ (p1 → True))) ∨ (p4 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310487362278930578958420090909 : (p2 ∨ (((((p2 ∨ p3) ∧ p3) ∨ False) ∨ True) ∨ (p5 ∧ ((False → (((p4 ∨ p2) ∧ (((p4 → (True → p3)) ∨ p5) ∧ p1)) → p4)) ∧ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112606333727927679325463637443 : (((((p2 → ((((p3 ∧ (p1 ∧ p1)) ∨ ((p5 ∨ False) → (p2 → False))) ∨ (p3 ∨ False)) ∧ p4)) ∨ p1) ∨ (p5 → p5)) → p5) ∨ (True ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45425844861105433480758238397 : (((True ∨ (((((p2 ∨ ((p2 ∧ p2) ∧ p2)) ∨ ((p1 ∧ (True → (True → True))) → ((p4 ∧ p1) ∨ p2))) ∨ True) ∧ p5) ∨ p4)) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173937044284184653404405716159 : ((((((p4 ∧ ((False → p3) ∧ p2)) ∧ p1) ∧ p1) ∧ ((True ∧ True) ∨ p1)) → True) → ((((p5 → (p5 → p1)) ∨ p5) ∨ p5) ∨ (True ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116298335927586431814766972617 : (((True → (p5 ∨ p1)) ∨ ((p2 → p3) ∨ (((p4 ∨ (False ∧ p4)) ∨ ((p3 → (p2 ∨ True)) ∧ p1)) ∨ (False → (p4 ∨ p2))))) ∨ (p3 ∨ p5)) := by
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
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_654556928392876743625262742241 : (((((p1 ∨ (((((p2 ∧ False) ∨ ((False ∨ (True → (p5 → (True → p4)))) ∨ p2)) → False) ∧ p3) ∧ (p4 ∧ False))) ∨ p5) ∨ (True ∨ p2)) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_139848128452276747217130805879 : (((p4 → (((((p2 ∧ p5) → p3) → p1) ∧ ((p5 → p4) → (p1 ∨ (p1 → p5)))) ∧ (False ∨ (True → True)))) → p4) → (p3 ∨ (False → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2080687788514990511854800148 : ((((True → p5) ∨ (((p4 ∧ p4) ∨ (p2 ∨ p2)) ∧ (p3 ∧ (p5 ∨ True)))) → (p5 → p1)) ∨ (False → ((True ∧ True) → (False → p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43567542521510112426030551912 : (((((False ∧ (True ∧ (p2 ∨ ((((False → p1) → p4) ∧ p3) → (((p1 → (p4 → p5)) → p1) ∧ (p3 ∨ p2)))))) ∧ p2) → p4) → p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337859746534305011704931410322 : (p1 → (((p2 → (p2 ∨ (p3 → ((False ∧ p4) → (p2 → p2))))) → (True ∧ p2)) ∨ ((((p3 ∨ p2) → p5) ∧ (p3 ∨ p1)) → (False → False)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199225973739455149469408377835 : (((p5 ∨ (((p3 → False) → p4) ∧ p3)) ∧ p1) → (((((p3 ∨ (p5 ∧ (p5 → (p4 ∨ (p1 ∧ p4))))) → (True → False)) ∨ True) ∨ p4) ∨ p1)) := by
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
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341204735020097093507068893874 : (p2 → ((((((p4 ∧ (p1 → (((p2 → (p5 → p2)) ∧ (False ∧ False)) → (p5 ∧ False)))) → p3) ∧ (False ∧ True)) ∨ (p3 → p2)) → False) → p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : ((((p4 ∧ (p1 → (((p2 → (p5 → p2)) ∧ (False ∧ False)) → (p5 ∧ False)))) → p3) ∧ (False ∧ True)) ∨ (p3 → p2)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h3
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_653472373880614855612644767168 : ((((p4 → (p1 ∨ ((((((p2 ∨ (True → (p5 → (p2 ∧ True)))) ∨ (p4 ∨ p4)) → (p3 ∧ p4)) → False) ∨ p1) ∧ p4))) ∧ (p5 ∨ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_610780026282241617285075367881 : ((((((((p4 ∧ (p2 → (p4 ∧ ((p2 ∧ False) → p1)))) → (p3 ∧ p4)) ∧ (p1 → True)) ∨ ((True ∨ (p2 → p1)) ∨ True)) → False) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160389152177021539657900344026 : (((p3 ∨ ((p4 → (((p3 ∧ True) → ((p2 → p1) → p4)) ∨ False)) → p4)) ∧ ((p2 → p2) ∨ p2)) → (p4 → (((True → False) ∨ True) ∨ p3))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5
  case inr h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h9 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h10 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_142073184631580177774836755152 : ((True ∧ (((True → ((p1 ∨ False) ∨ (p5 ∧ True))) → (p1 → True)) → ((((p5 ∧ p2) → True) ∧ (p3 ∨ True)) ∧ False))) → ((p5 ∨ p4) ∨ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : ((True → ((p1 ∨ False) ∨ (p5 ∧ True))) → (p1 → True)) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- Implications on the right can always be decomposed.
    intro h6
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h7 := h3 h4
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61614341443975100572114395387 : ((p1 ∧ ((p4 → p1) ∧ (p2 ∧ ((((((False ∧ p5) ∧ (False ∧ p3)) ∧ (False → p4)) ∨ (False ∨ p1)) ∧ (True ∧ p2)) ∧ (p5 ∧ p4))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113231376342876113171056148119 : (((((p2 ∨ (p1 → (True ∧ False))) ∧ ((p3 → ((False ∨ p4) ∨ p1)) → ((p1 ∧ True) ∧ (p2 ∧ p5)))) → p2) ∧ (p5 → p5)) ∨ (False → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354700557007720948602035158798 : (p5 → (((((p3 ∨ p1) ∧ ((((p2 ∧ True) ∧ (p5 ∨ ((p3 ∨ False) ∨ (p3 ∧ (p1 ∨ p1))))) ∨ p5) ∨ p2)) → p1) → (p5 → p3)) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328139096982701057856141246104 : (True → ((False ∧ (p3 ∨ ((p1 ∧ ((((p3 → ((((p3 → p2) ∨ False) → p2) ∧ p4)) ∨ p2) ∨ p3) ∧ p2)) ∧ p5))) ∨ ((False → p2) ∨ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158782178660194697079848292843 : ((p5 ∧ ((((p1 ∧ p2) ∧ (False ∨ ((p1 ∨ (False ∨ p2)) ∨ (p1 ∨ (False ∨ p1))))) ∨ p5) ∨ p2)) ∨ ((p1 → p1) ∧ ((p2 → p2) ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165971039995662775313700875552 : (((p3 → False) ∧ ((False ∨ ((p3 → (p1 → p4)) ∧ (False ∨ (p5 ∧ (p2 → False))))) → p4)) ∨ ((p3 → (True → (p5 ∧ (False → p3)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_782094636973526252021374122163 : (((p3 ∨ (((((True ∨ (((p1 → (p3 ∨ True)) → p2) → True)) ∨ p2) ∧ (((p3 → True) → ((p5 → p3) → p4)) ∧ False)) ∨ p2) ∧ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112322441676693327945809170907 : (((p3 → ((p3 ∧ (p1 ∧ (p4 → False))) → (((((False ∨ p3) ∨ p3) → ((p1 ∨ (p1 → True)) ∧ p4)) ∧ p1) → False))) ∨ True) ∨ (p1 ∨ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63284006468620087807508723319 : ((p5 ∧ (((p4 ∨ p2) → (p3 → p4)) → (p1 → (True → ((((True ∨ p4) ∨ p4) → (p2 → (((True ∨ p4) ∨ p5) ∧ p1))) → p5))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114311502866785214282664775975 : ((((((True → (p4 ∨ p1)) ∨ p3) ∨ p2) → (((p3 ∨ p4) ∨ (p4 ∨ True)) ∨ (p4 ∨ False))) ∧ (((p3 → p2) ∨ p5) → True)) ∨ (p5 ∨ p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h4 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h4
  case inr h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- Implications on the right can always be decomposed.
  intro h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191447961244595342451752160716 : (((False → p5) → (((p3 → False) ∨ p5) ∨ (p5 → p2))) ∨ (False → (True → (True → ((((p2 ∨ p5) ∨ (p2 ∨ (False ∨ p4))) → True) → p2))))) := by
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
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148317391284194143117485275489 : (((p3 ∨ ((p1 → (p3 → ((p3 ∧ p2) ∧ p5))) ∧ (p1 ∧ ((False ∧ True) → p3)))) → (p1 → (p5 ∨ True))) ∨ ((p3 → (p4 ∨ p4)) → p4)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52031486989792965969416201206 : (((p3 ∨ ((((p5 ∧ (p4 ∨ p3)) ∧ (p5 ∧ (p2 → p4))) → p1) → (p1 ∨ False))) ∨ ((p1 → p3) → ((True → True) ∨ (True ∨ p2)))) ∨ p1) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_831036744778055406517406851 : ((p5 ∧ ((p1 ∧ p5) ∧ (((p3 ∨ (p1 ∨ ((p4 ∧ ((p2 ∨ p3) → p1)) → p3))) ∨ (((p2 ∨ p2) ∧ p2) ∨ True)) → p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64325693676959557540921632696 : ((p1 ∨ ((((p1 → p5) → ((p1 → p4) → ((False → True) ∧ p5))) ∨ ((p5 ∧ False) ∧ (p5 → (p4 → ((p3 ∧ p2) → p3))))) ∧ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214601333743414122831923225376 : (((p5 ∨ False) ∧ (p1 ∧ True)) ∨ (False ∨ (p2 ∨ (p1 ∨ (False ∨ (p3 ∨ ((p1 → (((((p5 ∨ p4) ∨ False) ∨ p2) → False) ∨ True)) ∨ p5))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_143782218982316623337515072036 : ((((p1 ∨ ((p2 ∧ (p2 ∨ ((p4 ∧ p3) ∨ ((p4 ∧ p2) → (p2 ∨ (False → p4)))))) ∧ False)) ∧ p5) ∨ True) ∧ ((False → p4) ∨ (p4 ∧ p3))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111991890991248330062913206421 : (((((p3 → False) ∧ (p3 → p4)) ∧ (p2 ∧ (p4 ∧ ((True → (True ∧ (p2 ∨ ((p2 ∨ p4) ∨ (p2 ∧ p2))))) ∧ False)))) ∨ True) ∨ (p3 ∧ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136840999684373277543945755914 : (((p2 ∧ p2) ∨ ((((p1 ∧ (False ∧ p2)) → p3) ∧ ((False ∨ p1) → p2)) ∧ (True → ((p1 ∨ (p5 ∧ p4)) → p5)))) ∨ ((True → False) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64372498723996748316569808116 : ((p1 ∨ (((p3 → p2) ∨ (((((p1 ∨ (((p5 → False) → p4) ∨ p1)) → (False ∨ True)) → p3) ∧ p5) → (p3 ∨ (p4 ∧ p1)))) ∨ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166870376790721293109577555320 : ((((((p4 ∨ ((p5 ∧ (p4 ∨ (p4 → p1))) ∧ p2)) → True) → False) ∨ (p2 → p3)) ∧ p5) → ((p3 ∨ ((p4 ∨ (p2 ∨ True)) → p4)) ∨ p5)) := by
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
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322464466094445142709729709412 : (p5 ∨ ((((True ∨ p4) ∧ p4) → ((((((p3 ∧ False) ∧ p5) → (True ∨ (p4 ∨ p3))) → (p3 → p1)) ∨ (p2 → (p1 → True))) ∨ p2)) ∨ p1)) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Implications on the right can always be decomposed.
    intro h6
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h7 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- Implications on the right can always be decomposed.
    intro h9
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_175317289345077590685868991233 : ((p4 ∨ (((p2 ∧ p4) ∨ ((p3 ∧ p5) → (p5 ∨ (p1 ∧ p5)))) ∨ (p5 → p1))) → ((((False ∧ p5) ∨ (p4 → True)) ∨ True) ∨ (p3 → p2))) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h5 =>
        -- Conjunctions on the left can always be decomposed.
        let h6 := h5.left
        let h7 := h5.right
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h8 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h9 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_120060744248504006564169303938 : (((((p3 ∧ ((p1 ∨ p4) ∧ (p3 ∧ p3))) ∨ True) → (p1 ∧ ((((((p2 → p2) ∨ False) ∨ p3) ∧ p3) → p4) ∧ False))) ∧ p1) → (p2 → p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h5 : ((p3 ∧ ((p1 ∨ p4) ∧ (p3 ∧ p3))) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h5
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148013806747941609214614760883 : (((((((True ∧ ((p5 ∨ (p4 ∨ p3)) ∨ p1)) ∧ p4) ∨ p2) ∨ p2) → ((p5 → p3) ∨ p4)) ∨ (p5 → True)) ∨ (p3 ∨ ((p4 ∧ False) → p3))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190590769337636688005439568254 : ((((True → p3) ∧ ((p5 ∧ (p2 → p5)) ∨ p3)) → False) ∨ ((p4 ∨ (p5 ∨ False)) → ((((p2 ∨ (p3 ∧ False)) ∧ (p4 → p5)) ∨ False) ∨ True))) := by
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
theorem thm_5_vars_792254058910843356593579134636 : (((True → (((p4 → (True → p1)) ∨ ((p3 → ((p5 ∧ False) ∧ p2)) ∧ (p3 → (True → (True → p3))))) → ((False ∨ p4) ∨ (p2 → False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56396376798796599362892216617 : ((((p1 ∧ (p1 → p3)) → p2) → ((((False → p5) ∧ p1) → ((p4 ∨ (False → False)) → (p5 ∨ p1))) → ((True → p5) → (p2 → p5)))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h5 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h5
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301434682332606767135470828780 : (False ∨ ((p1 ∧ (p1 ∧ (p4 ∨ p5))) → (p5 → (((((False → False) ∧ p3) ∧ ((((p4 → p1) → (p4 ∨ p5)) → p4) ∨ p2)) ∨ False) ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_343664100137977116643916244090 : (p2 → (True ∧ (p3 ∨ (((p3 ∨ (((p1 ∨ p1) ∧ ((((False ∧ False) → True) ∧ p2) → ((True → p2) ∧ p3))) ∧ False)) ∧ p2) ∨ (True ∨ False))))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173225890870056781131909257713 : ((True → (((((True → p1) ∨ (p3 ∨ p1)) ∨ True) → (True ∧ (p4 → False))) ∧ True)) ∨ (((False ∧ p4) ∨ True) ∨ ((p4 ∨ False) ∧ (p4 ∨ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47705244991591200344819846967 : (((((((True → (p1 ∨ (p4 ∨ ((p4 → False) → p1)))) ∧ (p3 ∧ (((False → p2) → True) ∨ p2))) → True) ∧ p2) ∨ p2) → (p4 ∧ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68943995656769094098143218711 : ((p4 → (True → ((((((p2 ∨ False) ∨ p5) ∧ (p2 → (((True ∨ (True ∧ p4)) → (p4 ∨ p3)) ∧ p2))) ∧ True) ∨ (p3 ∨ p2)) → p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187191955541920983940131827752 : (((False ∨ True) → ((((p5 ∧ True) → p5) ∨ (p2 ∧ False)) ∧ False)) → (((True ∧ ((False ∧ p2) ∨ (p4 → ((False ∧ p5) ∧ False)))) → True) ∧ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : (False ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168236299417242109846875517624 : ((((p4 ∧ p3) ∨ p4) → (((((p3 ∨ p1) ∨ (True → p1)) ∨ True) ∨ p2) → (p2 → p2))) → ((p1 ∨ (False ∧ ((p1 → p5) ∨ p1))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197772044463384180534181398626 : (((p5 ∨ (p1 → False)) ∧ ((p1 ∨ p4) → False)) ∨ (p5 ∨ (((True ∧ ((p1 ∨ ((p1 ∨ ((p5 ∨ p5) → p4)) ∧ p3)) → p1)) ∨ False) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_4047578124152354409277653954 : (p2 ∨ (((False ∧ (p1 ∨ p5)) ∧ (True ∧ ((p2 → p1) ∧ p4))) ∨ ((False → p3) ∨ (((False ∨ (p2 → (False → p1))) → p3) ∧ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179240697552143869930446697266 : ((p5 ∧ (((True → (False ∧ (p1 ∧ (p4 ∧ True)))) ∨ (p4 ∨ True)) → False)) ∨ (((p4 ∨ (((p1 ∨ False) ∧ (True ∨ p3)) ∨ p3)) ∧ p1) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308384086577434351230347079773 : (p2 ∨ ((((p4 ∨ (p3 ∧ ((p4 → (((p4 ∧ p1) ∨ p2) ∧ p3)) ∨ (True → p1)))) ∧ (((False ∨ (p5 ∨ False)) ∧ p3) → False)) ∨ p2) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53248917682432867515636014202 : ((((p1 ∨ p1) ∧ (p3 → ((False ∧ p2) ∨ (p2 ∨ (False ∧ p4))))) ∨ (((p3 ∧ ((p1 ∨ (p5 ∨ p5)) ∧ False)) ∧ True) → (True ∨ True))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  cases h6
  case inl h8 =>
    -- False on the left can always be used.
    apply False.elim h7
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- False on the left can always be used.
      apply False.elim h7
    case inr h11 =>
      -- False on the left can always be used.
      apply False.elim h7



