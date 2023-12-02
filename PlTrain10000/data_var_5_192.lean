variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340693828655323936518220156914 : (p2 → ((((((p1 ∨ (p3 ∧ p5)) ∨ (((p2 ∨ True) ∧ (True ∨ p1)) ∧ (p2 → p2))) → ((p5 → (True → True)) ∧ False)) ∨ p1) ∧ p2) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205621195305972304763971290471 : (((p1 ∧ p2) ∨ ((p5 ∨ p4) ∧ p2)) ∨ (p1 ∨ ((p2 ∧ p1) → (((((p4 ∧ ((p5 ∨ False) ∨ p1)) ∧ (p1 ∧ p5)) ∧ p3) → p5) ∨ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198631396209412911492465975726 : ((p3 ∨ (((p4 ∨ (p3 ∧ p2)) ∨ p3) ∨ p3)) ∨ ((p2 → p2) ∨ ((((False ∨ ((p1 ∧ True) ∨ (p2 ∧ p5))) ∧ (p3 ∨ p3)) ∨ p1) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67457922806833861484888563005 : ((p1 → (((((p4 ∨ (p2 ∨ True)) ∧ True) → ((p4 ∨ False) ∨ p3)) ∧ ((p2 ∧ p5) ∨ (True ∧ p5))) ∨ ((False ∧ (p5 ∧ p4)) ∨ p1))) ∨ False) := by
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
theorem thm_5_vars_158609218622603280648900505541 : ((False ∧ (((p4 ∨ True) → (((False ∨ False) → True) → p5)) ∨ (((p1 ∨ p3) ∧ (True ∨ p2)) → p4))) ∨ (False → ((p2 ∧ p2) → (p5 ∧ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h1
  -- Conjunctions on the left can always be decomposed.
  let h5 := h2.left
  let h6 := h2.right
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136245965923232148022133557111 : (((p5 ∧ (((p2 ∧ True) ∨ p5) ∧ p2)) ∨ ((True ∧ ((p5 ∧ False) ∨ ((p4 ∨ p1) ∨ (True ∧ False)))) → (p1 ∨ True))) ∨ ((p3 → False) ∨ p4)) := by
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
  cases h3
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h10 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h10
    case inr h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- False on the left can always be used.
      apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_330622937374374040725687476600 : (True → (True → ((True ∨ (p1 ∨ (p3 ∧ (((p1 ∨ False) → True) → p1)))) ∧ ((p4 ∨ (p2 ∨ p3)) → ((((p4 ∧ p1) ∨ True) ∨ p5) ∨ p5))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230598847226839051616808175933 : (((p1 → p5) ∧ p5) → (((((p3 ∨ (True ∨ False)) ∧ (p4 ∧ p4)) ∨ (((p1 ∨ p1) ∧ (p4 ∨ p5)) ∨ True)) ∧ (p2 → p4)) ∨ (p3 → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208210760359319834934467721126 : (((p2 → (p4 ∧ p5)) → (p2 → False)) → (((p1 ∨ (((p5 ∨ (p4 → p2)) ∧ ((False ∨ p3) → False)) ∧ p3)) → p1) ∧ (False → (True → p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h9 =>
      -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
      have h10 : (False ∨ p3) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h6
      -- We have shown the premise of h8, we can now drive its conclusion.
      let h11 := h8 h10
      -- False on the left can always be used.
      apply False.elim h11
    case inr h12 =>
      -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
      have h13 : (False ∨ p3) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h6
      -- We have shown the premise of h8, we can now drive its conclusion.
      let h14 := h8 h13
      -- False on the left can always be used.
      apply False.elim h14
  -- Implications on the right can always be decomposed.
  intro h15
  -- Implications on the right can always be decomposed.
  intro h16
  -- False on the left can always be used.
  apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136854949114457102603486666201 : (((p4 ∧ p4) ∨ ((((p2 → ((p2 ∨ (True → (True ∧ p3))) ∨ (p2 ∧ True))) → False) ∨ ((False → p3) ∨ p4)) ∨ p2)) ∨ ((p4 ∧ p1) ∨ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52293121168140767996943653519 : (((((p3 ∧ (p3 ∧ (p4 ∧ (True ∨ ((True ∧ p5) ∧ p5))))) ∨ p5) ∧ p3) ∧ (p5 ∧ ((p4 → p3) ∧ ((p4 → (p1 ∧ p4)) → True)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234309581483825346964281488617 : ((p1 → (False ∧ p4)) → ((p1 → p2) ∧ (p4 ∨ (True → (((((False ∨ p4) ∧ p4) ∧ ((p5 ∨ p1) ∧ (p5 → (p1 → False)))) → p5) ∨ False))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : p1 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- False on the left can always be used.
  apply False.elim h5
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h6
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h7
  -- Conjunctions on the left can always be decomposed.
  let h8 := h7.left
  let h9 := h7.right
  -- Conjunctions on the left can always be decomposed.
  let h10 := h8.left
  let h11 := h8.right
  -- Disjunctions on the left can always be decomposed.
  cases h10
  case inl h12 =>
    -- False on the left can always be used.
    apply False.elim h12
  case inr h13 =>
    -- Conjunctions on the left can always be decomposed.
    let h14 := h9.left
    let h15 := h9.right
    -- Disjunctions on the left can always be decomposed.
    cases h14
    case inl h16 =>
      -- One of the premise coincides with the conclusion.
      exact h16
    case inr h17 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h18 : p1 := by
        -- One of the premise coincides with the conclusion.
        exact h17
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h19 := h1 h18
      -- We need to get the left conjuct of h19 based on <expert-advice>.
      let h20 := h19.left
      -- False on the left can always be used.
      apply False.elim h20



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351169224804483019660229194936 : (p4 → (((((p5 ∧ (p3 ∨ (p5 ∧ (False → p4)))) ∨ (False ∧ p3)) ∨ p1) ∨ ((p1 ∨ (True ∨ (p1 ∧ p5))) → p4)) ∧ (True → (p4 ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- One of the premise coincides with the conclusion.
      exact h1
  -- Implications on the right can always be decomposed.
  intro h9
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227772216078124237197759126704 : ((p1 ∧ (False → False)) ∨ ((p1 ∨ (((p5 ∨ p1) ∧ p4) ∨ True)) ∨ ((((p1 ∨ p5) ∨ p5) ∧ p2) ∨ (p3 ∨ (False ∨ (p4 ∨ (True ∧ False))))))) := by
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
theorem thm_5_vars_42827414446503672684155544963 : (((p1 → ((p2 ∨ p3) ∨ (p2 ∨ (p5 ∧ ((True ∨ ((p2 ∧ (p3 ∧ p1)) ∨ p5)) ∧ ((((p3 ∨ p5) ∧ True) ∨ p1) → True)))))) ∨ True) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193253547343112556435101450274 : (((p4 ∧ (p1 → False)) ∧ (p2 → (False ∧ (True → p1)))) → ((p4 → ((True → ((p3 ∨ (p5 ∧ p2)) ∧ (p3 → p1))) ∨ (p5 → True))) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h7
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119279978504847751597887849526 : ((p3 → (((((((((True ∧ p3) ∨ p4) → (p3 ∧ p2)) ∨ p4) → ((p3 ∨ (p2 ∧ p4)) → p5)) ∧ p2) ∨ p1) ∧ p4) ∨ p3)) ∨ (p5 ∨ p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62991447372195915433574286608 : ((p4 ∧ (True → (((p5 ∧ ((((p1 → ((p2 ∨ True) ∧ ((p3 → p4) ∧ (False → p3)))) ∧ p4) ∨ p4) ∨ False)) ∨ (p2 ∧ False)) ∧ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218058588313080744366411219517 : (((p3 ∨ p4) ∧ (p4 → False)) → (p3 ∨ ((True → ((p5 ∧ p3) → (False ∧ p5))) ∧ (p2 ∨ ((p1 ∧ p1) ∧ ((p4 ∧ (p4 ∧ p4)) → p4)))))) := by
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
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h6 : p4 := by
      -- One of the premise coincides with the conclusion.
      exact h5
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h7 := h3 h6
    -- False on the left can always be used.
    apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_151191879612344487058103387374 : ((((((((p3 ∨ p5) ∨ False) → True) ∨ True) ∧ p2) → ((p5 → p2) ∧ ((p5 → p2) ∧ (p1 ∨ True)))) → p3) → ((p2 → False) ∨ (True → p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : ((((((p3 ∨ p5) ∨ False) → True) ∨ True) ∧ p2) → ((p5 → p2) ∧ ((p5 → p2) ∧ (p1 ∨ True)))) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h9 =>
      -- One of the premise coincides with the conclusion.
      exact h7
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h10
    -- Conjunctions on the left can always be decomposed.
    let h11 := h4.left
    let h12 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h13 =>
      -- One of the premise coincides with the conclusion.
      exact h12
    case inr h14 =>
      -- One of the premise coincides with the conclusion.
      exact h12
    -- Conjunctions on the left can always be decomposed.
    let h15 := h4.left
    let h16 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h15
    case inl h17 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h18 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h19 := h1 h3
  -- One of the premise coincides with the conclusion.
  exact h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_615372943556222269271404455842 : ((((((p5 ∧ (False → p4)) ∨ (((p3 ∧ (p3 ∧ (p2 ∧ True))) ∨ (p1 ∧ p5)) ∧ False)) ∨ ((p3 → ((p4 ∨ False) → p1)) ∨ True)) ∨ p4) ∨ p1) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_623808193782140202566975248879 : ((((p1 ∨ (((p2 ∧ p3) ∨ p5) ∨ (((p4 ∧ (((p4 ∧ False) → p3) ∧ (p4 ∨ (((p1 ∨ p1) → True) → False)))) ∧ p5) → p2))) ∨ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_733223981353848711555389810662 : ((((p3 ∧ p2) ∧ (p5 → ((p1 ∨ (((p4 ∨ p2) ∨ (((False ∨ (False ∧ p3)) ∧ p4) ∨ False)) ∧ ((p3 → p3) ∨ (p3 → p3)))) ∨ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_695902330852566722130340306723 : (((((False → p5) ∨ (p1 ∨ (p1 ∨ (p1 → ((p1 ∧ (p5 → p1)) → p2))))) → (((((p5 → (p3 ∨ p4)) ∨ p3) ∨ p3) → p3) → p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245585131319097696509000851604 : ((p3 ∧ False) ∨ (((((False ∧ False) → (((p5 → p4) ∨ p2) ∨ ((p4 ∧ (p4 → (p5 → False))) ∧ p1))) ∧ ((False → p4) ∨ p2)) → p1) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149232398229189437803707991953 : (((p5 ∧ False) ∨ (p5 ∧ (False ∧ ((p4 ∨ p3) → (True → ((p1 ∨ p3) ∧ ((p1 ∧ p1) → (True → p3)))))))) ∨ (((False ∨ p2) ∨ p5) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115183854049505617256258856197 : ((((p2 → (False ∧ (False ∨ (p3 ∨ p2)))) ∨ (p4 ∧ p4)) ∧ (((False ∧ p5) → ((p5 → (p5 ∨ False)) ∨ True)) → (False ∧ p1))) ∨ (True ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172295585838284730350258366473 : ((((p1 ∨ ((p2 ∧ p5) → (p2 → False))) ∨ p4) → ((p5 → p3) ∨ (False ∨ True))) ∨ ((((p4 ∧ (False ∨ p4)) ∧ (p1 ∨ p1)) → p5) ∧ p3)) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307415545777876947043030615100 : (p1 ∨ (p4 ∨ (p5 → ((((p2 → ((True ∨ ((p2 → (p1 ∨ p3)) ∨ p2)) ∧ p1)) → ((p5 ∨ p4) → ((p5 → False) → False))) ∨ p3) ∨ p1)))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h6 : p5 := by
      -- One of the premise coincides with the conclusion.
      exact h5
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h7 := h4 h6
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h9 : p5 := by
      -- One of the premise coincides with the conclusion.
      exact h1
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h10 := h4 h9
    -- False on the left can always be used.
    apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_550036570973827777395633160237 : (((p1 ∨ (((p2 ∧ p4) ∨ ((((((True ∨ p4) ∧ False) → (p2 ∨ p3)) ∨ False) → False) → ((p1 ∨ p1) ∧ ((p1 → p2) ∨ p2)))) ∨ p1)) ∧ True) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((((True ∨ p4) ∧ False) → (p2 ∨ p3)) ∨ False) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
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
      apply False.elim h5
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h8 := h1 h2
  -- False on the left can always be used.
  apply False.elim h8
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h9 : ((((True ∨ p4) ∧ False) → (p2 ∨ p3)) ∨ False) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h10
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h13 =>
      -- False on the left can always be used.
      apply False.elim h12
    case inr h14 =>
      -- False on the left can always be used.
      apply False.elim h12
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h15 := h1 h9
  -- False on the left can always be used.
  apply False.elim h15
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118498164195921117644040020299 : ((p3 ∨ ((((True → p5) ∨ ((p4 → (False ∨ (p5 → p3))) ∨ p3)) ∨ p3) ∨ (((p2 → p3) ∧ ((p4 ∨ True) ∧ False)) → p5))) ∨ (p4 ∨ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- False on the left can always be used.
    apply False.elim h5
  case inr h7 =>
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_621312468754944989883492707509 : ((((True ∧ (((p2 ∨ ((p5 ∧ p1) ∨ p1)) ∨ p1) → ((((True ∧ False) ∨ p2) ∧ p5) → (p4 ∧ ((True → False) ∨ (p1 → p5)))))) ∨ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214555221989929334201437476812 : (((False ∨ p5) ∧ (p2 → True)) ∨ ((p3 ∨ (p4 → p5)) → (((((((p5 → True) → p2) ∧ (p5 ∨ p1)) ∧ (p3 → p2)) → p2) ∨ p2) ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h9 : p3 := by
        -- One of the premise coincides with the conclusion.
        exact h2
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h10 := h5 h9
      -- One of the premise coincides with the conclusion.
      exact h10
    case inr h11 =>
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h12 : p3 := by
        -- One of the premise coincides with the conclusion.
        exact h2
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h13 := h5 h12
      -- One of the premise coincides with the conclusion.
      exact h13
  case inr h14 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h15
    -- Conjunctions on the left can always be decomposed.
    let h16 := h15.left
    let h17 := h15.right
    -- Conjunctions on the left can always be decomposed.
    let h18 := h16.left
    let h19 := h16.right
    -- Disjunctions on the left can always be decomposed.
    cases h19
    case inl h20 =>
      -- We want to use the implication h18 based on <expert-advice>. So we show its premise.
      have h21 : (p5 → True) := by
        -- Implications on the right can always be decomposed.
        intro h22
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h18, we can now drive its conclusion.
      let h23 := h18 h21
      -- One of the premise coincides with the conclusion.
      exact h23
    case inr h24 =>
      -- We want to use the implication h18 based on <expert-advice>. So we show its premise.
      have h25 : (p5 → True) := by
        -- Implications on the right can always be decomposed.
        intro h26
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h18, we can now drive its conclusion.
      let h27 := h18 h25
      -- One of the premise coincides with the conclusion.
      exact h27



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_860219222081430303800390542832 : (((((p3 ∧ ((((p4 → (p4 ∨ (((p5 ∧ True) ∧ p4) ∧ False))) ∨ p3) ∧ ((False ∧ p5) ∨ (p1 → p5))) → p3)) ∨ (p3 → p3)) → p2) → p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p3 ∧ ((((p4 → (p4 ∨ (((p5 ∧ True) ∧ p4) ∧ False))) ∨ p3) ∧ ((False ∧ p5) ∨ (p1 → p5))) → p3)) ∨ (p3 → p3)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_625646822067384513003412608153 : ((((p1 → ((((False ∧ False) ∨ (p3 → ((p3 → (p1 → (((p5 → p3) ∨ p2) → (True ∨ True)))) ∧ False))) → False) ∧ (True → p5))) ∨ True) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_670623870632005429794931486868 : (((((p1 ∧ p5) → (((((((p3 ∧ False) ∨ ((p2 → p1) ∨ False)) → (p4 ∨ False)) ∧ p4) ∨ True) ∨ True) ∨ p2)) ∨ (p3 → (p4 → True))) ∨ p5) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_170320284257647964374513720109 : (((p3 ∨ ((p1 ∨ False) ∨ p2)) ∨ ((((True ∧ p1) ∧ False) → p5) → (p3 → True))) ∧ ((((False ∧ ((p2 ∨ p5) ∧ p2)) ∨ True) → p2) → p2)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : ((False ∧ ((p2 ∨ p5) ∧ p2)) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356265440348000037244150859776 : (p5 → (((p1 ∧ p1) ∧ ((p4 ∨ (True ∨ ((p4 ∧ ((False ∨ p1) → p2)) → p5))) ∧ False)) ∨ ((((p1 ∨ p1) ∨ p5) ∨ (p3 ∧ p4)) ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_617968608462512920557239106672 : (((((p5 → (True ∨ (p1 → (p4 → False)))) → (p3 ∨ ((p2 → ((((True ∧ True) ∧ p2) → (p4 ∨ (p2 ∨ p3))) ∨ p4)) → p2))) ∨ True) ∨ False) ∧ True) := by
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
theorem thm_5_vars_50456341333155036016196494568 : (((p4 ∨ ((((p4 ∨ ((False → (p1 → False)) → p3)) ∨ p4) → ((p2 ∧ p4) ∧ (True → p1))) ∨ p3)) ∨ ((p4 ∧ (False ∧ p3)) → p3)) ∨ False) := by
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
  let h4 := h3.left
  let h5 := h3.right
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_800767760849857737760909306585 : (((p2 → ((((True → (p4 → p5)) ∧ (p5 → (((p2 → ((True ∧ p1) ∧ p1)) ∧ p5) ∧ p4))) ∨ ((p5 ∧ False) ∨ p2)) ∧ (False → p3))) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158651529012394141743103406980 : ((p1 ∧ (((p1 → p1) → p2) → ((((p1 → (p2 → (p3 → p3))) → (False ∧ p1)) ∨ p2) ∨ p4))) ∨ ((p5 → ((p5 ∧ True) → True)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60734072355862068256557781842 : ((True ∧ ((True ∨ ((True ∧ True) ∧ p5)) → (p4 ∧ (((True ∨ p1) → (p1 ∧ (False ∧ p3))) ∨ (p5 → ((p5 ∧ p1) ∨ (p3 ∧ p3))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_891351078261285529777106456120 : ((((p1 → (p2 → (((p5 ∧ False) ∨ (p5 ∧ ((((p2 ∧ p4) ∨ p3) ∧ (((p4 ∨ p2) → p1) ∨ p5)) ∨ p5))) ∨ p1))) → (p3 ∨ False)) → p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p1 → (p2 → (((p5 ∧ False) ∨ (p5 ∧ ((((p2 ∧ p4) ∨ p3) ∧ (((p4 ∨ p2) → p1) ∨ p5)) ∨ p5))) ∨ p1))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h2
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- False on the left can always be used.
    apply False.elim h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_615518793558603723257804161113 : ((((((((p2 ∨ (((False ∧ p1) → p1) ∨ p4)) ∧ False) ∧ p3) → ((True ∧ p2) ∨ p3)) → (((p1 → (p1 ∨ False)) → p1) ∨ p4)) ∨ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_209225339143952345149636840614 : ((p5 ∨ ((True ∧ (p1 ∨ p1)) ∧ p5)) → (((p3 ∨ p2) ∧ (((((((False ∨ True) → p4) → p5) ∧ p3) → False) → False) ∧ p1)) ∨ (True → p5))) := by
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
    exact h2
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h12
      -- One of the premise coincides with the conclusion.
      exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158923557882260083615087775928 : ((p1 ∨ (p5 ∨ ((((True → p4) ∧ (((True → p2) ∨ False) → (p4 ∧ p4))) → p3) ∨ (p3 ∨ True)))) ∨ (p4 → (p5 ∧ (p3 ∨ (p4 ∧ p5))))) := by
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
theorem thm_5_vars_168659832544198715062034075111 : ((p4 ∧ (p5 ∨ (p1 ∧ (((((p5 ∨ p3) ∨ (p2 ∧ p1)) ∨ (p4 → p5)) → p5) → p2)))) → ((p1 ∧ (((p2 ∨ p3) ∧ p2) ∨ p4)) ∨ True)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38624646138999975233262468168 : (((((((p3 ∧ (p3 → True)) ∧ True) → p2) → p3) ∨ ((p1 → ((p4 → False) → (False ∨ p4))) ∧ (((p1 → p3) ∨ p1) → p5))) ∧ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303704627695961527051943153717 : (p1 ∨ (((((((((True ∨ (True → (False → ((p5 → True) ∨ p5)))) → (p5 → p2)) ∨ p2) → p5) → (True → p2)) ∨ p2) ∧ p1) ∧ p5) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54674599004636988537054596747 : (((((p3 → ((p1 → p1) ∨ False)) ∨ p3) → p5) → ((p4 ∨ (p2 ∨ (False ∧ (p3 ∧ (False ∨ p2))))) ∨ (((p4 ∧ False) ∧ p5) → p3))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165637183932139599548739863514 : (((p2 ∧ ((p2 ∧ p2) ∧ (False → p3))) ∧ ((((p1 ∨ p2) → p5) → p4) → (p4 ∧ p2))) ∨ ((False ∧ (((p5 ∧ p5) ∧ p4) → p4)) → p3)) := by
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
theorem thm_5_vars_783284002964153610113422588129 : (((p3 ∨ ((((((p1 ∧ (p4 ∨ p4)) ∨ (p3 → False)) ∧ (True ∧ False)) → (p4 ∨ (p2 → p1))) → p3) ∨ (False ∨ ((p1 ∨ True) ∨ p5)))) ∨ p5) ∧ True) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313467467232705641436646671042 : (p3 ∨ (((((p2 ∨ ((((p3 ∨ False) → p1) ∧ ((p3 → p4) ∨ (True → ((p4 ∧ False) ∧ True)))) ∨ p1)) → False) → (p1 → p2)) → False) → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p2 ∨ ((((p3 ∨ False) → p1) ∧ ((p3 → p4) ∨ (True → ((p4 ∧ False) ∧ True)))) ∨ p1)) → False) → (p1 → p2)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h5 : (p2 ∨ ((((p3 ∨ False) → p1) ∧ ((p3 → p4) ∨ (True → ((p4 ∧ False) ∧ True)))) ∨ p1)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h6 := h3 h5
    -- False on the left can always be used.
    apply False.elim h6
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h7 := h1 h2
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61503974239813039690676275943 : ((p1 ∧ ((p4 ∨ ((p5 → ((p3 ∨ p3) → False)) → (((p3 ∧ (p2 → (p3 ∧ p3))) ∧ False) → False))) ∧ ((p3 ∨ p3) ∨ (p5 ∨ p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57641858914369092793510322372 : ((((True ∨ p2) ∨ False) → (((p3 ∨ p4) ∨ p5) ∨ (p3 ∨ ((False → (p1 → ((False → p4) ∧ p1))) ∨ ((p1 ∨ (True ∨ p2)) ∧ p4))))) ∨ p3) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h4
      -- Implications on the right can always be decomposed.
      intro h5
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h6
      -- False on the left can always be used.
      apply False.elim h6
      -- False on the left can always be used.
      apply False.elim h4
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h8
      -- Implications on the right can always be decomposed.
      intro h9
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h10
      -- False on the left can always be used.
      apply False.elim h10
      -- False on the left can always be used.
      apply False.elim h8
  case inr h11 =>
    -- False on the left can always be used.
    apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47598608285523124663161162019 : (((p3 → ((p3 ∧ (((p2 → p3) → (p2 ∧ (p2 ∧ True))) ∨ True)) ∧ (((p5 ∨ (False ∨ p2)) ∨ (p3 ∨ False)) ∨ False))) ∨ (True ∨ p1)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191822107665478854232838011304 : ((p2 ∨ (p3 → ((True ∨ p1) → (p2 ∨ (False ∧ p3))))) ∨ ((((((False → p2) ∧ (p3 ∨ p4)) ∧ ((p1 ∨ p3) → p4)) → p5) → p3) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1546424934884416088769516121 : ((p3 ∧ ((((p5 ∨ ((((p1 ∧ p3) ∧ ((False → False) ∨ p2)) ∧ (False ∨ p5)) → p2)) ∧ (p4 ∧ p2)) ∧ p1) ∨ p4)) ∨ (True ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_226047422731348996837952476851 : (((p5 ∧ p1) ∨ p2) ∨ ((p2 ∨ (p3 ∨ (p4 ∨ (p4 → ((p5 → ((False ∧ (True ∨ p2)) ∨ p1)) ∨ False))))) ∨ ((p3 → False) ∨ (True ∨ False)))) := by
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
theorem thm_5_vars_310839788654514546691427501947 : (p2 ∨ (((p4 → p4) ∧ True) → (((True → ((p3 ∨ ((p5 → p2) → False)) ∧ False)) → (p3 ∨ (True → ((p4 → (p1 → True)) ∧ p1)))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_115109774076647348563007511996 : ((((((p1 ∧ p3) ∧ (True ∨ (True ∧ (p3 ∨ p5)))) ∧ p2) → p4) → (p5 ∨ (((p2 ∨ False) ∧ p4) ∨ (True → (p1 ∧ p2))))) ∨ (True ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_593905658796517855730489277185 : ((((((p1 ∨ ((p4 → (p4 → (p2 → (p2 ∨ ((True ∧ p1) ∧ p1))))) → p2)) → (True → p3)) ∨ ((p2 → (p1 ∧ p3)) ∧ p4)) ∧ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117040566852125620793429406611 : (((p3 ∨ p3) → (False ∧ (p3 ∧ (False ∧ (False ∧ (((True → (((True → (p5 ∨ p5)) ∧ p3) ∨ p5)) ∨ p4) ∨ (p2 ∧ p3))))))) ∨ (True ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158804212155343578380768547954 : ((p5 ∧ ((True → True) → (p3 ∨ (p1 → (((((p3 ∧ False) → p4) ∧ (p3 ∨ p4)) → p2) ∨ p3))))) ∨ (p2 → ((p1 → (False → True)) ∨ p1))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_806387595072832645678097185180 : (((p4 → ((p5 ∨ (p2 ∨ (p4 → (True → (p2 ∨ (True ∧ (((p3 ∨ (((p3 ∨ p3) ∨ (p4 ∧ p5)) → False)) ∨ p3) ∨ True))))))) ∨ p2)) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174079459392205026250923145514 : (((((p5 ∧ ((p2 → (p5 ∨ (False → p4))) → p2)) → p2) → False) ∧ (p2 → False)) → (((True ∨ (p1 ∨ False)) → False) ∨ ((True → p3) ∨ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : ((p5 ∧ ((p2 → (p5 ∨ (False → p4))) → p2)) → p2) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h8 : (p2 → (p5 ∨ (False → p4))) := by
      -- Implications on the right can always be decomposed.
      intro h9
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h6
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h10 := h7 h8
    -- One of the premise coincides with the conclusion.
    exact h10
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h11 := h2 h4
  -- False on the left can always be used.
  apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337442255086396416754860633232 : (p1 → (((p5 → (p2 → p1)) ∧ (((p3 ∧ p5) ∨ (p1 ∨ True)) → (((False ∧ (p4 ∨ (True ∨ p3))) → False) ∧ False))) → (p5 ∨ (False ∨ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h5 : ((p3 ∧ p5) ∨ (p1 ∨ True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h6 := h4 h5
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184089260550530367527346252401 : (((((p2 ∧ p5) ∨ p5) ∨ (p3 ∨ (p4 → (p1 ∧ p5)))) ∨ p2) ∨ ((p2 ∨ ((p3 → (((False → False) ∧ (p2 ∨ True)) ∨ False)) ∨ p4)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_658221656891398343000829405267 : ((((p5 ∧ ((((p2 → (p1 ∨ (p2 → False))) ∨ ((p1 → p1) ∨ ((p4 ∨ p4) → p1))) → True) → ((p3 ∨ p5) → p3))) ∨ (True ∨ p1)) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_160227792990816744737714085077 : ((((p5 ∧ (False ∨ (False ∧ (p2 ∧ ((True → (p3 ∧ p1)) → p5))))) → (p3 ∧ True)) ∨ (False → True)) → ((p4 ∨ p3) ∨ (False → (p2 ∧ False)))) := by
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
    -- False on the left can always be used.
    apply False.elim h3
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- False on the left can always be used.
    apply False.elim h5
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_139181271137759034253548474293 : ((((((False ∨ (p5 ∨ p3)) ∧ p1) ∨ p5) ∨ (((p2 → False) ∧ ((p5 ∨ p1) ∧ p1)) ∨ (False ∧ (True ∧ p3)))) ∨ p3) → (False ∨ (p3 → p3))) := by
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
        -- Conjunctions on the left can always be decomposed.
        let h5 := h4.left
        let h6 := h4.right
        -- Disjunctions on the left can always be decomposed.
        cases h5
        case inl h7 =>
          -- False on the left can always be used.
          apply False.elim h7
        case inr h8 =>
          -- Disjunctions on the left can always be decomposed.
          cases h8
          case inl h9 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h10
            -- One of the premise coincides with the conclusion.
            exact h10
          case inr h11 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h12
            -- One of the premise coincides with the conclusion.
            exact h12
      case inr h13 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h14
        -- One of the premise coincides with the conclusion.
        exact h14
    case inr h15 =>
      -- Disjunctions on the left can always be decomposed.
      cases h15
      case inl h16 =>
        -- Conjunctions on the left can always be decomposed.
        let h17 := h16.left
        let h18 := h16.right
        -- Conjunctions on the left can always be decomposed.
        let h19 := h18.left
        let h20 := h18.right
        -- Disjunctions on the left can always be decomposed.
        cases h19
        case inl h21 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h22
          -- One of the premise coincides with the conclusion.
          exact h22
        case inr h23 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h24
          -- One of the premise coincides with the conclusion.
          exact h24
      case inr h25 =>
        -- Conjunctions on the left can always be decomposed.
        let h26 := h25.left
        let h27 := h25.right
        -- False on the left can always be used.
        apply False.elim h26
  case inr h28 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h29
    -- One of the premise coincides with the conclusion.
    exact h29



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148209191453645112035215838159 : (((p3 ∨ (((True → p3) ∨ ((p4 ∨ p1) ∧ p3)) ∧ (p5 ∨ ((p2 → p3) ∨ p2)))) ∧ ((p4 → p1) ∨ True)) ∨ (((p2 ∧ True) ∧ p4) → p4)) := by
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
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56301945779616589476610027051 : (((((False ∨ p2) → p3) ∧ p1) → (p5 ∧ (((p4 → (p1 ∨ p2)) ∧ ((p2 ∨ p2) → p5)) ∨ (p4 ∧ (p1 ∧ ((p3 → p2) ∧ True)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112856522472294600074015203993 : (((((p4 ∧ p4) ∨ p5) ∨ (((p1 → p1) ∧ (p3 → p5)) ∨ (p3 ∨ (p5 ∨ (True ∨ (p2 ∨ ((p2 → p1) ∨ p3))))))) → p1) ∨ (p1 → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64194443230004291105265124201 : ((False ∨ (False ∧ ((p5 ∧ ((((p4 ∨ True) → False) ∨ (((True ∨ True) ∨ (True → p1)) ∧ p2)) ∧ (False ∨ (p4 → (p5 ∨ p1))))) ∨ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113517317194120854803039263958 : (((((((p4 ∧ (True ∨ p5)) ∧ True) → p2) ∧ (p4 ∨ p2)) ∧ ((p5 ∨ (p3 ∧ p5)) ∨ ((p4 → False) ∧ p5))) ∨ (p2 → True)) ∨ (p2 ∧ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_196741615981461260068861896370 : (((((p3 ∨ p5) ∨ False) ∧ (p5 ∧ True)) ∧ False) ∨ (p3 ∨ (True ∨ (p1 → (((((p1 ∧ True) ∧ p4) ∧ (p5 ∧ (True ∨ p2))) ∧ False) → p3))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51565157078579611111623171690 : (((p1 ∨ ((((((p3 ∨ p3) ∨ p1) ∨ (p5 ∧ p5)) → ((False ∨ p4) ∧ True)) ∧ p2) → p5)) → (((p3 ∨ (p3 ∧ p2)) → p1) → p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61372351256878421378962853181 : ((p1 ∧ (((p2 ∧ ((((False ∨ p1) ∨ (((p1 ∨ ((p2 ∨ p3) ∨ p4)) ∧ ((p1 ∨ p5) ∧ False)) ∨ False)) → p2) ∧ p1)) ∧ False) ∨ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_777720393230209250303762946750 : (((p1 ∨ ((p5 ∨ (True → ((p2 ∨ p3) ∨ (False ∧ p5)))) → ((True ∧ (((p3 ∨ ((p5 ∨ (p4 → False)) → p3)) ∧ p1) ∨ True)) ∨ p3))) ∨ p4) ∧ True) := by
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
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_143814008572228015253785374030 : ((((p2 ∨ (((p4 ∧ p5) → p5) ∧ (p4 ∨ (((p4 ∨ (True → p4)) → (p2 ∨ p4)) ∨ p5)))) ∨ p4) ∨ p1) ∧ ((p4 ∧ p5) ∨ (p5 → p5))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  exact h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h7 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h8 := h6 h7
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h8
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h9
  -- One of the premise coincides with the conclusion.
  exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305669613576424061533135364364 : (p1 ∨ ((((p1 → p4) ∨ ((p1 → (p2 → False)) ∧ p3)) ∨ False) ∨ ((((p1 → (((p5 ∨ p5) ∨ False) ∨ False)) ∧ (True ∨ p5)) ∧ False) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137764726754788877376515094359 : ((p2 ∨ (((False → ((((True ∧ (p3 ∧ p2)) → True) ∧ (p3 ∧ ((p1 ∧ p2) ∧ False))) → p2)) ∨ p3) → (p4 ∨ p2))) ∨ ((p4 → p5) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180763952931307261794902160585 : (((((p3 ∧ p2) ∨ False) ∧ True) → ((p3 ∨ (False ∧ p3)) ∨ (p4 → p3))) → ((p1 ∧ (p4 ∧ (p4 → (p4 → p4)))) → ((p1 → False) → p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h8 : p1 := by
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h9 := h3 h8
  -- False on the left can always be used.
  apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37565918712739810570077884092 : ((((p4 ∨ ((p2 ∧ (p2 → ((False ∨ False) ∧ p3))) ∨ (((((p2 ∧ False) ∨ ((p5 ∨ p2) ∧ True)) ∧ p3) ∨ False) ∧ p1))) ∨ True) ∧ True) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159019460184326549287444033630 : ((p4 ∨ (((p2 ∨ p2) ∨ ((((True ∨ p1) ∨ False) → False) ∨ p3)) → ((p1 ∧ False) ∨ (False → p2)))) ∨ ((p1 ∧ (p3 ∧ (p2 ∧ p1))) ∧ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
      -- False on the left can always be used.
      apply False.elim h4
    case inr h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- False on the left can always be used.
      apply False.elim h6
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h9
      -- False on the left can always be used.
      apply False.elim h9
    case inr h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h11
      -- False on the left can always be used.
      apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205872527564996109174382434528 : ((True ∧ ((p4 ∨ (p2 ∧ p5)) ∧ True)) ∨ (False ∨ ((((p1 ∧ p5) ∧ (False ∨ (p1 ∧ p4))) ∨ False) ∨ (True ∧ (((p5 ∧ p5) ∧ p4) ∨ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197466073128825764921037805731 : ((((p2 → (p2 ∧ p3)) → False) ∧ (p3 → p1)) ∨ (((p1 ∨ p2) → False) ∨ (False → ((True → ((True ∧ p4) ∧ ((p1 → p3) → False))) → p4)))) := by
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
theorem thm_5_vars_631085334799939020818950145600 : (((((((((p1 ∨ p3) ∧ p2) ∨ p3) ∨ (((p4 → p1) ∨ ((p4 ∨ p4) ∧ (p1 → False))) ∨ ((p1 ∧ p1) ∨ True))) ∨ p4) → p3) → p3) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((((p1 ∨ p3) ∧ p2) ∨ p3) ∨ (((p4 → p1) ∨ ((p4 ∨ p4) ∧ (p1 → False))) ∨ ((p1 ∧ p1) ∨ True))) ∨ p4) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_608756174265242618431351964562 : (((((((True → False) ∨ (((((True ∨ (((True ∧ p1) ∧ p3) ∧ False)) → False) ∨ p2) ∨ False) ∨ p5)) ∧ ((p2 ∨ p4) → p3)) ∨ True) ∨ False) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_664465623830362014155936369936 : ((((p4 ∨ ((p1 ∨ ((True ∨ ((True → (p1 ∧ p5)) → (p3 → (False ∧ ((p4 → p1) ∨ True))))) ∨ p5)) ∨ (p5 ∨ p1))) → (p2 ∨ True)) ∨ p5) ∧ True) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h5 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h6 =>
        -- Disjunctions on the left can always be decomposed.
        cases h6
        case inl h7 =>
          -- Disjunctions on the left can always be decomposed.
          cases h7
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
        case inr h10 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
    case inr h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h13 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179725757421272112926153730165 : (((((False ∨ (p4 ∨ True)) ∨ ((p1 ∧ (p2 → p3)) → p2)) → p2) ∧ True) → ((p3 ∨ (p1 ∨ p2)) ∧ (True ∨ ((True ∧ p4) → (p5 → True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : ((False ∨ (p4 ∨ True)) ∨ ((p1 ∧ (p2 → p3)) → p2)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h5
  -- Conjunctions on the left can always be decomposed.
  let h6 := h1.left
  let h7 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147323786553319894226152303160 : (((((p3 ∧ (((False ∧ (p1 → p4)) ∨ (p4 → ((p2 ∧ p4) → p5))) ∨ p4)) → p1) ∧ (p5 ∨ p2)) ∨ p3) ∨ (((p3 → p1) ∨ p4) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215178721521346372747239055136 : ((True ∧ ((p3 ∨ p2) → False)) ∨ (((p1 → p1) → ((p5 ∧ p5) → (((p5 → False) → (p2 ∨ (False ∧ p3))) ∨ p3))) ∨ (p2 ∨ (p5 ∨ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h5
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h6 : p5 := by
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h7 := h5 h6
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_153050301784406757369689588758 : ((p3 ∧ ((((p2 ∧ p5) ∧ (((((p4 ∨ False) ∨ ((p3 ∧ p3) ∧ p2)) ∨ p2) ∧ True) ∨ p3)) ∧ p2) ∧ p2)) → (p4 ∨ (p4 ∨ (p3 → p2)))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h10 := h8.left
  let h11 := h8.right
  -- Disjunctions on the left can always be decomposed.
  cases h9
  case inl h12 =>
    -- Conjunctions on the left can always be decomposed.
    let h13 := h12.left
    let h14 := h12.right
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h15 =>
      -- Disjunctions on the left can always be decomposed.
      cases h15
      case inl h16 =>
        -- Disjunctions on the left can always be decomposed.
        cases h16
        case inl h17 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h17
        case inr h18 =>
          -- False on the left can always be used.
          apply False.elim h18
      case inr h19 =>
        -- Conjunctions on the left can always be decomposed.
        let h20 := h19.left
        let h21 := h19.right
        -- Conjunctions on the left can always be decomposed.
        let h22 := h20.left
        let h23 := h20.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h24
        -- One of the premise coincides with the conclusion.
        exact h5
    case inr h25 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h26
      -- One of the premise coincides with the conclusion.
      exact h5
  case inr h27 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h28
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135804232147404810229127032440 : (((p1 ∨ (p4 ∨ ((p3 ∧ False) ∨ (((False ∧ p2) ∧ (p2 ∨ p2)) ∨ p5)))) → (p3 → ((True ∧ p2) ∨ (p1 ∨ p3)))) ∨ ((p5 ∨ p5) → False)) := by
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
    exact h3
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Conjunctions on the left can always be decomposed.
        let h8 := h7.left
        let h9 := h7.right
        -- False on the left can always be used.
        apply False.elim h9
      case inr h10 =>
        -- Disjunctions on the left can always be decomposed.
        cases h10
        case inl h11 =>
          -- Conjunctions on the left can always be decomposed.
          let h12 := h11.left
          let h13 := h11.right
          -- Conjunctions on the left can always be decomposed.
          let h14 := h12.left
          let h15 := h12.right
          -- False on the left can always be used.
          apply False.elim h14
        case inr h16 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136794188669060632131079025382 : (((p1 → p5) ∧ (p2 ∨ (((((p1 → p1) → (p4 ∧ p1)) ∧ p4) → p2) ∧ (((p5 ∨ True) ∨ (p1 ∨ p5)) ∧ p3)))) ∨ (p2 ∨ (p3 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_621491022279984441591159200747 : ((((False ∧ (((p3 → ((((p3 → False) ∧ (((p5 ∨ ((False ∧ True) ∨ (True ∧ True))) → p5) ∧ p3)) → p1) ∧ p5)) ∨ p4) → p3)) ∨ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_15948244407723979993093510037 : (((True ∨ (p5 → (((p5 ∨ (((p3 ∨ p4) ∧ ((p5 ∧ p4) → p2)) → (p3 ∨ p2))) ∧ (False → (p5 ∧ p3))) ∨ True))) → (p2 ∨ True)) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



