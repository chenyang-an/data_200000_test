variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231471446114978324965948695261 : (((p3 → False) ∨ True) → (((p3 ∧ p5) ∧ (p2 → p1)) ∨ (p1 → ((False ∨ True) ∨ ((((True ∨ (True ∨ (p3 ∨ True))) ∨ p3) → p4) ∧ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_154476421803479557350902396832 : (((((((False ∨ p1) ∧ p2) ∧ (p5 ∨ p1)) ∨ ((False → p4) ∨ p5)) → ((p5 ∧ p5) ∧ False)) → p4) ∧ (p5 → ((p3 ∨ True) ∧ (False ∨ p5)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((((False ∨ p1) ∧ p2) ∧ (p5 ∨ p1)) ∨ ((False → p4) ∨ p5)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- False on the left can always be used.
  apply False.elim h5
  -- Implications on the right can always be decomposed.
  intro h6
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119258315493054582116131592294 : ((p2 → (True → ((p5 ∨ ((p3 ∧ ((True ∧ (p1 ∨ False)) ∨ True)) ∨ ((p5 ∨ p2) ∨ ((p1 → p1) ∨ True)))) ∧ (False → False)))) ∨ (p3 ∨ p1)) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_633229999584336859202533559209 : (((((False → (((p2 → p3) → (((((p5 → ((p3 ∨ p2) ∨ (p4 ∧ p4))) → True) → p1) → False) ∨ p1)) → p3)) ∧ (p5 → p4)) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113579681612327830113497048168 : (((p1 ∧ (((p2 → (p1 ∧ (p5 → (((p4 → p5) → (True ∧ True)) ∨ (p2 → (True ∧ p3)))))) ∧ p4) ∨ True)) ∨ (False ∧ False)) ∨ (False → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_730412021948908138236231867914 : ((((True ∧ (p3 → p1)) → ((p2 ∨ ((((p4 ∧ p4) ∧ (p2 ∨ (p2 ∧ (p3 ∨ p5)))) ∨ ((False ∨ (p5 → p3)) → p2)) ∨ True)) → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66044621365067168343053273292 : ((p5 ∨ ((p3 → (p1 ∨ ((p5 → ((p3 ∧ p2) ∧ (p1 → p3))) → (p1 → ((p5 ∨ False) ∨ (True → (False ∧ (False ∨ p2)))))))) ∧ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_255182152584590056955879643082 : ((p4 ∧ p4) → ((((p2 ∧ (((p4 → p3) → False) ∨ True)) ∨ True) → ((p2 → p5) ∧ ((p3 → (((p5 → False) ∨ False) ∧ p1)) ∧ p2))) ∨ True)) := by
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
theorem thm_5_vars_340019159475336608805254864852 : (p1 → (p1 → (p4 → ((((((p5 ∨ p4) ∧ p3) ∧ False) ∧ (((p2 ∧ ((p5 ∧ p5) ∨ True)) ∨ False) ∧ p2)) ∨ (p4 → p2)) ∨ (p5 → p4))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_343126113962265084480530679346 : (p2 → (((p1 ∧ p4) ∧ p3) ∨ (((True → p4) ∨ ((p3 ∨ (p3 ∨ (p1 ∧ p4))) → (True → (((p2 → False) → p3) → p2)))) ∧ (p1 ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h5 =>
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- One of the premise coincides with the conclusion.
      exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_624365770552802379206575527883 : ((((p3 ∨ ((p3 ∨ (False ∧ p3)) → (p2 → (p1 ∧ ((p2 → ((p3 ∨ p4) ∧ (False ∨ (p4 ∨ ((p3 → False) ∧ True))))) → False))))) ∨ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39882002745554756085287827643 : (((p2 → (((p1 ∧ p4) ∧ (((p3 ∨ (p2 → (p5 ∨ (p5 ∧ p2)))) ∨ p1) → p3)) ∨ (False → ((p1 ∧ p5) ∧ (p1 → False))))) ∧ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_614843325543797199672940845343 : (((((p3 ∨ (((p4 ∧ (((p2 ∨ False) → (p1 ∨ p1)) → ((True ∨ False) → p4))) ∨ p4) ∧ False)) ∨ (p2 → (p4 → (p3 → p2)))) ∨ p5) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_727961057308063392726599073198 : ((((p3 ∨ (p1 ∧ False)) ∨ (((((p5 ∧ p3) → p4) → ((p4 → (p3 ∨ (p2 → ((p3 → p1) ∧ (p3 ∧ p3))))) → p4)) ∨ p5) → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48988340026675413488140061017 : (((((p1 ∧ True) ∨ ((p5 ∧ (False → (((((p1 ∨ p3) ∧ (True → False)) ∨ True) ∨ False) ∨ p1))) ∧ p4)) ∨ False) ∨ ((p3 ∨ p2) → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305406335654521066340141274172 : (p1 ∨ (((p3 ∨ ((((p4 ∧ p2) ∨ False) → p5) ∨ p3)) ∧ ((False ∧ (False ∧ p4)) → False)) ∨ (((p2 → p5) ∧ p5) ∨ (p3 ∨ (p4 ∨ True))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_320397501661297615880052366639 : (p4 ∨ ((p2 ∧ p2) → ((((p2 ∨ True) → ((False → p2) ∧ p2)) ∧ ((p4 → p3) → p5)) → (True ∧ ((p3 ∧ ((False → p3) ∧ False)) ∨ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h1.left
  let h6 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347411842017927234553725809805 : (p3 → ((((True ∧ p1) → p3) ∧ ((True ∨ p2) ∧ p4)) → ((False ∨ (p4 → False)) → (((p2 → (True → (False → (True → p4)))) → p4) ∧ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h2.left
    let h8 := h2.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h11 =>
      -- One of the premise coincides with the conclusion.
      exact h10
    case inr h12 =>
      -- One of the premise coincides with the conclusion.
      exact h10
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h13 =>
    -- False on the left can always be used.
    apply False.elim h13
  case inr h14 =>
    -- Conjunctions on the left can always be decomposed.
    let h15 := h2.left
    let h16 := h2.right
    -- Conjunctions on the left can always be decomposed.
    let h17 := h16.left
    let h18 := h16.right
    -- Disjunctions on the left can always be decomposed.
    cases h17
    case inl h19 =>
      -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
      have h20 : p4 := by
        -- One of the premise coincides with the conclusion.
        exact h18
      -- We have shown the premise of h14, we can now drive its conclusion.
      let h21 := h14 h20
      -- False on the left can always be used.
      apply False.elim h21
    case inr h22 =>
      -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
      have h23 : p4 := by
        -- One of the premise coincides with the conclusion.
        exact h18
      -- We have shown the premise of h14, we can now drive its conclusion.
      let h24 := h14 h23
      -- False on the left can always be used.
      apply False.elim h24



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118196477455851345181553164328 : ((False ∨ (True → (p5 ∨ ((((True ∧ ((True ∨ p2) ∨ p1)) → (p2 → p3)) ∧ (p2 → p4)) → ((p3 ∧ (p2 ∧ p4)) ∨ True))))) ∨ (p5 → p1)) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346347627107325619670861600446 : (p3 → (((p5 → ((p2 ∨ True) ∧ p3)) ∧ (False ∧ (((p1 ∨ ((p3 → p2) ∨ p2)) → (p1 ∧ p5)) ∨ ((False → p2) → p2)))) ∨ (p3 ∨ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114405544753655175606812396024 : ((((p2 ∧ (((p5 ∧ p5) ∨ False) → p3)) → (((p5 ∧ ((p1 → p1) → p2)) → False) ∨ True)) ∨ (True ∨ ((p3 ∨ True) ∨ p1))) ∨ (False → False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158527388149380163103793867742 : (((p5 ∨ p3) → (p2 ∨ (((True ∧ (p5 → ((p2 → False) ∨ (p2 ∨ True)))) ∧ (True ∨ p2)) ∨ p2))) ∨ (p3 → ((p5 ∨ p2) → (False ∧ p1)))) := by
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
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65337895820685471195436433551 : ((p3 ∨ (((p4 ∨ p2) ∨ (p2 ∧ (((p5 ∧ (p1 → p1)) ∧ p3) ∨ (((True ∧ True) → p2) ∧ p1)))) → (p1 → (False ∨ (p4 ∨ p2))))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- Conjunctions on the left can always be decomposed.
      let h12 := h10.left
      let h13 := h10.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h14 =>
      -- Conjunctions on the left can always be decomposed.
      let h15 := h14.left
      let h16 := h14.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_103196941253569445829596289765 : (((True ∧ ((p4 ∧ (p4 ∧ False)) ∧ ((((False ∧ ((p1 ∧ (p5 ∨ p3)) → p3)) → (p5 → p1)) ∨ p2) ∧ (p1 → p3)))) ∨ True) ∧ (False ∨ True)) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_261470531731508179501223204677 : ((p5 → p2) → ((True → p4) ∨ ((p3 ∧ p1) ∨ ((p2 ∧ ((False → p1) → p2)) ∨ ((((p2 → p2) ∧ True) ∧ ((p1 → p1) ∨ False)) ∨ p1))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62326503691550218751975094597 : ((p3 ∧ (((((p5 ∨ True) → p5) ∨ (True ∧ p3)) ∨ (((p5 ∨ (False → (p1 ∨ p3))) → p5) ∨ ((False → p2) ∧ p3))) → (p2 ∧ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_665823327782889916308181286438 : (((((((p5 ∨ p1) → (((p2 ∨ ((p2 → (p2 ∨ ((p3 ∧ p5) ∨ p2))) → p5)) ∧ p3) ∧ p4)) → p4) → p5) ∧ (p2 → (p2 ∨ True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191425426009691318441218603000 : (((p1 ∨ p3) → (p1 ∧ ((True ∧ (True ∧ False)) ∨ p4))) ∨ ((((True → (p2 ∨ p3)) ∨ (False → (p1 ∧ True))) → p3) → (p1 → (False ∨ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : ((True → (p2 ∨ p3)) ∨ (False → (p1 ∧ True))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- False on the left can always be used.
    apply False.elim h4
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184925624689985528606263806903 : (((p5 ∧ (p5 → False)) ∨ (p3 ∧ (p2 ∨ ((p4 ∧ True) ∨ p4)))) ∨ (p3 → ((p5 → (((False → p5) ∨ (p2 ∧ False)) ∨ (p3 ∨ False))) ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350277798506900161623353861504 : (p4 → ((p5 ∧ ((((True ∨ (p2 → (True ∧ ((p4 → (p3 ∧ p1)) ∨ (p2 ∧ p3))))) ∨ False) ∨ p2) → (p5 ∨ (p3 ∨ (True ∨ p3))))) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310686731236216972334156864076 : (p2 ∨ ((p1 ∨ ((p2 ∨ p5) ∨ p2)) → ((((p3 ∨ (p2 ∨ True)) ∨ (p1 ∧ p3)) ∨ (((p2 → p4) ∨ p5) ∧ (p3 ∨ (p1 → p3)))) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
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
  case inr h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h5 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h5
      case inr h6 =>
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
    case inr h7 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166758729253525707908807227833 : ((p4 → (p3 ∨ (p4 → ((False → (p2 ∧ (p2 → p3))) → (False ∧ (p3 ∨ (p5 ∧ p3))))))) ∨ (False ∨ (((False ∨ True) ∨ (p5 ∧ True)) ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180546591604870511829682294365 : (((p5 ∧ ((True ∨ (True ∨ p2)) ∧ (p2 → p2))) ∨ (p1 → (p5 ∨ p2))) → (((((p4 ∧ (p2 ∨ p2)) ∨ True) ∧ p3) ∨ p2) ∨ (p2 → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h11
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h12 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h12
  case inr h13 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h14
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174214791513777554003234219253 : (((((False ∨ (p5 ∨ (p5 ∨ (p2 ∧ False)))) → p4) → (p4 ∧ p1)) → (p4 → p4)) → (p4 ∨ (p5 → ((p2 → p2) → (p4 ∨ (p3 ∨ True)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_238150758684991796270876370831 : ((True ∨ p3) ∧ ((p5 → p2) ∨ (((p3 ∧ (((p1 ∨ p1) ∨ p1) ∨ (True ∧ False))) ∨ ((True → p5) ∨ False)) ∨ ((False ∨ (False ∨ True)) ∨ p2)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
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
theorem thm_5_vars_194265559085700527640814586751 : ((p5 → ((((p5 ∧ True) ∧ (p3 ∧ p4)) ∨ p3) → False)) → ((((((p4 ∨ p1) → (p5 ∨ p5)) ∨ (p2 ∧ False)) ∧ p4) ∨ False) ∨ (True ∨ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165702538381409054320387867320 : ((((False ∧ (p4 ∧ False)) ∧ True) ∧ (((p1 ∧ p5) ∨ False) → (p4 ∧ ((False ∨ p1) ∧ p3)))) ∨ ((((p5 ∧ (p5 ∧ p4)) → p1) → p3) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_610414506169352140916743852342 : (((((((((p1 → (p4 → ((p1 ∨ True) → (p5 ∨ False)))) → p3) ∧ p1) ∨ (True ∧ ((p2 ∨ (True → p1)) → p4))) → False) → p1) ∨ True) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_45447599359736711716408865168 : (((True ∨ ((p4 ∧ True) ∧ (p1 → ((p4 → (p5 → (p2 ∨ False))) ∨ (True → ((True → p2) ∧ ((p5 → False) ∨ (False ∨ p1)))))))) → p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354790468354058576741196352897 : (p5 → (((((p3 → p2) ∨ p3) → (p4 ∨ p2)) ∧ ((((p4 ∧ p4) → p3) ∧ (p5 → False)) ∧ ((p2 → (p2 ∧ p1)) ∨ (p3 → True)))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_154267159289548207155623739508 : (((((p1 → p2) → True) → ((p3 → p5) → (((p2 → p4) → p4) ∨ ((True ∨ p2) ∨ p2)))) ∨ p1) ∧ (True → (((p1 ∨ True) ∨ p2) ∨ p5))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157701328243860298120723583988 : ((((p1 → (False ∨ ((True → (p5 ∧ (p5 ∨ False))) ∨ (p5 ∨ p2)))) ∨ p5) → ((p1 ∧ p5) ∧ p2)) ∨ ((p3 ∨ (p5 ∨ (p3 → True))) ∨ p1)) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46031387073989934861721273020 : ((((p1 ∧ (p1 ∧ ((p4 → p1) ∧ (p4 → (p3 ∧ (p3 ∨ (((p4 ∨ (p4 ∧ p2)) ∧ True) ∧ (p4 ∧ False)))))))) ∧ p3) ∧ (p1 → p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166223346236712769366533101546 : ((p2 ∧ ((True → (((False ∨ ((True ∨ (False ∧ p3)) ∧ p3)) ∨ p5) ∧ False)) → (False ∧ False))) ∨ (False → (((p2 → False) → p3) → (p4 → True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112570710855904066047664173995 : ((((p3 ∨ ((True ∨ (p3 ∧ (p3 ∨ p1))) → (p3 → (p5 ∧ (p5 → (((p5 → True) ∨ (p2 → p5)) → p4)))))) → False) → p2) ∨ (True ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317583299881189032931804065964 : (p4 ∨ ((((True ∧ ((p2 ∨ (((True ∧ p2) ∨ ((p1 ∨ (p2 ∨ p1)) ∧ True)) ∨ ((True → (True → True)) ∨ True))) → p4)) → p1) ∧ True) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228447455690866994963646233164 : ((False ∨ (p1 ∨ p1)) ∨ (((p3 ∨ ((p4 → p1) ∧ (p1 → ((((p3 → p5) ∧ True) ∧ (False → p3)) → p5)))) → (p3 ∧ (True ∧ p2))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_662301546016964038769991364783 : (((((p1 ∨ (p3 → (p3 ∨ (((False ∧ True) → True) ∨ p1)))) → ((p5 ∧ p4) ∧ (((p1 ∧ (p1 → False)) ∧ p4) ∨ p4))) → (p3 ∨ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61545519206564964971991013542 : ((p1 ∧ ((False → (p3 ∧ (((p2 ∨ p5) → (p4 ∨ p3)) ∨ False))) ∧ ((((p2 → (True ∧ False)) → (p2 ∧ p2)) → (p1 ∧ False)) ∧ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319042276796445595601233870253 : (p4 ∨ (((p4 ∨ (p4 ∧ (True ∨ ((p3 → (p1 ∧ p2)) → ((p4 ∧ p4) → p3))))) → ((p4 → False) ∨ True)) ∨ ((p3 ∨ False) ∧ (p4 → p2)))) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
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
theorem thm_5_vars_181374869535214065329172117790 : ((p1 ∨ ((p1 → (p4 ∧ (False → ((p3 ∨ True) ∨ (p1 → p5))))) ∨ p1)) → ((True ∨ p5) ∧ ((True ∧ p2) → (p5 ∨ (p1 ∨ (p2 ∨ p1)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  -- Implications on the right can always be decomposed.
  intro h6
  -- Conjunctions on the left can always be decomposed.
  let h7 := h6.left
  let h8 := h6.right
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h9
  case inr h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116487763213381678063593378544 : (((p2 ∧ p2) ∧ ((True ∧ p3) ∧ ((p1 ∨ ((p2 → p5) ∨ p1)) ∧ ((p4 ∧ ((False ∧ True) → ((p2 → p3) ∨ p4))) → True)))) ∨ (p1 → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_141735551019749375453317233338 : (((True → True) ∧ ((((p3 ∨ (False ∨ (((False → True) ∧ p4) ∨ p2))) ∧ True) ∧ (p4 → p3)) ∧ (p2 ∧ (p5 → p1)))) → (p4 → (p3 ∧ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- Conjunctions on the left can always be decomposed.
  let h9 := h7.left
  let h10 := h7.right
  -- Disjunctions on the left can always be decomposed.
  cases h9
  case inl h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h6.left
    let h13 := h6.right
    -- One of the premise coincides with the conclusion.
    exact h11
  case inr h14 =>
    -- Disjunctions on the left can always be decomposed.
    cases h14
    case inl h15 =>
      -- False on the left can always be used.
      apply False.elim h15
    case inr h16 =>
      -- Disjunctions on the left can always be decomposed.
      cases h16
      case inl h17 =>
        -- Conjunctions on the left can always be decomposed.
        let h18 := h17.left
        let h19 := h17.right
        -- Conjunctions on the left can always be decomposed.
        let h20 := h6.left
        let h21 := h6.right
        -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
        have h22 : p4 := by
          -- One of the premise coincides with the conclusion.
          exact h19
        -- We have shown the premise of h8, we can now drive its conclusion.
        let h23 := h8 h22
        -- One of the premise coincides with the conclusion.
        exact h23
      case inr h24 =>
        -- Conjunctions on the left can always be decomposed.
        let h25 := h6.left
        let h26 := h6.right
        -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
        have h27 : p4 := by
          -- One of the premise coincides with the conclusion.
          exact h2
        -- We have shown the premise of h8, we can now drive its conclusion.
        let h28 := h8 h27
        -- One of the premise coincides with the conclusion.
        exact h28
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336171576666080522695294667533 : (p1 → ((((False ∧ False) → ((False ∨ (((True ∨ (((p3 ∨ True) → False) → ((p1 ∧ p5) → p4))) ∧ True) ∨ (p3 → p1))) → p5)) → p3) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_606261186210397680745721507604 : ((((((p5 ∧ (p2 → ((((True ∧ p4) ∨ False) → ((p4 → p1) → ((((p5 → p5) → p1) ∨ p2) → False))) ∧ False))) ∧ p4) ∧ False) ∨ True) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_306414266727199867469907011318 : (p1 ∨ ((p3 ∧ False) ∨ ((False ∨ ((p1 ∨ (p1 → (True → ((True ∧ (p5 ∨ False)) ∨ p3)))) → p4)) ∨ ((True ∧ (p1 → True)) → (False → False))))) := by
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
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_768514573737824731028943492355 : (((p5 ∧ (((((True ∨ p4) ∨ p1) ∧ ((p5 ∨ ((p5 ∨ (p4 → p5)) ∧ p3)) → p1)) ∨ True) → (((p2 ∨ p4) → (p2 → p3)) ∧ True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_352114651776775978315301183308 : (p4 → ((False ∧ ((p4 → p3) ∧ (p4 ∨ True))) ∨ ((p3 ∨ (((p5 ∨ (True → p3)) → ((((p2 ∨ True) ∨ p2) ∧ p5) → p2)) ∨ p5)) ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_619528322820335044084334044021 : (((((p4 → (p2 ∨ p3)) → (((p2 → (((p2 ∨ p2) → (p2 ∧ False)) ∧ True)) ∨ False) ∨ (p2 → (p2 ∨ (p3 → (p2 ∨ p1)))))) ∨ p1) ∨ p3) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57680853067821435431423987686 : ((((p3 → True) ∨ p2) → ((p3 ∨ p4) → ((((p2 ∧ (((p5 → True) → p4) ∧ p5)) ∧ True) ∨ ((p5 → (False → p2)) ∨ p4)) ∨ p3))) ∨ p2) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h7 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h8 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136421572412569951176189538496 : ((((p3 ∧ (True ∧ p5)) ∨ p2) → (p3 → (((((p1 ∧ (p3 ∧ p1)) ∨ False) ∨ True) → p2) ∧ ((p2 ∧ False) ∨ p5)))) ∨ (False → (False ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167323088532876519344043908147 : ((((p4 → ((p2 ∨ p4) → (((p3 ∨ False) → p3) ∧ (p4 ∧ p3)))) ∧ (p1 ∧ p4)) → p5) → (((True → (False ∧ (p3 ∨ p4))) ∧ p5) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_243026900694304971214163611132 : ((p4 → True) ∧ (p5 → (((True → ((((((True → ((False ∨ p2) ∧ p2)) ∨ p3) ∨ p5) ∧ p2) ∨ (p2 → (False → p5))) ∨ True)) ∨ p4) ∨ False))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150791926997101910392785922362 : ((((p3 → (((False → (p2 ∧ ((((p2 → p3) ∨ p5) ∧ p4) ∧ p3))) ∨ p4) → (p4 → False))) → p1) ∨ p3) → (p2 ∨ (p2 → (True → p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- Implications on the right can always be decomposed.
    intro h7
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_610951716697134926434868321145 : (((((((p2 → (p5 ∨ (p5 ∨ p3))) ∨ (p4 → (p1 ∨ True))) → (p4 → (p3 → (p3 ∨ (p5 → ((False ∧ p2) ∧ True)))))) → p2) ∨ True) ∨ False) ∧ True) := by
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
theorem thm_5_vars_40355769500781776452413954348 : ((((((p1 → (p1 ∧ (p1 ∨ (((p5 ∨ p3) ∨ False) ∧ (True → ((False → True) → (p2 ∧ (p5 ∨ p2)))))))) → True) → p3) ∨ True) ∨ False) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_698475631181871140067277679879 : (((((p4 → ((p1 ∨ (p5 ∨ p5)) ∧ p1)) ∨ ((p3 → p3) → p1)) ∨ ((False ∧ (p1 → (((p1 → p1) ∧ p4) ∨ (False ∧ p1)))) → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_962015868610516131952878890237 : ((((p4 ∨ p4) ∧ ((p5 ∧ ((p5 → ((p3 ∨ p1) ∨ (False → (p4 → p2)))) → False)) ∧ ((p4 ∨ p4) ∧ ((p2 ∨ (False → p5)) ∧ p5)))) → False) ∧ True) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h3.left
    let h6 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h6.left
    let h10 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h10.left
      let h13 := h10.right
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h14 =>
        -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
        have h15 : (p5 → ((p3 ∨ p1) ∨ (False → (p4 → p2)))) := by
          -- Implications on the right can always be decomposed.
          intro h16
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h17
          -- Implications on the right can always be decomposed.
          intro h18
          -- False on the left can always be used.
          apply False.elim h17
        -- We have shown the premise of h8, we can now drive its conclusion.
        let h19 := h8 h15
        -- False on the left can always be used.
        apply False.elim h19
      case inr h20 =>
        -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
        have h21 : (p5 → ((p3 ∨ p1) ∨ (False → (p4 → p2)))) := by
          -- Implications on the right can always be decomposed.
          intro h22
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h23
          -- Implications on the right can always be decomposed.
          intro h24
          -- False on the left can always be used.
          apply False.elim h23
        -- We have shown the premise of h8, we can now drive its conclusion.
        let h25 := h8 h21
        -- False on the left can always be used.
        apply False.elim h25
    case inr h26 =>
      -- Conjunctions on the left can always be decomposed.
      let h27 := h10.left
      let h28 := h10.right
      -- Disjunctions on the left can always be decomposed.
      cases h27
      case inl h29 =>
        -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
        have h30 : (p5 → ((p3 ∨ p1) ∨ (False → (p4 → p2)))) := by
          -- Implications on the right can always be decomposed.
          intro h31
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h32
          -- Implications on the right can always be decomposed.
          intro h33
          -- False on the left can always be used.
          apply False.elim h32
        -- We have shown the premise of h8, we can now drive its conclusion.
        let h34 := h8 h30
        -- False on the left can always be used.
        apply False.elim h34
      case inr h35 =>
        -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
        have h36 : (p5 → ((p3 ∨ p1) ∨ (False → (p4 → p2)))) := by
          -- Implications on the right can always be decomposed.
          intro h37
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h38
          -- Implications on the right can always be decomposed.
          intro h39
          -- False on the left can always be used.
          apply False.elim h38
        -- We have shown the premise of h8, we can now drive its conclusion.
        let h40 := h8 h36
        -- False on the left can always be used.
        apply False.elim h40
  case inr h41 =>
    -- Conjunctions on the left can always be decomposed.
    let h42 := h3.left
    let h43 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h44 := h42.left
    let h45 := h42.right
    -- Conjunctions on the left can always be decomposed.
    let h46 := h43.left
    let h47 := h43.right
    -- Disjunctions on the left can always be decomposed.
    cases h46
    case inl h48 =>
      -- Conjunctions on the left can always be decomposed.
      let h49 := h47.left
      let h50 := h47.right
      -- Disjunctions on the left can always be decomposed.
      cases h49
      case inl h51 =>
        -- We want to use the implication h45 based on <expert-advice>. So we show its premise.
        have h52 : (p5 → ((p3 ∨ p1) ∨ (False → (p4 → p2)))) := by
          -- Implications on the right can always be decomposed.
          intro h53
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h54
          -- Implications on the right can always be decomposed.
          intro h55
          -- False on the left can always be used.
          apply False.elim h54
        -- We have shown the premise of h45, we can now drive its conclusion.
        let h56 := h45 h52
        -- False on the left can always be used.
        apply False.elim h56
      case inr h57 =>
        -- We want to use the implication h45 based on <expert-advice>. So we show its premise.
        have h58 : (p5 → ((p3 ∨ p1) ∨ (False → (p4 → p2)))) := by
          -- Implications on the right can always be decomposed.
          intro h59
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h60
          -- Implications on the right can always be decomposed.
          intro h61
          -- False on the left can always be used.
          apply False.elim h60
        -- We have shown the premise of h45, we can now drive its conclusion.
        let h62 := h45 h58
        -- False on the left can always be used.
        apply False.elim h62
    case inr h63 =>
      -- Conjunctions on the left can always be decomposed.
      let h64 := h47.left
      let h65 := h47.right
      -- Disjunctions on the left can always be decomposed.
      cases h64
      case inl h66 =>
        -- We want to use the implication h45 based on <expert-advice>. So we show its premise.
        have h67 : (p5 → ((p3 ∨ p1) ∨ (False → (p4 → p2)))) := by
          -- Implications on the right can always be decomposed.
          intro h68
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h69
          -- Implications on the right can always be decomposed.
          intro h70
          -- False on the left can always be used.
          apply False.elim h69
        -- We have shown the premise of h45, we can now drive its conclusion.
        let h71 := h45 h67
        -- False on the left can always be used.
        apply False.elim h71
      case inr h72 =>
        -- We want to use the implication h45 based on <expert-advice>. So we show its premise.
        have h73 : (p5 → ((p3 ∨ p1) ∨ (False → (p4 → p2)))) := by
          -- Implications on the right can always be decomposed.
          intro h74
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h75
          -- Implications on the right can always be decomposed.
          intro h76
          -- False on the left can always be used.
          apply False.elim h75
        -- We have shown the premise of h45, we can now drive its conclusion.
        let h77 := h45 h73
        -- False on the left can always be used.
        apply False.elim h77
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41517176239159046679695494577 : (((((((p2 ∨ (p1 → p1)) ∨ p4) → p5) ∨ (p5 ∧ p4)) ∧ (((True → ((p5 ∧ True) ∨ (p5 ∧ (True ∨ p2)))) ∨ p3) → p4)) ∨ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193285297509604782286952423315 : ((((True ∨ False) ∨ p5) ∨ ((p2 ∧ p1) ∨ (p3 ∧ p2))) → ((p5 ∨ p4) ∨ (p3 ∨ ((p4 → p3) → ((True → p2) → (p1 ∨ (False → p3))))))) := by
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
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h5
        -- Implications on the right can always be decomposed.
        intro h6
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h7
        -- False on the left can always be used.
        apply False.elim h7
      case inr h8 =>
        -- False on the left can always be used.
        apply False.elim h8
    case inr h9 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h9
  case inr h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h14
      -- Implications on the right can always be decomposed.
      intro h15
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h13
    case inr h16 =>
      -- Conjunctions on the left can always be decomposed.
      let h17 := h16.left
      let h18 := h16.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_183790619709322647062044598642 : ((((((False ∧ ((p1 ∨ True) → p1)) ∨ p1) ∧ p4) ∨ True) ∧ p5) ∨ (False ∨ (True ∨ (False ∧ ((p4 → (p1 ∧ ((True → p2) ∧ p2))) → p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_619753941540086482596742995629 : (((((False ∨ p1) ∧ (((p4 → ((p2 ∧ False) ∧ p1)) ∨ (False ∨ ((p3 ∨ False) ∧ True))) ∨ (p3 ∨ (False ∧ ((p5 ∨ p1) ∧ p3))))) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_978485851651971794995623360636 : (((True ∧ (p4 ∨ ((((p1 → p1) → p4) ∧ ((p4 → ((p1 → (p5 ∧ p5)) ∨ ((p5 ∨ p4) ∨ p2))) ∧ (p3 ∨ p1))) ∧ (False ∨ p3)))) → p4) ∧ True) := by
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
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h6.left
    let h9 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h13 =>
        -- False on the left can always be used.
        apply False.elim h13
      case inr h14 =>
        -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
        have h15 : (p1 → p1) := by
          -- Implications on the right can always be decomposed.
          intro h16
          -- One of the premise coincides with the conclusion.
          exact h16
        -- We have shown the premise of h8, we can now drive its conclusion.
        let h17 := h8 h15
        -- One of the premise coincides with the conclusion.
        exact h17
    case inr h18 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h19 =>
        -- False on the left can always be used.
        apply False.elim h19
      case inr h20 =>
        -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
        have h21 : (p1 → p1) := by
          -- Implications on the right can always be decomposed.
          intro h22
          -- One of the premise coincides with the conclusion.
          exact h22
        -- We have shown the premise of h8, we can now drive its conclusion.
        let h23 := h8 h21
        -- One of the premise coincides with the conclusion.
        exact h23
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117658547050285523270676200009 : ((p3 ∧ (((True ∨ (((((p3 ∨ p5) ∨ (p2 ∨ (p4 ∧ (True → p4)))) ∧ p5) → p4) → p5)) → p5) ∧ (p3 → (p4 ∨ p5)))) ∨ (p1 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62512706060841569797357947581 : ((p3 ∧ (p3 ∧ (((p4 ∧ p3) ∧ ((p5 → ((p5 ∧ p4) → p2)) ∧ p3)) ∧ (((p2 → p1) → (False ∧ (True ∨ p1))) ∧ (p4 ∨ p3))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197893396612477837961199978522 : ((((True → p5) → True) → ((p3 ∨ p4) ∧ p3)) ∨ (((True → p3) ∨ (p3 ∨ p3)) → (p2 ∨ (p1 → (False → (((False → False) ∧ p4) ∨ p4)))))) := by
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
    -- Implications on the right can always be decomposed.
    intro h4
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h7
      -- Implications on the right can always be decomposed.
      intro h8
      -- False on the left can always be used.
      apply False.elim h8
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- Implications on the right can always be decomposed.
      intro h11
      -- False on the left can always be used.
      apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300374125005432420100214158669 : (False ∨ ((((p2 → (((p5 ∧ ((p4 ∧ (p5 → (p4 ∨ (p3 ∧ p1)))) → True)) ∨ p4) → p1)) ∧ p4) → (p3 ∧ True)) ∨ ((p1 ∨ True) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_3989450866866098374229243242 : (p1 ∨ ((((False ∧ p5) ∧ (p3 → True)) ∨ p3) ∨ (p4 ∨ ((p3 ∨ p2) → (False → ((False ∨ p2) ∨ ((p4 ∧ p4) ∨ (True ∨ p4)))))))) := by
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
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115438562902505963012961982914 : (((((False ∨ (p2 → p2)) → False) ∧ (p3 ∨ p1)) ∨ ((((p3 ∧ p2) ∨ (p2 ∧ True)) → p4) ∨ (p5 ∨ ((True ∨ p4) → p5)))) ∨ (True → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_253598140842845806004044985541 : ((p1 ∧ True) → ((((p4 → p1) → False) → ((False ∧ ((p2 → (p1 ∨ True)) → ((((p3 ∧ p3) ∨ p5) ∨ p2) ∧ (p2 ∧ p1)))) ∨ False)) ∧ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h5 : (p4 → p1) := by
    -- Implications on the right can always be decomposed.
    intro h6
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h7 := h2 h5
  -- False on the left can always be used.
  apply False.elim h7
  -- Conjunctions on the left can always be decomposed.
  let h8 := h1.left
  let h9 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_737255834259684804018431087037 : ((((p4 → False) ∧ ((((((p1 ∧ p3) → p5) → (p2 ∧ p5)) ∨ (p3 ∧ p2)) ∧ ((False → True) ∧ True)) ∨ ((False ∨ p1) ∧ (p3 ∧ p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_306657577399785498024971112172 : (p1 ∨ (True ∧ (((((p2 → ((p2 → False) ∧ p2)) ∨ p2) ∨ p1) ∧ False) ∨ (False → ((False ∧ p2) ∧ (True ∧ (((p3 → True) → p4) ∨ p3))))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204704861612976453754263112087 : (((p4 ∨ (True → (p3 ∨ p5))) ∨ p3) ∨ (((p1 ∧ ((True → (False ∧ False)) ∧ ((p4 → (p3 ∧ p1)) ∧ (p3 ∧ p4)))) ∨ True) ∨ (True ∧ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351768526745191299150036162101 : (p4 → ((True ∧ (p1 ∨ (p2 ∨ (p1 ∨ ((p2 → ((p4 → p5) → True)) ∧ p1))))) → ((p1 ∧ (True → (p1 → p2))) ∨ (p3 → (p3 ∨ p1))))) := by
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
    -- Implications on the right can always be decomposed.
    intro h6
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h9
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h9
    case inr h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h12
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
        -- Implications on the right can always be decomposed.
        intro h16
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118252340600014575165559133432 : ((p1 ∨ ((((p1 ∧ False) → (p3 ∧ ((((p1 ∨ p1) → p2) ∨ ((False ∨ p1) ∨ p1)) ∧ False))) ∨ p1) → (p4 → (p1 ∨ False)))) ∨ (True ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_320280961967240378198203076559 : (p4 ∨ ((p2 ∧ p4) ∨ (((((False ∨ (((p1 ∨ p2) ∧ (p2 → p4)) ∧ p4)) → p2) ∧ p2) ∨ (True ∨ False)) ∧ ((p3 ∧ p3) ∨ (True ∨ p3))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_252024533630922581115873244964 : ((p4 → p1) ∨ ((((p5 ∧ (p4 ∨ p2)) ∨ p5) → (((True ∧ p2) → (False → (p4 ∧ (p1 ∨ p2)))) → ((p1 ∧ (True ∧ p1)) ∨ p5))) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_395720196931714488830933439685 : ((((p2 ∧ (p2 → (p1 ∧ ((False ∧ p5) ∧ ((p4 → p5) → (False ∧ ((True → (((p5 ∨ p2) ∨ (p3 ∧ p2)) → False)) → p3))))))) ∨ True) ∧ True) ∧ True) := by
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
theorem thm_5_vars_134682400582592022374712660159 : (((((p5 → p3) → (p5 ∧ (False ∧ p4))) ∧ ((p3 → ((True ∧ p3) ∧ p1)) ∧ ((p1 → p1) ∨ (p3 ∧ p5)))) → p2) ∨ (p2 → (True ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244224036673579500319137010439 : ((True ∧ p5) ∨ ((p2 ∧ p3) → (((p3 ∧ (p5 ∨ p5)) ∨ ((p1 ∨ (((p4 ∨ (p2 ∨ (False → False))) → False) ∨ True)) ∨ False)) ∨ (True ∧ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
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
theorem thm_5_vars_184410748740169665923073586728 : ((((p3 ∧ (p2 ∨ ((p4 → p5) ∨ False))) ∨ p1) ∧ (p1 ∧ True)) ∨ (p3 ∨ (p3 → ((p5 → p1) ∨ (((p4 ∨ (True → True)) ∨ p2) ∨ p5))))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_783320403701852421723888456145 : (((p3 ∨ ((((p3 ∨ p1) ∨ (p3 ∨ ((p4 ∨ ((p4 ∨ p1) ∧ p5)) → True))) ∨ ((p3 ∧ p3) ∧ p4)) → (True ∧ ((p4 → False) → p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2936081274863677647468942100 : (((p3 ∧ p1) ∨ p4) ∨ (((p1 ∧ p3) → (p4 ∨ (p5 → ((p4 ∧ ((((False → True) ∧ p1) ∧ (p5 ∧ p1)) ∨ p3)) ∨ p1)))) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_685178296699022630969102339618 : ((((p4 ∨ (p3 ∧ (p1 ∧ ((p4 ∧ p3) ∧ (((p4 ∨ False) ∨ (p3 ∧ p5)) ∨ (True → False)))))) ∨ ((p3 ∧ (True ∨ p1)) → (p3 → p3))) ∨ p2) ∧ True) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h6 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_126335539317887244713748051410 : ((p1 ∧ ((((p4 ∨ False) → p5) ∨ ((p5 → (p3 ∧ (p2 → False))) ∧ ((((p5 → p1) ∧ p5) ∨ p4) ∧ (p5 ∨ p4)))) → True)) → (p3 → p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_950233153373668775366430205258 : (((((True → p4) → p1) ∧ ((((p1 → (True → p3)) → (p2 ∨ p5)) → p5) ∧ (False ∨ (((True → ((p4 ∧ p4) ∧ True)) ∧ p3) ∧ p4)))) → p1) ∧ True) := by
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
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h8.left
    let h11 := h8.right
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h12 : (True → p4) := by
      -- Implications on the right can always be decomposed.
      intro h13
      -- One of the premise coincides with the conclusion.
      exact h9
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h14 := h2 h12
    -- One of the premise coincides with the conclusion.
    exact h14
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300667896183260550338630709697 : (False ∨ (((p3 ∧ ((p5 ∧ p3) ∨ (((False ∨ ((p3 → p2) ∧ p1)) ∨ (p3 ∧ p4)) ∨ p1))) ∨ p2) ∨ (True ∨ (((True ∧ p2) ∧ p5) → True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198185741026032203745340093852 : (((True → p2) → ((p5 ∨ (p4 → p3)) → False)) ∨ ((False ∨ p3) → (True → (((p3 → ((True ∨ (True ∨ p3)) ∨ p5)) ∧ True) ∧ (False → True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h4 =>
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204937746824486722909080776417 : ((((True ∨ p1) → (False → False)) → p1) ∨ (((p4 → ((False ∨ ((p4 ∨ p5) ∧ p1)) ∧ (p5 ∨ (p3 → p1)))) ∨ (p4 → (p5 → p4))) ∨ p5)) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256501819011044602695580847071 : ((False ∨ p4) → (p3 ∨ (((((((((p5 → p4) → p1) ∧ (p4 ∨ p3)) → (False ∨ (True ∧ p1))) → True) ∧ True) → False) ∧ False) ∨ (p4 ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- False on the left can always be used.
    apply False.elim h2
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3



