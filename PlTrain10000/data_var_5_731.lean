variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_677941746201782369527476028633 : ((((((p1 ∧ (p5 ∨ ((p5 ∧ (((p4 ∧ False) ∧ (p3 ∨ p3)) → p5)) ∧ p4))) → p3) → (p5 ∧ True)) ∨ (True ∧ (p3 → (p3 ∨ p3)))) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233418583445187365793243336243 : ((False ∨ (p3 ∨ p1)) → (((p2 ∨ p1) ∨ (False ∨ (p3 → (p3 ∨ (p3 ∧ p4))))) ∧ ((p2 ∨ (p2 ∨ True)) ∨ (p1 ∨ ((p2 ∧ p5) ∧ p1))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h5
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h6 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h6
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h7 =>
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116862717443513383078990844826 : (((p1 → p2) ∨ (p3 ∧ (p5 ∨ ((False → (((True ∧ (False ∧ p4)) ∧ p1) → (True ∧ p5))) ∧ ((p2 → (p3 ∨ p4)) ∧ p5))))) ∨ (True ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_669502615778864860444157673443 : (((((((p5 ∨ True) ∨ (((True ∨ p1) ∧ True) → (p5 ∧ p5))) ∧ (((p3 ∧ p2) → p1) → p3)) → (p3 → p1)) ∨ ((True ∧ False) → False)) ∨ p4) ∧ True) := by
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
  -- False on the left can always be used.
  apply False.elim h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111580894613479475523508125574 : ((((p1 ∧ (p5 → ((p2 → (p4 ∨ (((False ∧ p4) ∧ (((p3 → p4) → (p2 ∨ False)) ∧ p2)) ∨ p2))) ∨ p3))) ∧ False) ∨ True) ∨ (p2 ∨ p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56752579518795558246658447918 : ((((p2 → p1) ∨ p4) ∧ (((p4 → False) ∨ (p2 ∨ p3)) → (p5 ∧ (p5 ∨ (((True ∧ p4) → ((p5 → True) ∨ True)) → (p4 ∧ p3)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_8532782654919274382040855424 : ((((((p5 ∨ p1) ∨ p5) ∧ (((p5 ∧ (True ∨ p2)) → (True ∧ ((p2 ∨ (p3 ∨ p3)) ∨ (p5 ∨ False)))) → p4)) ∧ (p5 ∨ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166893151547973076645098319749 : (((((False → True) → (p4 ∨ ((p3 → (p2 ∧ p1)) ∧ p1))) → (p1 ∧ (False ∧ False))) ∧ p1) → (p2 → ((p1 ∨ ((p4 → p3) → p4)) → p3))) := by
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
    let h5 := h1.left
    let h6 := h1.right
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h7 : ((False → True) → (p4 ∨ ((p3 → (p2 ∧ p1)) ∧ p1))) := by
      -- Implications on the right can always be decomposed.
      intro h8
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h9
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h2
      -- One of the premise coincides with the conclusion.
      exact h6
      -- One of the premise coincides with the conclusion.
      exact h6
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h10 := h5 h7
    -- We need to get the right conjuct of h10 based on <expert-advice>.
    let h11 := h10.right
    -- We need to get the left conjuct of h11 based on <expert-advice>.
    let h12 := h11.left
    -- False on the left can always be used.
    apply False.elim h12
  case inr h13 =>
    -- Conjunctions on the left can always be decomposed.
    let h14 := h1.left
    let h15 := h1.right
    -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
    have h16 : ((False → True) → (p4 ∨ ((p3 → (p2 ∧ p1)) ∧ p1))) := by
      -- Implications on the right can always be decomposed.
      intro h17
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h18
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h2
      -- One of the premise coincides with the conclusion.
      exact h15
      -- One of the premise coincides with the conclusion.
      exact h15
    -- We have shown the premise of h14, we can now drive its conclusion.
    let h19 := h14 h16
    -- We need to get the right conjuct of h19 based on <expert-advice>.
    let h20 := h19.right
    -- We need to get the left conjuct of h20 based on <expert-advice>.
    let h21 := h20.left
    -- False on the left can always be used.
    apply False.elim h21



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112233539503123706608792070175 : (((p2 ∨ (((((p1 ∨ p1) → (p4 ∧ p1)) ∨ True) → p4) → ((p4 → (((p1 ∧ p5) → p1) → p2)) → (True ∧ p1)))) ∨ True) ∨ (False → p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55405726797886059046462444423 : ((((((p1 ∨ p1) → False) ∨ p5) ∨ True) → (((p1 ∨ p1) ∨ ((p1 → ((False ∧ ((p3 → p4) → (p4 ∨ p1))) → p2)) ∨ p5)) ∨ p3)) ∨ p2) := by
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h4
      -- Implications on the right can always be decomposed.
      intro h5
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- False on the left can always be used.
      apply False.elim h6
    case inr h8 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h8
  case inr h9 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h10
    -- Implications on the right can always be decomposed.
    intro h11
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- False on the left can always be used.
    apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53399030113198802867801917426 : ((((((p4 ∨ (p4 → False)) → (p5 → p4)) ∧ p4) ∨ (p2 ∨ True)) → (((False ∧ ((p1 → p1) → p2)) ∧ (p3 → (p4 ∨ p2))) ∧ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118486898399774402305521231399 : ((p3 ∨ ((((p1 ∧ True) ∨ ((p2 ∨ (((p3 ∨ p5) ∧ False) ∨ False)) → (p4 → (p5 → p1)))) → p1) ∨ (False → (True → False)))) ∨ (p1 ∧ True)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_310492070865737947853194166249 : (p2 ∨ ((((True ∧ (p3 → p3)) ∨ p1) → p1) ∨ ((True → (((False ∨ p3) ∧ p4) → ((True ∧ True) → p3))) → (p1 → (p3 ∨ (p1 ∧ p1)))))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_727017931837993200949556514985 : (((((p2 → p3) → p2) ∨ ((False ∨ (((p3 ∨ p3) ∧ p2) ∧ ((p1 ∨ p4) ∧ (p2 ∨ ((((False ∨ True) ∨ True) ∧ p3) ∨ False))))) ∨ True)) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_111514040039456124877296150461 : (((p5 → (((((True → p3) ∧ False) → (p2 ∧ p2)) ∧ ((True → ((p5 ∨ p3) ∧ (False ∨ p4))) ∧ (p4 → p2))) → p2)) ∧ p1) ∨ (True ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208569923559107626343332491675 : (((p5 ∨ p4) → (p2 ∧ (p5 ∨ True))) → (((p3 → p1) ∧ (p1 ∧ p4)) → (((((p1 ∧ p1) ∧ True) ∧ ((p3 ∧ False) → True)) → p5) ∨ p2))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h7 : (p5 ∨ p4) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h6
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h8 := h1 h7
  -- We need to get the left conjuct of h8 based on <expert-advice>.
  let h9 := h8.left
  -- One of the premise coincides with the conclusion.
  exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117513319964932994690158739518 : ((p2 ∧ ((((p1 ∧ p4) ∨ (((p3 ∨ (p2 → p3)) ∧ (p3 ∨ True)) ∨ (False ∧ p4))) ∨ (((True ∨ p2) ∧ p2) ∨ p5)) ∨ p3)) ∨ (False → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354869203918715199699898025057 : (p5 → ((True ∧ (p5 ∧ (((p2 ∧ (p2 → (((False ∧ False) → p1) ∨ (((p1 ∨ (p4 ∧ (p3 → p5))) → p3) ∨ p1)))) → p4) ∧ p1))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258321955410464143332880375117 : ((p5 ∨ True) → (p1 ∨ (((((p3 → (p2 ∨ (((True ∨ False) ∨ (True ∨ p5)) ∧ p5))) ∧ False) ∨ ((True → p1) ∧ p4)) ∨ (True ∨ True)) ∨ p4))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40976777196689416833196432145 : (((((False ∧ p3) ∨ (((p3 ∨ ((p5 → (((p2 ∧ p4) → p5) ∨ False)) → True)) → (True ∧ p4)) ∨ (p1 ∧ False))) ∨ (True ∨ p3)) ∨ True) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_669263230005822339291863719778 : (((((True → (((True ∨ p2) ∧ (p4 → ((p4 → p1) ∨ p3))) ∧ (p5 ∧ ((p1 ∧ False) ∧ (p2 ∨ p5))))) → p2) ∨ (p2 → (p5 → p2))) ∨ p4) ∧ True) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51319981052496976473703024176 : (((p5 ∨ (p3 ∧ ((p2 → (((((p4 ∧ False) ∨ False) → True) ∨ p1) → (p3 ∧ p1))) ∨ p1))) ∨ ((p4 ∧ p2) ∨ ((False ∨ p4) → p4))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- False on the left can always be used.
    apply False.elim h2
  case inr h3 =>
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_635132446181715083505249596474 : ((((((False → (p3 ∨ (p5 ∨ p5))) ∧ ((((p4 ∧ p5) ∨ (p4 ∨ p4)) ∨ p5) ∨ (True → (True → p5)))) → ((True → p4) ∨ p2)) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_621437546738328242881822323278 : ((((False ∧ ((((((p4 → (p2 ∧ ((p2 ∨ p1) → (((True ∨ (p4 ∨ True)) → p3) ∨ p1)))) → p1) → p5) ∨ p3) ∨ False) ∧ p3)) ∨ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178461368322301334016059795006 : (((p2 ∨ ((p2 ∨ p3) ∧ (p1 ∨ (True ∧ False)))) ∧ (False → (p5 ∧ p3))) ∨ ((((p4 ∨ p1) → ((True ∧ p3) ∧ (p2 ∧ p4))) ∧ p1) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40784338257802421788651720534 : ((((p2 ∧ (((p3 ∨ False) → p5) ∧ (p1 ∨ ((p2 → False) ∨ ((((p4 → p4) → p3) ∧ p2) → (False → (p3 → p5))))))) → p1) ∨ True) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_683730835338719934883288550057 : (((((p5 → (False ∨ ((p2 ∨ ((p4 ∧ p5) ∨ p1)) → (((p1 ∧ p5) → p1) ∧ p4)))) ∧ p5) ∨ ((p5 → (p4 ∨ (p1 ∧ p3))) → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50960356984912692090944049432 : (((((p5 ∧ (p4 → (p5 ∧ p4))) ∨ False) → ((False ∧ (p1 ∨ p1)) ∧ (False ∧ (p5 ∨ p4)))) ∧ ((p4 ∨ p4) → ((p2 ∧ p2) ∧ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_226301498869868778672160307385 : (((p4 ∨ p4) ∨ p3) ∨ ((p1 → False) → ((p3 ∨ p1) → (p5 ∨ ((True ∨ ((False ∧ p1) ∨ ((p4 ∨ p5) ∨ p1))) ∨ ((p1 ∧ True) ∧ p5)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_616307826699467812815720650269 : ((((((p2 ∨ ((p2 ∨ p4) → p2)) ∧ ((p2 ∨ (False ∧ p2)) ∨ p1)) ∨ (False ∨ (p4 → (False → (True ∧ ((p1 ∨ p1) → p3)))))) ∨ False) ∨ p1) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_194253939948513019904619310412 : ((p4 → (p5 ∨ ((False → p3) → ((p2 ∨ p2) → p2)))) → (((((True ∧ False) → (p5 → (p1 → (p4 ∧ p3)))) ∧ p3) ∧ (p3 ∧ p5)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171547892867549591814200226117 : ((((((True ∨ p2) → (((p4 ∧ (False → p5)) → True) ∨ p5)) ∨ True) → p4) ∨ False) ∨ (False → (False → ((p2 ∧ p5) ∨ (False → (True → p5)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47524764292470083203087346047 : (((p3 ∨ (p3 ∧ ((True ∨ p4) ∧ (p2 ∨ ((p2 ∨ (p4 ∧ p3)) ∧ (((p4 ∨ ((p3 ∧ p4) → False)) → False) → p4)))))) ∨ (False ∨ True)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172797915042757968678577896793 : (((p3 → p4) → ((p2 → p3) → (p5 ∨ ((((p3 → p3) ∧ p5) → p5) ∧ False)))) ∨ ((True → ((p3 ∧ (p4 ∨ p3)) → p3)) ∨ (p3 ∨ p3))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h6 =>
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207692776684351785454432365146 : ((((True → p5) → (p5 ∨ p1)) → False) → (((p3 ∨ p4) ∨ p3) → ((p5 ∧ ((p2 ∨ (p2 ∧ (p1 ∨ True))) ∧ p5)) ∧ (False → (True → p4))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h5 : ((True → p5) → (p5 ∨ p1)) := by
        -- Implications on the right can always be decomposed.
        intro h6
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
        have h7 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h6, we can now drive its conclusion.
        let h8 := h6 h7
        -- One of the premise coincides with the conclusion.
        exact h8
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h9 := h1 h5
      -- False on the left can always be used.
      apply False.elim h9
    case inr h10 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h11 : ((True → p5) → (p5 ∨ p1)) := by
        -- Implications on the right can always be decomposed.
        intro h12
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
        have h13 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h12, we can now drive its conclusion.
        let h14 := h12 h13
        -- One of the premise coincides with the conclusion.
        exact h14
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h15 := h1 h11
      -- False on the left can always be used.
      apply False.elim h15
  case inr h16 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h17 : ((True → p5) → (p5 ∨ p1)) := by
      -- Implications on the right can always be decomposed.
      intro h18
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- We want to use the implication h18 based on <expert-advice>. So we show its premise.
      have h19 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h18, we can now drive its conclusion.
      let h20 := h18 h19
      -- One of the premise coincides with the conclusion.
      exact h20
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h21 := h1 h17
    -- False on the left can always be used.
    apply False.elim h21
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h22 =>
    -- Disjunctions on the left can always be decomposed.
    cases h22
    case inl h23 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h24 : ((True → p5) → (p5 ∨ p1)) := by
        -- Implications on the right can always be decomposed.
        intro h25
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- We want to use the implication h25 based on <expert-advice>. So we show its premise.
        have h26 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h25, we can now drive its conclusion.
        let h27 := h25 h26
        -- One of the premise coincides with the conclusion.
        exact h27
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h28 := h1 h24
      -- False on the left can always be used.
      apply False.elim h28
    case inr h29 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h30 : ((True → p5) → (p5 ∨ p1)) := by
        -- Implications on the right can always be decomposed.
        intro h31
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- We want to use the implication h31 based on <expert-advice>. So we show its premise.
        have h32 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h31, we can now drive its conclusion.
        let h33 := h31 h32
        -- One of the premise coincides with the conclusion.
        exact h33
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h34 := h1 h30
      -- False on the left can always be used.
      apply False.elim h34
  case inr h35 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h36 : ((True → p5) → (p5 ∨ p1)) := by
      -- Implications on the right can always be decomposed.
      intro h37
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- We want to use the implication h37 based on <expert-advice>. So we show its premise.
      have h38 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h37, we can now drive its conclusion.
      let h39 := h37 h38
      -- One of the premise coincides with the conclusion.
      exact h39
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h40 := h1 h36
    -- False on the left can always be used.
    apply False.elim h40
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h41 =>
    -- Disjunctions on the left can always be decomposed.
    cases h41
    case inl h42 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h43 : ((True → p5) → (p5 ∨ p1)) := by
        -- Implications on the right can always be decomposed.
        intro h44
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- We want to use the implication h44 based on <expert-advice>. So we show its premise.
        have h45 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h44, we can now drive its conclusion.
        let h46 := h44 h45
        -- One of the premise coincides with the conclusion.
        exact h46
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h47 := h1 h43
      -- False on the left can always be used.
      apply False.elim h47
    case inr h48 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h49 : ((True → p5) → (p5 ∨ p1)) := by
        -- Implications on the right can always be decomposed.
        intro h50
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- We want to use the implication h50 based on <expert-advice>. So we show its premise.
        have h51 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h50, we can now drive its conclusion.
        let h52 := h50 h51
        -- One of the premise coincides with the conclusion.
        exact h52
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h53 := h1 h49
      -- False on the left can always be used.
      apply False.elim h53
  case inr h54 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h55 : ((True → p5) → (p5 ∨ p1)) := by
      -- Implications on the right can always be decomposed.
      intro h56
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- We want to use the implication h56 based on <expert-advice>. So we show its premise.
      have h57 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h56, we can now drive its conclusion.
      let h58 := h56 h57
      -- One of the premise coincides with the conclusion.
      exact h58
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h59 := h1 h55
    -- False on the left can always be used.
    apply False.elim h59
  -- Implications on the right can always be decomposed.
  intro h60
  -- Implications on the right can always be decomposed.
  intro h61
  -- False on the left can always be used.
  apply False.elim h60



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_748551099893165655249640948541 : ((((p3 → False) → (((p1 ∨ (((False ∨ ((p1 ∨ p5) ∧ False)) ∧ True) ∧ ((p2 → False) → p3))) ∨ (p3 ∧ p1)) ∨ ((True ∧ p1) ∨ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_69348978164565432855437615397 : ((p5 → (p2 ∨ ((p1 ∨ (p5 ∧ True)) → (p3 → ((((p4 ∧ (p3 ∨ (p5 → ((True ∧ p4) → p3)))) ∧ p2) → p1) ∨ (p1 ∨ p5)))))) ∨ p4) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_695588932680743385273694764143 : (((((p5 ∨ ((p4 ∨ (False → p4)) ∨ (False ∨ p2))) → (True ∨ (p3 ∨ p2))) → ((p1 ∨ (False ∧ ((p1 → p4) → p5))) → (p1 → p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167914525131329486688255053228 : (((p5 ∨ (p4 ∧ (((True ∨ True) ∧ p1) ∨ p2))) ∧ (True ∨ (False ∧ ((p5 ∧ p1) ∨ p5)))) → (p5 ∨ ((((p2 ∨ p1) ∧ p5) ∨ False) ∨ True))) := by
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- False on the left can always be used.
      apply False.elim h7
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h12.left
      let h14 := h12.right
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h15 =>
        -- Disjunctions on the left can always be decomposed.
        cases h3
        case inl h16 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h17 =>
          -- Conjunctions on the left can always be decomposed.
          let h18 := h17.left
          let h19 := h17.right
          -- False on the left can always be used.
          apply False.elim h18
      case inr h20 =>
        -- Disjunctions on the left can always be decomposed.
        cases h3
        case inl h21 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h22 =>
          -- Conjunctions on the left can always be decomposed.
          let h23 := h22.left
          let h24 := h22.right
          -- False on the left can always be used.
          apply False.elim h23
    case inr h25 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h26 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h27 =>
        -- Conjunctions on the left can always be decomposed.
        let h28 := h27.left
        let h29 := h27.right
        -- False on the left can always be used.
        apply False.elim h28



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354958602844889228011548421342 : (p5 → ((p1 → ((p3 ∧ True) → (p4 ∧ (p2 ∨ (((((((False ∨ p4) → p5) → p4) ∧ (True ∧ False)) ∨ p2) ∧ True) ∧ (p1 ∨ p2)))))) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_791269499395299229366471121824 : (((True → (((((p2 ∨ p3) ∧ ((p4 ∨ ((p2 ∧ (p5 → True)) ∧ (True ∧ (True ∨ p5)))) → False)) ∨ ((p1 ∧ p5) ∨ p3)) ∧ p5) ∨ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_85977761861945611632203370975 : (((((((False ∧ p3) ∧ True) ∨ True) ∨ False) → (p4 ∧ False)) ∧ ((p2 → ((True → (p2 → (True → True))) ∧ (False ∧ (False → p4)))) ∧ p4)) → False) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h6 : ((((False ∧ p3) ∧ True) ∨ True) ∨ False) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h7 := h2 h6
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_912560971206682039986640697843 : ((((((((((p2 → False) ∨ (p4 → (p3 ∧ p5))) → p1) ∨ True) → p5) → True) → (p1 ∨ True)) → (p3 ∧ (p3 ∧ (False ∨ (p1 ∨ p1))))) → p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((((((p2 → False) ∨ (p4 → (p3 ∧ p5))) → p1) ∨ True) → p5) → True) → (p1 ∨ True)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h7 =>
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- One of the premise coincides with the conclusion.
      exact h9
    case inr h10 =>
      -- One of the premise coincides with the conclusion.
      exact h10
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_608521864065977718956275188726 : (((((((True → False) ∧ ((p4 ∧ (p1 ∨ (p2 → False))) → (p1 → (((False ∧ (True ∨ (p1 → p2))) → False) ∧ True)))) → p2) ∨ True) ∨ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_302783706091626084056599113225 : (False ∨ (p4 ∨ (p1 ∨ ((True ∧ (((p1 → (p2 → False)) ∨ p5) → (p4 ∨ (((p4 → (((p2 ∧ True) → p1) ∧ p3)) ∧ False) → False)))) ∨ True)))) := by
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
theorem thm_5_vars_41724329051877262473739778337 : ((((((p5 ∧ False) ∨ p4) → False) ∧ ((((((False ∨ p4) ∧ p5) ∧ p4) ∧ p1) → (p1 ∨ ((p3 ∧ False) → p2))) → (p4 ∧ True))) ∨ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_700792018002204919890553740069 : ((((((p1 ∧ p1) ∨ (p2 ∧ ((p3 ∧ p3) ∧ False))) ∧ p1) ∧ ((p3 → (((p1 ∧ True) ∨ p2) ∧ (p3 ∧ p1))) ∧ ((p5 → p1) ∨ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149781666056097265848624791531 : ((False ∨ (((p1 → (((p1 ∧ True) ∧ (p5 ∨ (p4 ∧ p4))) ∨ True)) ∨ ((p2 ∧ p2) ∨ p5)) → (p3 ∨ p4))) ∨ ((True → False) ∨ (p5 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_252281899109888278358061292269 : ((p4 → p5) ∨ ((p5 → (True → (((((p5 → (p2 ∧ p1)) ∧ True) → p4) → (p3 ∧ (p4 ∨ p3))) ∧ (p1 ∨ p5)))) ∨ ((p3 ∨ True) ∨ p2))) := by
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
theorem thm_5_vars_322606398231867541436667042668 : (p5 ∨ ((p3 → (((p4 → ((p1 ∨ p1) ∨ p4)) → ((p3 ∧ (p4 ∧ ((True ∧ p4) ∧ p3))) → (False ∧ (True ∨ p2)))) ∨ (p5 → p3))) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_195243024335948245549773797210 : (((p2 ∨ ((False ∧ p2) → p3)) ∨ (p3 → p4)) ∧ (((False → True) → ((p4 → p4) → p1)) ∨ (p2 → (((p5 → False) ∨ (p4 ∧ p1)) ∨ True)))) := by
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
  -- False on the left can always be used.
  apply False.elim h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61238049505580803576405115116 : ((False ∧ (p3 ∧ (((p4 ∧ p5) ∧ p2) ∨ ((p2 ∨ ((p5 ∨ p4) → (((p4 → ((False → p4) → p1)) → p4) → p2))) ∧ (p5 → p3))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53980642661003940460785614425 : (((((p3 ∨ (p2 ∨ (p3 ∨ (p2 ∧ p3)))) ∨ p2) ∨ p1) → (p2 ∨ (p3 → ((p4 ∧ p1) → (((p5 ∧ p3) ∨ (p3 → True)) ∨ p2))))) ∨ p2) := by
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
        -- Implications on the right can always be decomposed.
        intro h5
        -- Implications on the right can always be decomposed.
        intro h6
        -- Conjunctions on the left can always be decomposed.
        let h7 := h6.left
        let h8 := h6.right
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h9
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h10 =>
        -- Disjunctions on the left can always be decomposed.
        cases h10
        case inl h11 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h11
        case inr h12 =>
          -- Disjunctions on the left can always be decomposed.
          cases h12
          case inl h13 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h14
            -- Implications on the right can always be decomposed.
            intro h15
            -- Conjunctions on the left can always be decomposed.
            let h16 := h15.left
            let h17 := h15.right
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h18
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h19 =>
            -- Conjunctions on the left can always be decomposed.
            let h20 := h19.left
            let h21 := h19.right
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h20
    case inr h22 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h22
  case inr h23 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h24
    -- Implications on the right can always be decomposed.
    intro h25
    -- Conjunctions on the left can always be decomposed.
    let h26 := h25.left
    let h27 := h25.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h28
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159036484119622046379904565331 : ((p4 ∨ (True → (p4 ∨ (((((p5 ∧ p3) ∧ ((p1 → (p3 ∨ p2)) → False)) ∧ p2) → p4) → p2)))) ∨ ((p4 ∧ (p3 ∨ (False ∧ p2))) → p3)) := by
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
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- False on the left can always be used.
    apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_107480321085239957549038801349 : (((True ∨ (True → p5)) → ((p1 → p2) → ((p4 → ((p2 ∧ p3) ∨ p4)) ∧ ((((p2 → p4) → True) → p3) ∨ (p4 ∨ True))))) ∧ (False → p3)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    exact h3
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- Implications on the right can always be decomposed.
  intro h8
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136834589699114191425882509433 : (((p1 ∧ p2) ∨ (((p4 → False) ∨ ((True ∧ p4) ∨ (((((False ∧ p5) ∧ (p3 → p4)) → p4) ∧ p1) ∧ p4))) → p3)) ∨ ((False → p4) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_654197892300560201989484718713 : ((((((p4 ∨ ((p1 ∧ (p5 ∧ ((p5 → p3) ∨ p2))) ∨ (((p4 → (p5 ∧ p3)) → (p2 ∨ True)) ∨ p5))) ∨ p4) ∨ p2) ∨ (p1 → p3)) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38820605068916641814827857160 : ((((True ∧ ((p3 ∨ p2) → p2)) → ((True ∨ (((p3 → p3) ∧ (True → p4)) ∧ True)) → (p4 → (p2 ∧ ((p1 ∨ p3) ∧ p3))))) ∧ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200177995913145313047199862881 : (((True ∧ (p3 ∨ p3)) ∨ ((p2 ∨ p3) ∧ p1)) → (((p1 → ((p5 ∧ ((p4 ∧ (p2 ∨ p3)) ∧ (p2 ∨ p4))) ∨ (p2 → p3))) ∨ p5) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h6
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h7
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h8 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h9
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- One of the premise coincides with the conclusion.
      exact h8
  case inr h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h14 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h14
    case inr h15 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h16
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h17
      -- One of the premise coincides with the conclusion.
      exact h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_748965258573185605993596606303 : ((((p4 → p3) → (p5 ∨ ((p1 → ((False → p2) ∨ False)) → ((True → ((p4 → ((p3 ∨ (p3 ∧ (True ∨ False))) ∧ True)) ∧ p4)) ∧ p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218074094864809245545375554947 : (((p5 ∨ False) ∧ (p1 → True)) → ((False → (p5 → p5)) → ((((True → (True ∧ p1)) ∧ (p1 → ((p4 ∧ p3) ∨ False))) → (p2 ∨ p1)) ∨ p4))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h6
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h9 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h10 := h7 h9
    -- We need to get the right conjuct of h10 based on <expert-advice>.
    let h11 := h10.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h11
  case inr h12 =>
    -- False on the left can always be used.
    apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340882203579749365360772086010 : (p2 → (((True → (((p1 ∧ ((False ∨ ((True → False) → (p5 ∨ True))) ∧ p5)) → False) → p4)) → ((((p1 ∨ p4) → p1) → False) ∨ p2)) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149030343820632723786381825385 : (((True ∧ (p5 ∧ False)) ∨ ((((True ∧ ((((p5 ∨ p2) ∨ p3) ∧ (True ∧ p3)) ∧ p1)) ∨ p2) ∧ p3) ∨ p2)) ∨ (False ∨ ((False → p2) ∨ p2))) := by
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
theorem thm_5_vars_56682379762320147160612349377 : ((((p4 → p1) ∧ True) ∧ ((True → (p3 ∧ (((p4 ∨ ((p3 ∧ (True → ((False → p4) ∨ False))) ∧ (p1 ∨ p2))) ∨ p2) → True))) → p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187577466298751950256224542692 : ((p3 ∨ ((p4 ∨ ((p5 → p3) → p4)) ∨ (p3 ∨ (p5 ∧ p3)))) → ((((p4 → p1) → False) → ((p3 ∨ (p1 → p2)) → (p3 ∨ p4))) ∨ True)) := by
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
        -- Conjunctions on the left can always be decomposed.
        let h10 := h9.left
        let h11 := h9.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158925708181673800959599349286 : ((p1 ∨ (p2 → ((p5 ∨ (((p2 ∧ True) ∨ p1) → p1)) ∨ (((True → p4) ∧ p3) ∧ (p2 ∧ p4))))) ∨ ((p1 ∨ (True ∨ (p4 ∧ False))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41712821851155927656454840136 : ((((False → (False ∧ (False → (p5 ∨ p2)))) → (p5 → ((False → ((p2 → p2) ∧ ((p1 → False) ∧ (p2 ∧ p1)))) → (False ∨ False)))) ∨ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_634967592331989927299060047325 : (((((((p4 ∨ (p2 ∧ ((p4 ∧ (p4 ∧ (p5 ∧ True))) ∧ ((p2 → (p5 ∧ p5)) → p3)))) ∨ p4) ∧ p1) → ((p3 → p1) ∨ p2)) → p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43251967431797049476335085889 : ((((False → (((p2 ∨ ((p5 ∨ False) ∧ ((p3 → (p3 ∧ p4)) ∧ ((True ∨ (True ∧ p3)) ∧ True)))) ∧ p1) ∧ (p1 → p2))) ∧ p2) → p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37350098941575676967431730016 : ((((((((p4 → (((p5 ∨ ((p3 ∨ p1) ∧ (p2 ∧ (p5 ∨ (False ∧ p5))))) ∨ p3) → p5)) ∨ p2) → p3) ∨ p5) ∨ p1) ∨ p2) ∧ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_23106698077393632048001277700 : (((((p2 → False) → p1) ∧ (True ∧ p4)) → ((p5 ∧ ((((p3 ∧ (p4 → p4)) ∧ p1) ∨ False) ∨ (p1 ∧ (True → p1)))) ∨ (p5 → True))) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h6
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192506973340281031184011649582 : ((((p2 → False) ∧ (True → ((True ∨ p2) ∧ False))) ∨ False) → (((False ∧ False) ∧ p3) ∨ (((False → ((True ∨ False) ∧ (True → p1))) ∧ True) → p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h5 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h6 := h4 h5
    -- We need to get the right conjuct of h6 based on <expert-advice>.
    let h7 := h6.right
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- False on the left can always be used.
    apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178782544129264410345707342242 : (((True → (p1 ∨ p1)) ∧ ((p3 ∧ (False → ((p3 → p2) ∨ p5))) ∨ False)) ∨ ((p4 ∧ (((True → False) ∧ (p4 ∨ False)) ∧ (p2 → p4))) → p1)) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h9 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h10 := h6 h9
    -- False on the left can always be used.
    apply False.elim h10
  case inr h11 =>
    -- False on the left can always be used.
    apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_637898674500441747273042843534 : ((((((p3 → p1) ∨ (((p5 ∨ p5) → True) → p1)) ∧ (((p1 ∨ False) → (((p4 → p3) ∧ (p4 ∨ p4)) → p5)) → (True ∧ p4))) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310018398211109210354402001180 : (p2 ∨ ((((((p5 ∨ (p5 → p1)) ∧ (False ∨ (p3 ∨ (False ∨ True)))) → p4) ∨ p2) ∨ True) ∨ (False ∨ (True ∧ ((p4 → p5) → (p4 ∧ p2)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_590378344380439229269778268712 : ((((((p5 → (p2 → p2)) → (((False → p1) → False) → (((False ∨ (p1 → (p4 ∧ p5))) → ((p3 → p1) → p2)) → p4))) → p1) ∧ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_153115785636242555040653338080 : ((p4 ∧ (((((True ∨ (p1 → p1)) ∨ p3) ∧ (False → p2)) ∧ (p3 ∧ (p3 → True))) → ((p1 → p5) ∧ False))) → ((False ∨ (p2 ∨ p4)) ∧ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111695743088781069986949906256 : ((((((p3 → (p1 ∧ p1)) ∨ (p3 ∨ ((p1 → p4) → ((False ∧ (p3 ∧ (p2 ∧ p2))) ∧ (True ∨ True))))) → p4) → p1) ∨ False) ∨ (p4 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62609861462535548173771169096 : ((p4 ∧ ((((True → (((p2 ∧ p4) ∨ (True ∧ (p1 ∧ (((((p4 ∧ False) → p4) → True) ∧ True) ∧ p1)))) ∨ p1)) ∨ p3) ∨ p2) ∧ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66485669035906427948503493596 : ((True → (((((p3 ∨ ((True ∨ p5) ∧ ((p5 ∨ (False → p4)) → p5))) ∧ ((p3 ∧ p5) → p4)) ∨ p5) ∨ ((p5 ∨ p3) → p3)) ∨ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180822889237875065262534372005 : (((p5 ∧ (True → False)) ∧ ((p1 ∨ p5) ∨ ((False ∨ p4) → (p5 → False)))) → (((p1 ∧ p1) ∧ (p4 ∧ (((p4 ∧ p2) ∨ p5) ∧ p5))) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h8 =>
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h9 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h10 := h5 h9
      -- False on the left can always be used.
      apply False.elim h10
  case inr h11 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h12 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h13 := h5 h12
    -- False on the left can always be used.
    apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_773287680386161161518866894409 : (((False ∨ (((((p4 → p1) ∨ p5) ∧ p4) ∨ ((False → (True ∨ (((p4 ∧ (p5 → ((p4 ∨ False) ∨ True))) ∨ p1) ∧ p3))) ∧ p4)) ∧ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346306080802859191204073259963 : (p3 → ((((p2 ∨ (((p1 ∨ (p5 ∨ True)) → (((False ∨ True) ∨ p3) → (True ∧ True))) ∨ p3)) ∧ ((p1 → False) ∨ p4)) → p5) ∨ (p5 → p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323902602225702633035158195382 : (p5 ∨ (((p3 ∧ (True → p4)) ∧ ((((p4 → p3) ∧ (p5 ∨ (True → p2))) ∧ p2) ∧ p1)) ∨ ((p5 ∧ (p3 ∧ (True → False))) → (p5 → p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h7 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h8 := h6 h7
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_124919371938893956232136858810 : (((((p5 → p3) ∨ False) → p5) → (p2 ∧ ((True ∧ ((((p3 ∨ (False ∨ (True → p4))) → p2) ∧ (p4 → True)) ∧ p2)) ∨ p5))) → (p3 ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167587269640757753820020942451 : ((((False ∨ p4) ∨ (((((False → p3) ∨ (True ∨ p4)) ∧ p4) ∧ False) → p4)) ∨ (False ∨ True)) → ((p2 ∨ p3) ∨ (p5 ∨ (p3 → (p3 ∨ True))))) := by
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
        -- False on the left can always be used.
        apply False.elim h4
      case inr h5 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h6
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- False on the left can always be used.
      apply False.elim h10
    case inr h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h12
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51438126377527735837171496127 : (((((p4 → (((p1 ∨ ((False → p1) ∨ (p5 → False))) → p2) ∧ False)) ∨ p1) → (p2 ∨ True)) → ((p1 ∧ (True → (p4 ∧ p2))) ∨ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59202799034805926456113719712 : (((p1 ∨ p2) ∨ (p3 ∨ (((((p4 ∧ (((True → (p3 ∧ False)) ∨ p3) ∧ p4)) ∧ (p1 ∨ p3)) ∨ (True → (p4 ∨ True))) ∨ p1) ∨ False))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40946268715562005731807002367 : (((((p3 ∨ (((p2 ∧ p1) → ((p4 ∨ p5) → (((True ∧ False) ∧ (p3 → p3)) ∧ p1))) ∧ (p2 → p3))) → False) ∨ (p3 ∨ False)) ∨ True) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147884216414331214671752398073 : ((((((p2 ∧ (p5 → (True ∨ p4))) ∧ ((p1 ∧ ((p3 ∧ p3) ∧ p1)) → p2)) → p3) ∧ p4) ∧ (p2 → True)) ∨ (p4 → ((p4 ∧ p1) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47685325681016449983902099566 : ((((p2 ∧ ((((p2 → p4) ∧ (p5 → (p3 ∧ (p1 → p2)))) ∧ p4) ∨ (((p3 ∧ (p5 ∨ p5)) ∧ p4) ∧ p3))) ∧ p2) → (p1 ∧ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114148340674432648788936511872 : (((((p2 ∨ (((p5 → (True ∨ p1)) ∨ p5) ∧ (p3 → ((p2 ∧ False) ∨ p5)))) ∨ (True ∨ True)) ∨ False) → (True ∧ (p1 → p2))) ∨ (True ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178239727628394448304347224253 : ((((((p1 ∨ (p1 ∨ (False ∨ p5))) ∧ True) ∨ p2) ∧ p2) ∧ (p3 ∧ True)) ∨ (p3 → ((False → ((p2 → True) ∧ (False → (True ∨ p3)))) → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_216119220092488157332771284088 : ((True → (p5 ∧ (p2 ∧ p1))) ∨ ((p5 → (p4 ∧ p3)) ∨ ((p3 → ((p1 ∨ ((False ∨ ((False ∨ True) → p5)) → p2)) ∨ p2)) → (p1 → p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_689912389886471750418274808443 : (((((p4 ∨ p4) → ((p3 → False) → ((p1 ∧ p5) ∨ ((p3 → (True → False)) ∧ True)))) ∨ (((p5 ∧ p3) ∨ (p5 ∧ True)) ∨ (p1 ∧ p1))) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h6 : p3 := by
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h7 := h2 h6
    -- False on the left can always be used.
    apply False.elim h7
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h9
    -- Implications on the right can always be decomposed.
    intro h10
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h11 : p3 := by
      -- One of the premise coincides with the conclusion.
      exact h9
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h12 := h2 h11
    -- False on the left can always be used.
    apply False.elim h12
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215700798786077808056727930303 : ((False ∨ ((p4 → False) ∨ p2)) ∨ (p5 ∨ ((p3 → p5) ∨ (True → ((p2 → p2) ∧ (p1 ∨ ((p4 ∨ p1) ∨ (p5 ∨ ((p4 → p4) ∨ p1))))))))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_221836450643299849822038404915 : (((p3 ∧ p1) → p3) ∧ (((p3 → p4) ∨ ((p1 ∨ p4) ∨ ((((p3 ∧ p2) → (p2 ∨ ((p3 → p5) ∨ p4))) ∧ True) ∨ True))) → (p2 ∨ True))) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- Conjunctions on the left can always be decomposed.
        let h12 := h11.left
        let h13 := h11.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h14 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40537777195498230040133511836 : ((((p3 ∨ (((((p5 ∧ p2) ∧ (p3 → p2)) ∨ (p1 → p4)) ∧ p3) ∨ (False → ((((p4 → False) ∨ False) ∧ p1) → p4)))) ∨ True) ∨ False) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187834384156121421360703143012 : ((p5 → (((p3 ∨ (False ∨ (False → (p3 ∧ p4)))) → p3) ∧ p5)) → ((((False ∧ p3) ∧ p5) ∧ ((False ∨ p3) ∨ (False ∧ (p5 ∧ p4)))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117531350721034298733382430622 : ((p2 ∧ (((((p1 ∧ (False ∧ ((p2 → True) → (p5 → (p2 ∨ False))))) ∨ p3) → ((p2 → p4) ∧ p4)) → False) ∧ (p2 ∧ p2))) ∨ (True ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



