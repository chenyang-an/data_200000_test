variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200702856253516744159483189119 : ((p2 ∧ ((p1 ∨ p1) ∨ ((p3 ∧ p3) ∨ p3))) → (((((True → False) ∨ ((True ∧ (p5 ∧ (p1 ∧ p5))) ∨ p5)) ∧ (False ∧ p4)) ∧ p1) ∨ p2)) := by
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
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_210791409976570193854386169013 : (((p2 ∧ (p1 ∨ p5)) → True) ∧ (p5 → (p2 ∨ ((p3 ∨ ((p2 → p3) ∧ (False ∨ ((p1 → ((p4 ∧ True) ∧ (p3 ∨ p2))) ∧ p1)))) ∨ True)))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345409632275996838543550822801 : (p3 → (((((((False ∧ p3) → p5) ∨ (True ∨ False)) ∧ (p4 ∧ p5)) ∧ ((p1 ∨ p2) ∨ (False ∧ (False → ((p1 → p2) ∧ p4))))) → p1) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113067767756232104457057678878 : (((p3 ∨ ((((p4 → p4) ∧ ((p1 ∧ False) ∨ ((p5 ∧ p4) ∨ (False ∧ ((False → p5) ∧ (False → p5)))))) → p3) → p2)) → p1) ∨ (p1 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208377772972960640959486394592 : (((p2 ∧ p5) ∨ (True ∨ (True ∧ p2))) → (((p5 → (p5 → p4)) ∧ p3) ∨ (p4 → ((True ∨ False) ∧ (p5 ∨ ((p1 ∨ (True ∨ p4)) ∨ p4)))))) := by
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
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
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
    case inr h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h12
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
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
theorem thm_5_vars_63017548836970682130694260484 : ((p4 ∧ (p3 → ((p3 ∧ p1) ∨ ((p2 ∨ (False ∨ ((False → (p3 ∨ (((True ∨ p5) ∧ p3) → p1))) ∧ p1))) ∧ (p2 → (p1 ∧ False)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167276926739727219837961705147 : ((((((((p3 ∨ (((p1 ∧ p5) ∨ p3) ∧ p1)) ∨ True) ∨ True) → False) → False) ∨ True) → False) → (p4 → ((False → (p4 ∧ (p5 ∧ p3))) ∧ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h3
  -- False on the left can always be used.
  apply False.elim h3
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h4 : ((((((p3 ∨ (((p1 ∧ p5) ∨ p3) ∧ p1)) ∨ True) ∨ True) → False) → False) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h4
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67852448628702510112490592303 : ((p2 → (((p5 ∨ ((p4 ∨ (p4 ∨ (p3 ∨ (p2 ∧ p2)))) → True)) → (p5 ∧ ((p2 → p3) ∧ (p3 ∨ (False → p4))))) → (p5 ∧ p3))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (p5 ∨ ((p4 ∨ (p4 ∨ (p3 ∨ (p2 ∧ p2)))) → True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
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
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h7 : (p5 ∨ ((p4 ∨ (p4 ∨ (p3 ∨ (p2 ∧ p2)))) → True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h9 := h2 h7
  -- We need to get the right conjuct of h9 based on <expert-advice>.
  let h10 := h9.right
  -- We need to get the left conjuct of h10 based on <expert-advice>.
  let h11 := h10.left
  -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
  have h12 : p2 := by
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h11, we can now drive its conclusion.
  let h13 := h11 h12
  -- One of the premise coincides with the conclusion.
  exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_781874458707290662270696540415 : (((p2 ∨ (p1 → ((True ∧ ((False → True) → (p2 → ((False ∧ p1) ∧ (p5 ∧ (p4 ∨ ((p5 → False) ∨ p2))))))) ∧ ((False ∧ p5) ∨ p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138027940658082887866501866630 : ((True → ((((((p4 ∨ True) → (p1 ∨ p5)) ∨ p5) ∧ (p1 ∨ p1)) → (((True ∧ p4) → p1) → p4)) ∨ (p5 ∧ p2))) ∨ ((p1 ∧ True) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136025397042550417865945931103 : ((((p4 ∨ ((p5 ∧ p4) ∧ (False ∨ False))) → (p1 ∨ p1)) → ((((False ∧ p2) ∨ True) ∧ (p1 → False)) ∨ (p3 ∧ p3))) ∨ ((True → True) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_761536502075318319450274338738 : (((p3 ∧ ((((((p5 ∨ p3) ∨ (True ∧ (((True ∧ p4) ∨ (p1 ∧ (p5 → (p1 → p3)))) ∧ p3))) → p3) → (True → p4)) ∨ p4) ∨ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_602756023314092853649938065796 : ((((False ∨ (p5 ∧ (((p5 ∨ True) → True) → (((p4 ∧ ((p2 ∧ True) → p5)) ∨ ((p5 → p1) ∧ (True ∨ p4))) ∧ (p5 ∨ p3))))) ∧ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148464373169495076964949172272 : ((((p2 ∨ p5) ∧ ((((p1 ∨ p1) ∨ p4) ∨ (False ∨ p2)) ∧ p4)) ∧ (p3 → (p4 ∨ (p1 → (p4 ∧ p3))))) ∨ ((True ∧ p1) → (p5 → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_201851507489132428268550730941 : ((((p1 → p4) ∨ (False → p2)) ∨ p2) ∧ (((((False → ((p2 → p5) ∨ ((p3 ∨ p2) ∨ (True ∧ p5)))) ∨ False) ∨ True) → (p1 → False)) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_69177141741197292883199197911 : ((p5 → (((((False ∧ p1) ∧ (True → (p4 → p4))) ∨ (p5 ∧ False)) ∧ (p1 → p1)) ∧ (p3 ∧ ((p3 ∧ (p1 ∧ p4)) ∧ (True → p2))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148368945210666734663304846710 : (((((((p4 ∨ False) ∨ (p4 → (p4 ∨ False))) → (p2 ∨ p5)) ∨ True) ∨ p4) ∨ (((p1 → p4) → p5) ∨ p3)) ∨ ((p1 ∨ p1) ∧ (True ∨ p2))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111146982126574453209680308133 : (((((False ∨ ((p3 ∨ p5) ∨ p3)) ∧ p1) ∨ ((p4 ∧ True) ∨ ((((p1 ∨ p2) ∨ True) → False) ∨ ((p3 → True) ∨ p4)))) ∧ True) ∨ (p2 → p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_176974190772130248003931077260 : (((False ∨ p5) → (p2 ∨ (p5 → ((True → ((p2 → p5) ∧ p4)) → p5)))) ∧ ((True → p4) → (((p2 ∧ p5) ∧ p2) ∨ ((p4 → p3) → p4)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h4
  -- Implications on the right can always be decomposed.
  intro h6
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h7
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h8 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h9 := h6 h8
  -- One of the premise coincides with the conclusion.
  exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192726119914263043171684873375 : ((((p2 → (p3 ∧ p2)) → ((p2 ∧ p3) ∨ True)) → False) → ((((False ∨ (((((p3 ∧ p1) → p5) → True) ∧ p3) → p2)) → False) → p2) ∧ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : ((p2 → (p3 ∧ p2)) → ((p2 ∧ p3) ∨ True)) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h3
  -- False on the left can always be used.
  apply False.elim h5
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h6 : ((p2 → (p3 ∧ p2)) → ((p2 ∧ p3) ∨ True)) := by
    -- Implications on the right can always be decomposed.
    intro h7
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h8 := h1 h6
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187381659650659204902011347073 : ((p3 ∧ (p2 → (((False → (p1 → p3)) ∨ p5) ∧ (False ∧ p3)))) → ((((((p4 → (p1 → False)) ∨ (p1 → p5)) ∨ p1) ∧ p5) ∧ p3) ∨ True)) := by
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
theorem thm_5_vars_62714111718472320475217379741 : ((p4 ∧ ((p1 ∧ (p5 ∨ (((p5 → True) → ((p4 ∨ (p2 ∧ (p2 ∧ (p4 ∨ ((p2 → True) → True))))) ∨ (False ∨ p3))) → p1))) → p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116055903785819839130354803437 : (((p5 → (p5 ∧ (p2 ∨ p4))) → (p2 ∨ (((p1 ∧ p1) ∧ ((p5 ∧ (p2 → ((p3 → (p1 ∨ p3)) → p3))) → False)) ∧ p1))) ∨ (p3 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181592223920786703305087936038 : ((p1 → ((True ∧ p5) ∨ ((p5 → p2) → ((False ∧ p2) ∧ (False ∨ p5))))) → ((False ∨ (p4 ∧ (((p3 ∨ p5) ∨ (p4 ∧ p5)) ∨ p3))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_125293833802101805354391954629 : ((((p3 ∧ p3) → p2) → (((True ∧ (p1 ∨ ((((False ∧ False) ∨ (p3 → p3)) ∧ (p3 → (p1 → p4))) ∧ True))) ∨ True) ∧ p2)) → (p4 ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_349144692736320758798496246577 : (p3 → (True → (p5 → (((p4 ∨ p4) ∧ ((True ∨ (p2 ∨ (p2 → p1))) ∧ (p5 ∨ (p5 → (p5 ∧ p5))))) → ((True → p3) ∧ (p2 ∨ p4)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
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
    -- Conjunctions on the left can always be decomposed.
    let h9 := h7.left
    let h10 := h7.right
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h12 =>
        -- One of the premise coincides with the conclusion.
        exact h1
      case inr h13 =>
        -- One of the premise coincides with the conclusion.
        exact h1
    case inr h14 =>
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h15 =>
        -- Disjunctions on the left can always be decomposed.
        cases h10
        case inl h16 =>
          -- One of the premise coincides with the conclusion.
          exact h1
        case inr h17 =>
          -- One of the premise coincides with the conclusion.
          exact h1
      case inr h18 =>
        -- Disjunctions on the left can always be decomposed.
        cases h10
        case inl h19 =>
          -- One of the premise coincides with the conclusion.
          exact h1
        case inr h20 =>
          -- One of the premise coincides with the conclusion.
          exact h1
  case inr h21 =>
    -- Conjunctions on the left can always be decomposed.
    let h22 := h7.left
    let h23 := h7.right
    -- Disjunctions on the left can always be decomposed.
    cases h22
    case inl h24 =>
      -- Disjunctions on the left can always be decomposed.
      cases h23
      case inl h25 =>
        -- One of the premise coincides with the conclusion.
        exact h1
      case inr h26 =>
        -- One of the premise coincides with the conclusion.
        exact h1
    case inr h27 =>
      -- Disjunctions on the left can always be decomposed.
      cases h27
      case inl h28 =>
        -- Disjunctions on the left can always be decomposed.
        cases h23
        case inl h29 =>
          -- One of the premise coincides with the conclusion.
          exact h1
        case inr h30 =>
          -- One of the premise coincides with the conclusion.
          exact h1
      case inr h31 =>
        -- Disjunctions on the left can always be decomposed.
        cases h23
        case inl h32 =>
          -- One of the premise coincides with the conclusion.
          exact h1
        case inr h33 =>
          -- One of the premise coincides with the conclusion.
          exact h1
  -- Conjunctions on the left can always be decomposed.
  let h34 := h4.left
  let h35 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h34
  case inl h36 =>
    -- Conjunctions on the left can always be decomposed.
    let h37 := h35.left
    let h38 := h35.right
    -- Disjunctions on the left can always be decomposed.
    cases h37
    case inl h39 =>
      -- Disjunctions on the left can always be decomposed.
      cases h38
      case inl h40 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h36
      case inr h41 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h36
    case inr h42 =>
      -- Disjunctions on the left can always be decomposed.
      cases h42
      case inl h43 =>
        -- Disjunctions on the left can always be decomposed.
        cases h38
        case inl h44 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h43
        case inr h45 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h43
      case inr h46 =>
        -- Disjunctions on the left can always be decomposed.
        cases h38
        case inl h47 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h36
        case inr h48 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h36
  case inr h49 =>
    -- Conjunctions on the left can always be decomposed.
    let h50 := h35.left
    let h51 := h35.right
    -- Disjunctions on the left can always be decomposed.
    cases h50
    case inl h52 =>
      -- Disjunctions on the left can always be decomposed.
      cases h51
      case inl h53 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h49
      case inr h54 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h49
    case inr h55 =>
      -- Disjunctions on the left can always be decomposed.
      cases h55
      case inl h56 =>
        -- Disjunctions on the left can always be decomposed.
        cases h51
        case inl h57 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h56
        case inr h58 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h56
      case inr h59 =>
        -- Disjunctions on the left can always be decomposed.
        cases h51
        case inl h60 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h49
        case inr h61 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h49



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_123229736589581923933677351285 : (((((p4 → ((p1 → (p2 ∧ (p4 → p3))) ∧ p5)) ∨ p5) ∧ ((p4 ∧ (p4 → p2)) ∨ p3)) ∧ ((p1 ∨ p2) → (p4 ∧ p4))) → (p3 ∨ True)) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
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
    cases h5
    case inl h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h12.left
      let h14 := h12.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h15 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_203923189707024557087655360162 : ((p2 → (((p3 ∧ False) → p1) ∨ True)) ∧ ((((p3 ∨ p1) → ((p4 ∨ p5) ∨ p2)) ∨ True) ∨ ((p1 → p1) ∨ ((p3 ∧ (p5 ∨ False)) ∧ p5)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68852360056979735247614000258 : ((p4 → ((p4 → p3) ∨ (p3 → (((((p1 → (True ∧ p3)) → p4) ∨ p4) ∧ (((p3 → (p4 → (p1 ∨ True))) ∧ p4) → p2)) ∧ p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58782268151390758025943090122 : (((p4 → p5) ∧ ((p4 ∨ ((((((p2 ∨ (p4 ∨ p4)) ∧ p1) ∧ p1) ∨ ((((p2 ∧ p3) ∧ p1) ∧ False) ∧ False)) ∧ True) ∧ p3)) ∧ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_718573754354511681472640759175 : (((((p4 → (p5 → p3)) → p4) ∨ (p4 ∨ ((p3 → (p2 → (((p5 ∧ (True → True)) → p2) → (False → True)))) ∨ ((p4 → False) ∨ p5)))) ∨ p2) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179200930254213729018479683398 : ((p3 ∧ (p5 ∨ (((p5 ∨ False) ∧ ((p4 ∨ (True ∧ True)) ∨ True)) ∨ p4))) ∨ (((p5 ∧ p2) ∨ False) → ((p4 ∨ (p3 ∨ p5)) → (False → p1)))) := by
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
theorem thm_5_vars_245798033361873372313370885692 : ((p3 ∧ p3) ∨ (((p2 ∨ p4) ∨ p5) ∨ (((True → (p1 → p3)) ∧ ((p5 → True) ∧ p4)) → ((p4 → (p5 → False)) → (True ∨ (True ∧ p5)))))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_353458443477065232759198394695 : (p4 → (p1 ∨ (p5 ∨ ((p1 ∨ (p1 ∨ (p2 ∧ (((p3 ∨ p5) → True) ∨ ((((p5 → True) ∧ True) ∨ p3) ∧ p1))))) → (p3 ∨ (True ∨ p3)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
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
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h10 =>
        -- Conjunctions on the left can always be decomposed.
        let h11 := h10.left
        let h12 := h10.right
        -- Disjunctions on the left can always be decomposed.
        cases h11
        case inl h13 =>
          -- Conjunctions on the left can always be decomposed.
          let h14 := h13.left
          let h15 := h13.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h16 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117170215674336983554132114761 : ((True ∧ ((((p5 ∧ p3) → (False ∨ (p3 ∨ ((p1 ∨ p3) → ((p5 ∧ p4) ∨ p2))))) → ((True ∧ (p5 ∧ p5)) → p1)) → p4)) ∨ (False → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_618736832023779914934293891765 : ((((((p3 ∧ p4) → p3) ∧ ((((p3 ∨ p2) ∨ (((p3 ∧ (p3 ∧ p1)) → (True ∨ p5)) ∨ (p3 → p3))) ∧ p5) → (p4 ∧ p5))) ∨ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234310994711179186168754656942 : ((p1 → (p1 ∧ True)) → (((((p1 → True) ∨ p3) ∧ p4) ∧ ((p2 ∨ (p1 ∧ ((p2 ∨ p5) ∧ True))) ∧ p1)) ∨ (True → (p4 → (p3 → True))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_209249433546909724530094659255 : ((p5 ∨ ((False → p5) → (p4 ∧ p5))) → ((True → (p5 ∧ ((p2 ∨ (((((True → (p1 ∧ False)) ∨ p5) ∨ p4) ∧ p2) ∨ True)) ∨ p2))) ∨ p2)) := by
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
    -- One of the premise coincides with the conclusion.
    exact h2
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
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h6 : (False → p5) := by
      -- Implications on the right can always be decomposed.
      intro h7
      -- False on the left can always be used.
      apply False.elim h7
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h8 := h4 h6
    -- We need to get the right conjuct of h8 based on <expert-advice>.
    let h9 := h8.right
    -- One of the premise coincides with the conclusion.
    exact h9
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56100523436715616868630974493 : ((((p3 ∨ p4) ∧ (p2 → p4)) ∨ (p4 → (p2 ∨ (True ∧ ((False → (((p1 ∨ p5) ∧ ((True ∧ p4) → (p4 ∨ p5))) → p3)) ∧ p5))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336292485802153373475464278218 : (p1 → (((p1 ∧ (False ∧ ((p4 → True) ∧ (p4 ∨ True)))) ∨ ((False ∧ True) ∨ ((p3 ∨ False) ∧ (((False ∧ p5) ∨ (p3 ∧ False)) ∧ p3)))) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_591999345389324606697703858937 : (((((True ∧ (((True → (False ∨ (((p2 ∨ (((True ∨ p4) ∧ p4) ∧ False)) → p1) → (p4 ∧ p1)))) ∧ p5) ∨ True)) ∨ (p2 ∧ p3)) ∧ True) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_731497017508021916422769719879 : ((((True → (p4 → p3)) → ((p5 ∨ (False ∨ False)) ∨ (p2 → (((p3 ∨ (p2 → ((p1 ∨ (p2 ∧ p4)) → p4))) ∨ True) → (p3 → p3))))) ∨ p1) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h7 =>
      -- One of the premise coincides with the conclusion.
      exact h4
  case inr h8 =>
    -- One of the premise coincides with the conclusion.
    exact h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158792734726798619368453227362 : ((p5 ∧ ((((p4 ∧ (p3 ∧ (p4 → p3))) ∧ (p2 → (True ∧ p5))) ∨ p2) ∨ (False → (p2 ∨ p4)))) ∨ (True → (p5 → (p3 → (p3 ∨ p1))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_141030071541161679297348777289 : ((((True ∨ p5) ∧ ((p5 → False) → (True ∧ False))) ∧ (((True ∧ p4) ∧ (p1 ∨ (p1 ∨ False))) ∨ (p3 → (p3 ∧ p1)))) → ((True → False) → p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Conjunctions on the left can always be decomposed.
      let h11 := h9.left
      let h12 := h9.right
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h13 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h14 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h15 := h2 h14
        -- False on the left can always be used.
        apply False.elim h15
      case inr h16 =>
        -- Disjunctions on the left can always be decomposed.
        cases h16
        case inl h17 =>
          -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
          have h18 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h2, we can now drive its conclusion.
          let h19 := h2 h18
          -- False on the left can always be used.
          apply False.elim h19
        case inr h20 =>
          -- False on the left can always be used.
          apply False.elim h20
    case inr h21 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h22 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h23 := h2 h22
      -- False on the left can always be used.
      apply False.elim h23
  case inr h24 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h25 =>
      -- Conjunctions on the left can always be decomposed.
      let h26 := h25.left
      let h27 := h25.right
      -- Conjunctions on the left can always be decomposed.
      let h28 := h26.left
      let h29 := h26.right
      -- Disjunctions on the left can always be decomposed.
      cases h27
      case inl h30 =>
        -- One of the premise coincides with the conclusion.
        exact h24
      case inr h31 =>
        -- Disjunctions on the left can always be decomposed.
        cases h31
        case inl h32 =>
          -- One of the premise coincides with the conclusion.
          exact h24
        case inr h33 =>
          -- False on the left can always be used.
          apply False.elim h33
    case inr h34 =>
      -- One of the premise coincides with the conclusion.
      exact h24



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138214012700709094990725337735 : ((p2 → (((p3 ∨ ((((p4 ∧ (p2 ∨ False)) → p5) ∧ p4) → (True ∧ False))) ∨ ((p3 → (p4 ∧ p2)) ∧ p1)) ∨ True)) ∨ ((True ∧ False) ∧ p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_229881793847877859520748377315 : ((p5 → (p4 ∨ p1)) ∨ ((p4 ∨ False) ∨ (p5 → (((p1 ∧ (p2 ∧ (True ∨ p3))) ∧ False) ∨ (((((p4 ∧ True) → False) ∨ p4) ∨ p4) → True))))) := by
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
theorem thm_5_vars_157386271953780094543978951688 : ((((((((p4 ∧ True) ∨ p5) ∨ ((False ∧ p3) ∨ p3)) ∧ False) ∨ (True ∧ p3)) ∨ p2) ∧ (p2 → True)) ∨ ((p2 → p2) ∨ ((p4 → False) → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179218456914947398955751746582 : ((p4 ∧ ((p3 ∧ (p4 → (p1 ∨ p3))) ∧ ((False ∨ (p1 ∨ p5)) ∧ p1))) ∨ (((False → p1) → ((True ∧ p4) → (p2 ∧ (True ∨ p5)))) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185330310438390604170905506175 : ((p3 ∧ (p1 ∨ ((p4 ∨ ((p5 ∨ p3) ∧ p2)) → (p2 ∧ p1)))) ∨ (p2 → (p3 ∨ ((((p4 ∨ p5) ∧ False) ∨ (p1 → p1)) ∨ (p5 → p1))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_93193547612337228821434582280 : ((True ∧ (False ∨ (((p2 → (((False ∨ ((True ∧ (p3 ∧ False)) ∧ (p4 ∨ p4))) ∨ p2) → False)) ∧ (True → ((p1 ∨ p3) ∨ p1))) ∧ p2))) → p3) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h6.left
    let h9 := h6.right
    -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
    have h10 : p2 := by
      -- One of the premise coincides with the conclusion.
      exact h7
    -- We have shown the premise of h8, we can now drive its conclusion.
    let h11 := h8 h10
    -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
    have h12 : ((False ∨ ((True ∧ (p3 ∧ False)) ∧ (p4 ∨ p4))) ∨ p2) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h7
    -- We have shown the premise of h11, we can now drive its conclusion.
    let h13 := h11 h12
    -- False on the left can always be used.
    apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319180341767317473378197216371 : (p4 ∨ ((True ∧ ((False ∧ (((p2 → (p1 ∨ False)) ∨ (p2 → ((p1 → p5) → p1))) ∧ False)) ∨ p3)) ∨ (True ∨ (False ∧ (p1 ∧ (p2 → p3)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172794613922965564297792330097 : (((p2 → p3) → (p5 → ((((p3 ∧ (p1 ∧ (p2 ∧ p2))) ∧ p5) ∨ p4) ∧ True))) ∨ ((p4 ∨ True) → ((p4 → (p4 → (p5 ∨ p4))) ∨ False))) := by
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
    -- Implications on the right can always be decomposed.
    intro h4
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h6
    -- Implications on the right can always be decomposed.
    intro h7
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_779454900677217127541749388314 : (((p2 ∨ (((False → (((True ∨ p5) ∨ False) ∨ ((p2 ∨ ((p2 → (p5 → (False ∧ p2))) ∧ (p2 → p3))) ∧ p4))) → (p1 ∨ p5)) ∨ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_311218617474578581535906128404 : (p2 ∨ ((False → p2) → (((p5 ∨ (p1 ∧ p2)) ∨ (((((p4 ∨ (p2 → False)) → p4) ∨ False) ∨ (p3 ∧ p2)) ∨ (p1 → (p5 → p1)))) ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49358002327435048805815358290 : (((p2 → ((p4 ∧ False) ∨ ((p4 ∧ False) ∨ ((p4 → p1) → (((False ∧ (p3 ∧ True)) ∨ (p3 ∨ p4)) ∧ p1))))) ∨ ((p5 → p2) ∧ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60462473510057834509353998701 : (((p5 → p2) → (p4 ∨ (((((p5 ∨ (p2 ∨ ((True ∧ p1) ∧ p1))) ∨ p4) ∨ p2) ∧ (p2 → (p3 → p3))) ∨ ((False → p2) ∨ p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117514061412459689728886053925 : ((p2 ∧ ((((True → (p3 ∧ p1)) → (True → ((True → p5) ∧ p1))) → (((((True → p4) ∧ p4) → p5) ∧ p5) ∨ p1)) ∨ p3)) ∨ (True ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46912714648875302913606853072 : (((((((p1 ∧ ((True ∨ True) → (p5 ∨ (p1 → p5)))) ∧ p3) ∧ p1) → (p4 ∧ ((False ∧ (p1 → p2)) ∨ False))) ∨ p1) ∨ (p3 → p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_216940880137701231059245899153 : (((False → (p1 ∨ True)) ∧ p2) → ((p4 → ((p5 ∧ (True → p5)) ∨ p2)) ∨ (p2 ∨ ((((p2 ∨ True) ∧ p4) ∧ ((p1 ∨ p1) → p4)) → False)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_145116835757283162954901112208 : (((((True ∨ p1) → (False ∧ p2)) ∧ ((p3 ∧ False) ∧ False)) ∨ ((p3 → (p4 → ((p4 ∧ p5) ∧ p5))) ∨ True)) ∧ ((p3 ∧ (p1 → True)) → p3)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225473057543837137952423110353 : (((p4 ∨ p4) ∧ p1) ∨ ((((True ∨ True) ∨ (p2 → (p2 ∧ (p5 ∨ (p5 → True))))) → (p2 ∧ (p3 ∧ p2))) ∨ ((True ∧ (p5 → p5)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_243424191172830249039690908564 : ((p5 → True) ∧ (((p2 ∨ (p5 ∧ ((False ∧ p2) ∧ p2))) ∨ p3) ∨ (p2 ∨ (((p3 → ((True → p5) ∧ False)) ∨ (p1 → p1)) → (p2 ∨ True))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
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
theorem thm_5_vars_159557369967170887748097332497 : (((p1 ∨ ((((p4 ∧ (p1 ∧ (p5 ∧ ((p1 ∧ p3) → (p1 → p5))))) ∨ p5) ∧ False) ∨ p2)) ∧ p5) → (((p1 → p1) → p3) ∨ (p2 ∨ p1))) := by
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
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h9 =>
        -- Conjunctions on the left can always be decomposed.
        let h10 := h9.left
        let h11 := h9.right
        -- Conjunctions on the left can always be decomposed.
        let h12 := h11.left
        let h13 := h11.right
        -- Conjunctions on the left can always be decomposed.
        let h14 := h13.left
        let h15 := h13.right
        -- False on the left can always be used.
        apply False.elim h8
      case inr h16 =>
        -- False on the left can always be used.
        apply False.elim h8
    case inr h17 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_241426532816765468909453584509 : ((False → p1) ∧ (((p2 ∨ p3) → p2) → (((((p3 → ((True → False) → False)) → (p3 ∧ False)) → (p2 ∧ p5)) ∨ ((True → p3) ∧ p5)) ∨ p4))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : (p3 → ((True → False) → False)) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- Implications on the right can always be decomposed.
    intro h6
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h7 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h8 := h6 h7
    -- False on the left can always be used.
    apply False.elim h8
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h9 := h3 h4
  -- We need to get the right conjuct of h9 based on <expert-advice>.
  let h10 := h9.right
  -- False on the left can always be used.
  apply False.elim h10
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h11 : (p3 → ((True → False) → False)) := by
    -- Implications on the right can always be decomposed.
    intro h12
    -- Implications on the right can always be decomposed.
    intro h13
    -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
    have h14 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h13, we can now drive its conclusion.
    let h15 := h13 h14
    -- False on the left can always be used.
    apply False.elim h15
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h16 := h3 h11
  -- We need to get the right conjuct of h16 based on <expert-advice>.
  let h17 := h16.right
  -- False on the left can always be used.
  apply False.elim h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118619580521380825079026443777 : ((p4 ∨ ((p1 ∧ ((p2 ∧ ((p1 → (p2 ∨ p4)) ∧ p4)) ∧ p3)) ∨ ((p2 → ((p2 ∧ p5) ∧ (p5 → True))) ∨ (p1 ∨ p2)))) ∨ (p5 → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_680137323285915331459463097558 : (((((p4 ∧ (((p4 → p5) ∧ (p2 ∨ p4)) → (True ∨ ((False ∨ p5) ∧ (p1 ∨ p1))))) ∧ (p1 ∧ p3)) → ((p5 ∨ p5) → (p1 ∧ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118156614674077381927097732268 : ((False ∨ ((p2 ∧ ((p2 → p5) ∨ p1)) ∨ (((True ∨ ((((p1 ∧ True) → p1) ∧ p3) ∧ p2)) ∨ p3) → ((False ∧ p1) ∧ False)))) ∨ (True ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37104225928120651512196219935 : ((((((False ∨ (p4 → (((((p4 → p1) ∨ p3) → ((p2 ∧ (p4 ∧ p1)) ∨ True)) → p3) ∧ (p5 ∨ True)))) → p3) → p1) ∧ p1) ∧ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50446706791108539867870306908 : (((p1 ∨ (p4 → ((p3 → (((p4 ∨ (False → (p1 ∨ (True ∨ (False ∧ p1))))) ∨ p5) ∧ p2)) → p5))) ∨ ((p5 ∨ (p3 → p4)) → True)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321570369601952012949488581637 : (p4 ∨ (p2 → ((p2 → p4) ∨ (((p3 ∨ False) → (False → p4)) ∧ (p1 ∨ ((p2 ∧ ((False ∧ p1) ∨ (p2 ∨ (p3 ∨ (p3 → p5))))) ∨ p3)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197937899382997394461807201093 : (((True ∧ p4) ∧ ((p2 ∧ p5) ∨ (p1 ∨ p5))) ∨ (True ∨ (p3 ∧ ((((p1 ∨ p5) ∨ False) ∨ (True ∨ (p1 → ((p2 ∨ True) → True)))) → p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62050389293398867557730609054 : ((p2 ∧ ((p4 → False) ∨ ((p3 ∨ False) ∨ ((p5 ∨ (True ∨ p2)) ∧ (p2 ∨ ((False ∨ ((p2 → (p5 ∨ (False → p1))) ∧ p4)) ∨ p4)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37780189069206405788032605714 : (((((p4 → True) ∧ (False → ((((p2 → (p1 → p1)) ∨ (((True ∧ False) ∧ ((p3 ∨ p4) ∨ p2)) ∨ False)) ∨ p4) → p1))) → p3) ∧ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_703161874328959807061691071044 : (((((p1 → p4) → ((p5 ∨ (True ∧ p2)) ∨ (p1 ∧ True))) ∨ (p1 ∨ (p2 → (p5 ∨ (((p1 ∨ p3) → p2) ∨ ((p5 → p4) → False)))))) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h4 =>
    -- One of the premise coincides with the conclusion.
    exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_784407320418305004701569824507 : (((p3 ∨ (p4 ∧ (((True ∨ (p2 → (p5 → ((p1 → ((p4 ∧ False) ∧ (True ∨ False))) → ((p1 → (p5 ∨ p5)) ∧ p3))))) → p1) ∨ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307422380300375905013718992443 : (p1 ∨ (p5 ∨ (((p1 → (((p3 ∧ (p1 ∧ p1)) ∨ p2) → ((p5 → True) → ((False ∨ (p5 ∧ ((False → True) ∨ p2))) ∨ True)))) ∧ True) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230648290582072932248109356342 : (((p3 → False) ∧ p3) → (p2 ∨ (False ∨ ((p2 → (((False ∧ p2) ∨ (p2 → ((p5 → p5) ∨ ((p2 ∧ (p4 ∧ p1)) ∧ p1)))) → False)) ∨ p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : p3 := by
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185500727947205267331630241610 : ((p2 ∨ (((p1 ∧ p5) ∨ p3) ∧ ((True → p1) ∧ (p4 ∨ p3)))) ∨ (((True ∧ False) ∧ p5) → (((p2 ∧ p1) ∧ (False ∨ (p5 ∨ False))) ∧ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- False on the left can always be used.
  apply False.elim h5
  -- Conjunctions on the left can always be decomposed.
  let h6 := h1.left
  let h7 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- False on the left can always be used.
  apply False.elim h9
  -- Conjunctions on the left can always be decomposed.
  let h10 := h1.left
  let h11 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h12 := h10.left
  let h13 := h10.right
  -- False on the left can always be used.
  apply False.elim h13
  -- Conjunctions on the left can always be decomposed.
  let h14 := h1.left
  let h15 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h16 := h14.left
  let h17 := h14.right
  -- False on the left can always be used.
  apply False.elim h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149083935060767471448207275549 : ((((p5 → p3) → p5) → ((p5 → (((p4 → (p5 → True)) ∧ False) → (p2 → ((p2 ∨ True) ∧ p1)))) → p5)) ∨ (True ∨ (p5 ∨ (p4 → True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219235395627628001980308703571 : ((p1 ∨ ((p5 ∨ True) ∨ False)) → (p3 → ((p4 → (((p5 ∨ ((p3 ∧ (True ∨ p1)) ∨ p2)) ∧ ((p3 ∨ p5) → p5)) ∨ p5)) ∨ (p4 → True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h8
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h10
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h11 =>
      -- False on the left can always be used.
      apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_326978042657465517714381586846 : (True → ((((((((((p2 → p2) ∧ (True → False)) ∨ p5) → p1) → p5) ∧ ((p4 → p3) ∨ p1)) ∨ True) → p4) ∨ (p4 → (p4 ∨ p5))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_343574432155218144565770850355 : (p2 → ((True → p2) → (((p1 ∧ (p4 ∧ (p2 ∧ ((((p2 ∧ p2) ∧ True) ∧ ((p2 ∧ p1) ∨ p3)) ∧ (False ∧ p4))))) ∨ True) ∧ (p5 ∨ p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185431561846632056789140884291 : ((False ∨ ((p5 ∨ ((False → p3) ∧ ((p2 ∧ p1) ∧ p5))) ∨ p5)) ∨ (((((p2 ∧ p2) ∨ False) ∨ False) → True) → (False → ((p4 ∨ p3) ∨ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_140716034957047684946644456533 : (((p3 ∧ (p5 ∧ (p3 ∧ (((p5 → (p1 ∧ (p4 ∧ p1))) ∨ p1) ∧ p1)))) ∨ (p1 ∧ ((p1 → (p1 ∨ True)) → p1))) → (p4 ∨ (True → True))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h12
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h13 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h14
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h15 =>
    -- Conjunctions on the left can always be decomposed.
    let h16 := h15.left
    let h17 := h15.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h18
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_352241317520508562616768490834 : (p4 → ((p1 ∧ ((p4 ∧ p3) → p4)) ∨ ((p3 ∧ p3) ∨ (p5 ∨ ((p1 ∧ (True ∧ (p4 ∧ (True ∨ (True ∨ p4))))) ∨ (p1 ∨ (True ∧ p4))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_252576591520417681865280668296 : ((p5 → p3) ∨ (((((p2 → True) → False) ∧ p5) ∧ ((p3 ∧ ((p1 → ((p3 ∧ (False → p3)) ∧ False)) ∧ ((True ∨ p3) → p5))) ∧ p2)) → False)) := by
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
  let h6 := h3.left
  let h7 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- Conjunctions on the left can always be decomposed.
  let h10 := h9.left
  let h11 := h9.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h12 : (p2 → True) := by
    -- Implications on the right can always be decomposed.
    intro h13
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h14 := h4 h12
  -- False on the left can always be used.
  apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_712878093324627350913308782371 : (((((p3 → True) → ((p2 ∧ False) ∧ True)) ∨ (p1 ∨ ((((p2 ∧ p4) → (p5 ∨ False)) ∨ True) ∨ (True ∧ (((p3 ∨ p2) ∧ p4) ∨ False))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228802852866832805552189778528 : ((p3 ∨ (p1 ∨ p2)) ∨ ((p3 ∧ ((p4 → (p4 → False)) → p4)) ∨ (p2 ∨ (p2 → (p4 → ((False → (True → ((False ∧ p1) ∧ p3))) ∨ p3)))))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h3
  -- False on the left can always be used.
  apply False.elim h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42601550000327187391287101210 : (((p2 ∨ (p1 → ((p4 → p5) ∨ (((((p5 ∧ (False → ((False → False) ∨ (p1 ∨ p2)))) ∧ p2) → p4) ∨ (p3 ∧ True)) ∧ True)))) ∨ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_715219160948027590104826874970 : ((((False → (p4 → ((True ∧ True) ∧ p3))) → ((((p1 ∧ (p3 ∧ p2)) ∧ (p2 ∨ True)) ∨ False) ∧ ((True → (True ∨ p5)) ∨ (p2 → p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200338619366741553142772476310 : (((p3 ∨ True) ∧ (p4 ∨ ((p2 ∨ p4) ∨ False))) → ((((p1 ∧ p4) → ((p2 → ((p5 ∧ False) ∨ p1)) ∨ (p3 → True))) ∨ (True → p1)) ∨ True)) := by
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
        -- False on the left can always be used.
        apply False.elim h10
  case inr h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h13 =>
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h14 =>
        -- Disjunctions on the left can always be decomposed.
        cases h14
        case inl h15 =>
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
        -- False on the left can always be used.
        apply False.elim h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47406636950698476504928624945 : (((False ∧ (((p3 → p2) ∧ ((p3 ∨ (((p1 ∧ p2) ∨ (p4 → p2)) → (p5 ∨ ((p3 → False) → p3)))) ∧ p1)) ∧ p1)) ∨ (True ∨ p1)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54085179570145062678203153898 : ((((False ∨ p2) ∨ (False → ((p5 ∨ p2) ∨ (p5 ∨ p5)))) → (((p3 ∧ (((p4 ∨ p2) → ((p1 ∨ p3) ∨ p4)) ∨ p3)) ∨ True) → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_349748604361507627195399852475 : (p4 → ((((p1 ∨ ((False ∧ p3) → p4)) ∨ True) → (p5 ∨ ((((p5 ∨ False) ∧ ((p4 → False) → (p1 ∨ (True → p5)))) ∨ p4) ∨ p3))) ∧ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317094172402999069651858602296 : (p3 ∨ (p5 → (((((p2 → p4) ∨ (False ∨ (((False ∨ ((p4 ∧ p5) ∨ p1)) → (p2 ∨ (True → (False → True)))) → p2))) ∧ p1) → p4) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178483999512976233018960963520 : ((((False ∧ (p2 ∨ (p3 ∧ p2))) ∨ (True ∧ False)) ∨ ((p1 ∧ p4) → p4)) ∨ (((p1 ∧ (True ∨ ((p5 ∧ False) → p3))) ∨ (p2 ∨ False)) → False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_261564034799058078847712582005 : ((p5 → p4) → ((((((p2 ∨ (p1 ∨ ((p5 ∨ p4) ∨ p4))) → p3) ∨ True) → p5) ∧ ((((p1 ∧ (p2 → p4)) → True) ∨ p1) ∨ p3)) → p4)) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h7 : (((p2 ∨ (p1 ∨ ((p5 ∨ p4) ∨ p4))) → p3) ∨ True) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h8 := h3 h7
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h9 : p5 := by
        -- One of the premise coincides with the conclusion.
        exact h8
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h10 := h1 h9
      -- One of the premise coincides with the conclusion.
      exact h10
    case inr h11 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h12 : (((p2 ∨ (p1 ∨ ((p5 ∨ p4) ∨ p4))) → p3) ∨ True) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h13 := h3 h12
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h14 : p5 := by
        -- One of the premise coincides with the conclusion.
        exact h13
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h15 := h1 h14
      -- One of the premise coincides with the conclusion.
      exact h15
  case inr h16 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h17 : (((p2 ∨ (p1 ∨ ((p5 ∨ p4) ∨ p4))) → p3) ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h18 := h3 h17
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h19 : p5 := by
      -- One of the premise coincides with the conclusion.
      exact h18
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h20 := h1 h19
    -- One of the premise coincides with the conclusion.
    exact h20



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115703107033464752517255921801 : ((((((p3 ∧ p4) ∨ p5) → p4) ∧ p3) → (((p2 → False) ∨ ((p4 → p3) ∧ ((p2 → (p5 → (p4 ∨ p3))) ∧ p3))) ∨ p3)) ∨ (p5 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158624564425647461033859063664 : ((False ∧ (p5 ∨ ((((p2 → p2) ∨ p5) ∨ (True → (False ∧ ((p1 ∨ p2) ∧ True)))) → (False ∧ p4)))) ∨ ((p2 ∧ ((False ∧ True) ∧ p1)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_664963107732150146563589289519 : ((((p3 → (p3 ∧ ((p1 → p4) ∨ ((((p5 → p3) ∨ ((False ∧ p2) ∧ p3)) ∨ True) ∧ (((p5 ∧ False) ∨ p4) ∧ p2))))) → (p1 ∧ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



