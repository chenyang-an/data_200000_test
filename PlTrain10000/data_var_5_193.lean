variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39695941540131583482957856717 : (((p4 ∨ (True ∧ ((((((True ∨ p3) ∧ p5) → (p5 ∨ (p5 ∧ p5))) ∧ (False → (p5 → False))) ∨ (p2 → p2)) → (True → p1)))) ∧ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206914992563703096516730168463 : ((((True ∧ (p2 → True)) ∨ True) ∧ p5) → (((((p4 → (True → ((p2 ∨ ((p4 → (p4 ∨ False)) → p5)) ∧ True))) ∨ p5) ∧ p1) ∨ False) ∨ p5)) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_120681926103586800261129221492 : ((((((p3 ∨ ((p1 ∨ ((p2 → (p3 ∧ p3)) ∨ (p2 ∧ (True → p5)))) → p3)) → (p1 ∨ p3)) ∧ p2) ∧ (p3 ∨ p2)) ∨ True) → (p5 ∨ True)) := by
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
    cases h4
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
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137300656035374446229441031646 : ((p2 ∧ ((((p5 → (p3 ∧ (True ∨ True))) ∧ True) → ((p3 ∧ p4) ∧ (p2 → (False ∧ (p4 ∧ p4))))) ∨ (p2 ∨ True))) ∨ (p4 ∨ (p1 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134337549535310766225270071179 : (((p4 ∧ (((((p3 → (p2 ∨ p3)) ∨ False) → (False ∧ p4)) ∧ ((False → True) ∧ (p2 → (p2 ∨ p1)))) → False)) ∨ p3) ∨ ((p5 ∨ p1) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230936520871784823966941511881 : (((p3 ∧ p2) ∨ p5) → ((p1 ∧ p5) ∨ (((p2 ∨ p1) → (p4 ∨ False)) → (p5 → (((p5 → ((p3 ∧ p5) ∧ p1)) ∨ (p2 ∨ True)) ∧ p5))))) := by
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
    -- Implications on the right can always be decomposed.
    intro h6
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- Implications on the right can always be decomposed.
    intro h9
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
    -- One of the premise coincides with the conclusion.
    exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135681892284617495827303449185 : ((((p2 → ((p3 ∧ False) ∨ ((p4 → ((p1 ∨ p5) ∨ p3)) ∨ p1))) ∧ False) ∧ ((p3 ∧ (p5 ∨ p4)) ∧ (p5 → True))) ∨ ((p4 ∧ False) → False)) := by
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
theorem thm_5_vars_615350566172574342622038998345 : (((((((p3 ∨ (((p1 → p4) → p1) ∨ False)) ∧ p2) → (((p3 ∧ p3) ∧ True) ∧ p2)) ∨ (False ∧ (((p3 ∧ True) ∨ p1) → p3))) ∨ True) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_102826789323390781515095742405 : ((((((p5 ∧ ((p1 ∨ False) → (((p4 → p1) → p3) ∧ (p4 ∨ (p2 → (p3 → False)))))) ∧ p1) ∧ p5) ∧ (p1 → p1)) ∨ True) ∧ (True ∨ p3)) := by
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
theorem thm_5_vars_200783130328893138087801087829 : ((p4 ∧ (p3 ∧ (((False → False) → p1) → p4))) → ((p3 → (True ∧ ((p2 ∧ (True ∨ (p4 ∨ (True ∨ (p1 ∨ p1))))) ∨ False))) ∨ (True ∨ p4))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_261558488448620393531588989427 : ((p5 → p4) → (((True → (p2 ∧ ((p3 → (p2 ∧ (True → (False ∨ p3)))) ∧ True))) ∨ (((p2 ∨ p3) → ((p5 → True) ∨ p2)) ∨ False)) ∨ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h4
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h6
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_71206923224856636124448739474 : (((((False → p5) ∨ p2) ∧ (((p5 → (p3 → p3)) ∨ (p3 ∨ False)) → (True ∧ ((((p4 → p1) ∨ (p2 → p4)) ∧ p2) ∧ p4)))) ∧ p4) → p2) := by
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
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h7 : ((p5 → (p3 → p3)) ∨ (p3 ∨ False)) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h8
      -- Implications on the right can always be decomposed.
      intro h9
      -- One of the premise coincides with the conclusion.
      exact h9
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h10 := h5 h7
    -- We need to get the right conjuct of h10 based on <expert-advice>.
    let h11 := h10.right
    -- We need to get the left conjuct of h11 based on <expert-advice>.
    let h12 := h11.left
    -- We need to get the right conjuct of h12 based on <expert-advice>.
    let h13 := h12.right
    -- One of the premise coincides with the conclusion.
    exact h13
  case inr h14 =>
    -- One of the premise coincides with the conclusion.
    exact h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112129658187193835562454015734 : (((False ∧ (((((True ∧ ((((p3 ∨ True) → p3) ∧ (p4 → True)) ∧ (p4 → (p1 ∨ p2)))) → True) ∧ False) ∧ p4) ∨ p4)) ∨ p1) ∨ (True ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_592730540960050797091990471318 : ((((((((p5 ∧ (((False ∨ True) → ((p2 ∨ True) ∨ (p2 → p2))) → True)) ∨ True) → (p3 ∨ p4)) ∨ True) ∧ (False → (p5 ∨ p4))) ∧ True) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218858052439502509833138444875 : ((p2 ∧ (p1 ∧ (True → p1))) → ((((p1 ∧ (p1 ∨ p4)) → (p3 ∨ False)) ∧ (p1 → p3)) ∨ ((p5 ∧ (True ∧ (False ∧ (p4 → True)))) → True))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199920827036415645507963823613 : ((((p3 → p1) ∧ (p4 ∨ p1)) ∨ (True → p1)) → ((p3 ∨ (((False ∧ (p1 ∨ p4)) → p1) ∧ ((False ∨ p2) ∧ (True ∨ (p2 ∧ p3))))) ∨ True)) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_122461904208190350861174558049 : (((((p2 → p4) ∧ ((p4 ∨ p5) ∧ p1)) → (((False ∨ ((p3 ∧ (False → p5)) ∨ p3)) ∨ (p4 ∧ p2)) → p5)) ∨ (p5 → p4)) → (p4 ∨ True)) := by
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
theorem thm_5_vars_204694803322238857156348878744 : (((p3 ∨ ((False ∨ False) ∨ p4)) ∨ p4) ∨ (p3 ∨ (((p5 → p4) → ((((p1 ∧ p1) ∧ (True ∨ False)) → True) → ((p1 ∨ p5) ∧ p4))) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_669472436531121007868877979304 : ((((((True → ((p3 ∧ p4) → (((p5 ∧ (p1 ∧ (True ∨ True))) ∧ (p1 ∧ True)) ∨ p5))) ∧ True) → (p3 ∧ p2)) ∨ (p3 → (p2 ∨ p3))) ∨ p4) ∧ True) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_326872596569281801208646553347 : (True → (((((p4 → False) → ((p4 ∧ ((((p5 ∨ p5) → (p2 → ((False ∨ p4) ∨ p3))) ∧ p4) → p4)) ∨ p2)) → (p2 ∧ p3)) ∨ True) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_85754799996123382572694309573 : ((((((((p5 ∨ p5) ∧ False) ∧ p5) ∧ p2) → p4) ∧ (p5 → True)) → ((p4 ∧ (p1 → (((p5 ∨ (p2 ∨ p2)) ∨ True) ∨ p1))) ∧ p5)) → p5) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((((((p5 ∨ p5) ∧ False) ∧ p5) ∧ p2) → p4) ∧ (p5 → True)) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
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
      -- False on the left can always be used.
      apply False.elim h9
    case inr h11 =>
      -- False on the left can always be used.
      apply False.elim h9
    -- Implications on the right can always be decomposed.
    intro h12
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h13 := h1 h2
  -- We need to get the right conjuct of h13 based on <expert-advice>.
  let h14 := h13.right
  -- One of the premise coincides with the conclusion.
  exact h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65621604732956302227331963448 : ((p4 ∨ ((((p3 ∧ (((True → ((p2 ∧ p4) → p2)) ∨ p5) ∨ (p4 ∨ ((p4 → p4) ∧ ((p4 ∨ p1) → p4))))) → p5) ∧ p4) ∨ True)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118761399579445063069657968678 : ((p5 ∨ ((True ∨ False) → ((((p1 ∧ (p2 ∨ p5)) ∨ p2) ∨ (False ∨ ((p1 ∧ ((False → p5) ∧ p3)) ∧ p2))) ∨ (p4 → p5)))) ∨ (True ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_784339576527530510381012010613 : (((p3 ∨ (p2 ∧ ((((p5 ∧ p2) → (p5 ∨ (p3 ∧ True))) ∨ (((p1 → (False → (p5 → p1))) ∨ p5) ∨ p2)) → (p1 → (p4 ∧ p3))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58969862001809876931014485186 : (((p2 ∧ p3) ∨ (((p1 ∨ p3) → ((p2 ∨ ((p4 ∨ p2) ∧ ((p1 → p5) ∧ p3))) ∨ p3)) ∧ ((p2 ∧ p3) ∨ ((p5 ∧ True) ∧ True)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230687886567456691601111012319 : (((p4 → False) ∧ p4) → (((p3 ∧ p5) ∨ (((((p3 → p2) ∨ p1) ∧ p3) ∧ (p3 ∧ p5)) ∨ (((p4 ∧ (p2 ∨ p5)) → False) → p4))) ∨ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : p4 := by
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64073365382711524687757622720 : ((False ∨ ((((p5 ∨ True) ∨ p5) ∨ ((p2 ∧ p1) → (((True ∧ p3) → p1) → (True → p2)))) → (p4 → ((p1 → False) → (p1 → p3))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346284150539633119888148818835 : (p3 → (((((p1 ∧ ((p2 ∨ (p3 ∧ p2)) ∨ True)) ∨ ((p4 → (p1 ∧ (p4 ∧ p3))) ∧ False)) ∨ ((p1 ∨ p2) ∨ True)) ∧ False) ∨ (True ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41456328918571455206441204705 : (((((True ∨ ((p5 ∧ (p5 ∨ p1)) → p3)) → (False ∨ (p4 ∨ p5))) ∧ (p2 ∧ (False ∨ (p4 ∧ (p1 ∧ (p5 → (p3 ∨ False))))))) ∨ True) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_612338626163129827151751911007 : (((((p5 ∧ (p2 ∨ (((p1 → (((p2 ∧ (p4 → (((p2 ∧ p1) → p2) ∨ False))) ∨ p4) → p3)) ∧ p1) ∨ False))) ∧ (p3 → p1)) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198684623852352213978022160342 : ((p4 ∨ ((p2 ∨ p2) ∨ (p2 → (False ∨ False)))) ∨ ((((p2 ∧ (p4 ∨ (p1 → p4))) ∧ p4) → (((p2 ∧ p5) ∧ p2) ∨ (p3 → p4))) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_688655968948152981435488782037 : ((((True → ((p4 ∧ (p3 ∧ ((False ∧ (p5 ∧ (p1 ∧ False))) → (p4 ∨ False)))) ∨ p3)) ∧ ((p1 ∧ p5) → ((p3 → (p2 ∨ p1)) ∧ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_688671500823349043071639813840 : ((((True → (p4 ∨ (((p5 ∧ (((False → p1) → p2) ∧ p3)) ∨ (p1 ∧ False)) → False))) ∧ (((((p3 → p5) → p2) ∧ p4) ∧ False) ∧ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52197381754196864553427101868 : ((((p3 ∨ (True ∧ p5)) ∨ (((p2 ∧ p2) ∧ True) → ((p5 ∨ False) → (True → False)))) → (((False → p2) → (p4 ∨ (False → p4))) ∧ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310854307359730585425033262255 : (p2 ∨ (((p4 ∧ p1) → p3) → ((False ∨ p5) ∨ (p3 ∨ ((p3 ∨ (((False ∧ (True → p4)) ∧ p3) ∨ p3)) → (False → (p4 → (p1 ∨ p2)))))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h4
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259217286553235553469780498575 : ((False → False) → (((p4 → p4) → (p4 → p2)) ∨ ((((False → ((p1 ∨ True) ∨ ((p2 ∧ (p2 ∧ p4)) → (p2 → False)))) ∨ True) → p1) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43497143762889571597359825210 : ((((True ∨ ((((((p5 ∨ (p2 ∧ p1)) ∨ (p4 ∨ (p3 → False))) → False) ∧ (((p4 → p4) → p2) ∨ p4)) → p2) ∧ True)) ∨ p2) → p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_783169483069848761806145441306 : (((p3 ∨ ((((p3 → p4) ∨ ((((p3 → p3) ∧ p2) ∨ (p5 ∧ (p2 ∧ p5))) ∨ ((p4 ∨ p5) ∨ p5))) → p2) ∨ ((False → p2) ∨ p4))) ∨ p4) ∧ True) := by
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
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137731611543615016076107668295 : ((p1 ∨ (p1 ∨ (((p3 ∨ p1) ∨ ((p3 ∧ ((p1 → ((p3 ∧ True) → p3)) ∨ (p1 ∨ (True ∧ p5)))) ∨ p4)) ∨ True))) ∨ (p1 → (p5 ∨ p4))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112656930653943552670602341631 : ((((p4 ∨ ((p2 ∧ p4) → ((p1 ∨ (True → (((True ∧ (True ∨ p2)) ∧ p4) ∧ p1))) ∨ False))) ∧ (False ∨ (p2 ∨ p5))) → p4) ∨ (p3 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_778743078801045672277214448288 : (((p1 ∨ (p4 ∨ (((p2 → ((False ∨ (p4 ∧ False)) ∨ ((p5 → p5) ∧ (False ∧ (p4 ∧ p2))))) ∧ p4) ∨ ((p2 → p5) ∨ (p4 ∧ p2))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60434748794202611335515936319 : (((p4 → p4) → (p2 → ((False ∧ (p3 → p4)) ∧ ((((p1 ∨ (p1 ∨ ((False → (p5 ∧ p3)) ∧ True))) ∧ False) ∨ (False ∨ False)) → p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_355106583587592399481473496287 : (p5 → ((((((p4 → ((p1 ∨ p2) ∧ p1)) ∨ True) ∧ p4) → (((p2 ∨ True) ∨ p2) → (p4 → (False ∧ (p2 → p2))))) ∧ (p4 ∧ True)) → p2)) := by
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
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h7 : (((p4 → ((p1 ∨ p2) ∧ p1)) ∨ True) ∧ p4) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h8 := h3 h7
  -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
  have h9 : ((p2 ∨ True) ∨ p2) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h8, we can now drive its conclusion.
  let h10 := h8 h9
  -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
  have h11 : p4 := by
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h10, we can now drive its conclusion.
  let h12 := h10 h11
  -- We need to get the left conjuct of h12 based on <expert-advice>.
  let h13 := h12.left
  -- False on the left can always be used.
  apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114855370042508098958119641051 : ((((p4 ∧ (p5 ∨ (p4 ∨ (((p2 ∨ p4) → (p3 ∨ p1)) → False)))) → p5) ∨ (False → ((p5 → ((p2 → p3) ∨ p3)) ∨ p4))) ∨ (True ∧ p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_654794251087362558446460720226 : ((((((p5 → ((((p1 ∧ p2) ∨ (True ∧ (p2 ∨ (p4 → p1)))) ∧ (True ∨ p3)) ∧ ((True ∨ True) ∧ p3))) → p1) → p4) ∨ (p5 ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165238033780936844143902269329 : (((p1 ∧ (((((p3 ∧ p3) ∧ p1) ∧ (p2 ∧ p5)) ∧ p4) ∨ (True ∨ p4))) ∨ (p5 ∧ p1)) ∨ ((((p4 ∨ True) ∧ p2) → p3) → (True ∧ True))) := by
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
theorem thm_5_vars_663367930056543435959816420161 : (((((True ∧ p5) → (((p1 ∧ ((False ∨ (p5 ∧ (p5 ∧ ((p3 → (p4 ∧ (p4 ∧ p2))) ∧ True)))) ∨ p1)) ∧ False) ∨ p2)) → (p5 ∨ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193750435762524749990319611870 : ((p3 ∧ ((p3 → ((p2 → p3) ∧ False)) ∧ (p2 ∨ p4))) → (p2 → ((p4 ∧ ((p2 ∧ p5) → ((p5 → False) ∨ (p5 ∧ False)))) ∧ (p4 ∨ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h7 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h8 : p3 := by
      -- One of the premise coincides with the conclusion.
      exact h3
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h9 := h5 h8
    -- We need to get the right conjuct of h9 based on <expert-advice>.
    let h10 := h9.right
    -- False on the left can always be used.
    apply False.elim h10
  case inr h11 =>
    -- One of the premise coincides with the conclusion.
    exact h11
  -- Implications on the right can always be decomposed.
  intro h12
  -- Conjunctions on the left can always be decomposed.
  let h13 := h12.left
  let h14 := h12.right
  -- Conjunctions on the left can always be decomposed.
  let h15 := h1.left
  let h16 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h17 := h16.left
  let h18 := h16.right
  -- Disjunctions on the left can always be decomposed.
  cases h18
  case inl h19 =>
    -- We want to use the implication h17 based on <expert-advice>. So we show its premise.
    have h20 : p3 := by
      -- One of the premise coincides with the conclusion.
      exact h15
    -- We have shown the premise of h17, we can now drive its conclusion.
    let h21 := h17 h20
    -- We need to get the right conjuct of h21 based on <expert-advice>.
    let h22 := h21.right
    -- False on the left can always be used.
    apply False.elim h22
  case inr h23 =>
    -- We want to use the implication h17 based on <expert-advice>. So we show its premise.
    have h24 : p3 := by
      -- One of the premise coincides with the conclusion.
      exact h15
    -- We have shown the premise of h17, we can now drive its conclusion.
    let h25 := h17 h24
    -- We need to get the right conjuct of h25 based on <expert-advice>.
    let h26 := h25.right
    -- False on the left can always be used.
    apply False.elim h26
  -- Conjunctions on the left can always be decomposed.
  let h27 := h1.left
  let h28 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h29 := h28.left
  let h30 := h28.right
  -- Disjunctions on the left can always be decomposed.
  cases h30
  case inl h31 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h27
  case inr h32 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h32



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46831330795831778477063861465 : (((((False → ((p5 → (p5 → (p1 → True))) ∨ ((p2 ∧ ((p4 ∧ True) → p5)) ∧ p2))) → ((True → p4) ∨ p1)) ∧ p2) ∨ (True → True)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149234983771877247635105410269 : (((p5 ∧ p4) ∨ (p3 ∨ ((p5 ∧ p5) ∧ ((p1 → ((((p4 ∨ True) ∨ True) → (p3 ∨ p5)) ∧ False)) ∧ p1)))) ∨ ((p1 ∨ (p3 ∧ p3)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341198739141490426173016562161 : (p2 → ((((False ∧ ((p5 → ((((p4 → p3) → False) ∨ False) ∧ (((p3 ∨ ((True ∨ p1) → p2)) ∨ p4) ∧ p5))) ∨ False)) ∨ True) → False) → p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : ((False ∧ ((p5 → ((((p4 → p3) → False) ∨ False) ∧ (((p3 ∨ ((True ∨ p1) → p2)) ∨ p4) ∧ p5))) ∨ False)) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_618725481700990921649381633168 : ((((((True ∧ True) → p4) ∧ (p2 ∧ (True ∧ (((p1 ∨ p4) ∨ ((((p5 ∨ p2) ∧ (p1 ∨ p3)) → p4) → (p2 → p5))) → p1)))) ∨ True) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_167612588376481175488915678140 : (((((p1 → (p5 → (((p5 ∨ p5) → p3) ∨ (True ∧ p3)))) → p3) ∧ p5) → (True → p1)) → ((True → (p1 ∧ (False ∧ (True ∧ p2)))) → p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234420855190935084386552225145 : ((p2 → (True ∧ p3)) → ((p2 → ((((((p1 ∨ False) → p3) → p2) ∨ ((True → p5) ∨ p2)) ∧ (((p5 ∨ p5) ∧ p5) → p3)) → p3)) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h7 : p2 := by
      -- One of the premise coincides with the conclusion.
      exact h2
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h8 := h1 h7
    -- We need to get the right conjuct of h8 based on <expert-advice>.
    let h9 := h8.right
    -- One of the premise coincides with the conclusion.
    exact h9
  case inr h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h12 : p2 := by
        -- One of the premise coincides with the conclusion.
        exact h2
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h13 := h1 h12
      -- We need to get the right conjuct of h13 based on <expert-advice>.
      let h14 := h13.right
      -- One of the premise coincides with the conclusion.
      exact h14
    case inr h15 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h16 : p2 := by
        -- One of the premise coincides with the conclusion.
        exact h2
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h17 := h1 h16
      -- We need to get the right conjuct of h17 based on <expert-advice>.
      let h18 := h17.right
      -- One of the premise coincides with the conclusion.
      exact h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185953755649933182949832128976 : ((((p5 ∧ p3) → (False ∧ (((p1 ∧ False) → p5) → p1))) ∧ p3) → (((True → ((False ∨ p1) ∧ p4)) ∧ ((p3 → p4) → (True ∧ p1))) → p4)) := by
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
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h7 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h8 := h3 h7
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- One of the premise coincides with the conclusion.
  exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173238647417792839809931378949 : ((True → ((((p4 → p4) → (p3 → p1)) ∨ False) ∨ (((p5 ∨ True) ∧ p2) ∨ False))) ∨ ((p5 ∧ False) → (p1 ∨ (((False ∨ p2) ∨ p3) → False)))) := by
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
theorem thm_5_vars_588409706874061480951605093584 : ((((((p4 ∧ (p2 ∧ p4)) ∨ (((p5 → p5) → (p2 → (((p1 ∨ p1) ∧ (p1 ∧ ((True ∧ False) ∧ True))) ∨ p2))) ∧ False)) ∨ True) ∧ True) ∨ p1) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147094805743557487093289643919 : ((((p4 ∧ (p2 ∧ True)) ∧ (((((False ∨ (p5 ∧ ((p2 ∧ p1) ∧ p3))) ∧ p5) ∨ p2) → True) → p2)) ∧ p5) ∨ ((p1 ∨ (p5 ∧ True)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_629572920575899106265283729506 : (((((((((p2 ∨ ((p1 → p4) ∨ False)) ∧ (p4 ∧ ((p3 → False) ∨ (p1 ∨ True)))) ∨ p5) → p1) ∧ ((p2 ∧ p1) → p3)) ∨ True) → p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147526930952251169700990770942 : (((True → ((False → False) → ((True → (p5 ∧ True)) ∨ ((((p4 ∧ (True ∨ p4)) → p3) → p5) ∧ p1)))) ∨ True) ∨ (p4 ∨ (p5 ∨ (p5 ∧ p3)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150879297800626479001320113319 : (((((p5 ∨ (p5 ∨ p1)) ∨ p1) ∧ ((((False ∨ p4) ∧ False) ∨ (p4 → p5)) ∧ ((False ∧ p1) ∨ p5))) ∨ p4) → (False ∨ ((p4 → False) ∨ True))) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Conjunctions on the left can always be decomposed.
        let h7 := h4.left
        let h8 := h4.right
        -- Disjunctions on the left can always be decomposed.
        cases h7
        case inl h9 =>
          -- Conjunctions on the left can always be decomposed.
          let h10 := h9.left
          let h11 := h9.right
          -- Disjunctions on the left can always be decomposed.
          cases h10
          case inl h12 =>
            -- False on the left can always be used.
            apply False.elim h12
          case inr h13 =>
            -- False on the left can always be used.
            apply False.elim h11
        case inr h14 =>
          -- Disjunctions on the left can always be decomposed.
          cases h8
          case inl h15 =>
            -- Conjunctions on the left can always be decomposed.
            let h16 := h15.left
            let h17 := h15.right
            -- False on the left can always be used.
            apply False.elim h16
          case inr h18 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
      case inr h19 =>
        -- Disjunctions on the left can always be decomposed.
        cases h19
        case inl h20 =>
          -- Conjunctions on the left can always be decomposed.
          let h21 := h4.left
          let h22 := h4.right
          -- Disjunctions on the left can always be decomposed.
          cases h21
          case inl h23 =>
            -- Conjunctions on the left can always be decomposed.
            let h24 := h23.left
            let h25 := h23.right
            -- Disjunctions on the left can always be decomposed.
            cases h24
            case inl h26 =>
              -- False on the left can always be used.
              apply False.elim h26
            case inr h27 =>
              -- False on the left can always be used.
              apply False.elim h25
          case inr h28 =>
            -- Disjunctions on the left can always be decomposed.
            cases h22
            case inl h29 =>
              -- Conjunctions on the left can always be decomposed.
              let h30 := h29.left
              let h31 := h29.right
              -- False on the left can always be used.
              apply False.elim h30
            case inr h32 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- True on the right can always be proven directly.
              apply True.intro
        case inr h33 =>
          -- Conjunctions on the left can always be decomposed.
          let h34 := h4.left
          let h35 := h4.right
          -- Disjunctions on the left can always be decomposed.
          cases h34
          case inl h36 =>
            -- Conjunctions on the left can always be decomposed.
            let h37 := h36.left
            let h38 := h36.right
            -- Disjunctions on the left can always be decomposed.
            cases h37
            case inl h39 =>
              -- False on the left can always be used.
              apply False.elim h39
            case inr h40 =>
              -- False on the left can always be used.
              apply False.elim h38
          case inr h41 =>
            -- Disjunctions on the left can always be decomposed.
            cases h35
            case inl h42 =>
              -- Conjunctions on the left can always be decomposed.
              let h43 := h42.left
              let h44 := h42.right
              -- False on the left can always be used.
              apply False.elim h43
            case inr h45 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- True on the right can always be proven directly.
              apply True.intro
    case inr h46 =>
      -- Conjunctions on the left can always be decomposed.
      let h47 := h4.left
      let h48 := h4.right
      -- Disjunctions on the left can always be decomposed.
      cases h47
      case inl h49 =>
        -- Conjunctions on the left can always be decomposed.
        let h50 := h49.left
        let h51 := h49.right
        -- Disjunctions on the left can always be decomposed.
        cases h50
        case inl h52 =>
          -- False on the left can always be used.
          apply False.elim h52
        case inr h53 =>
          -- False on the left can always be used.
          apply False.elim h51
      case inr h54 =>
        -- Disjunctions on the left can always be decomposed.
        cases h48
        case inl h55 =>
          -- Conjunctions on the left can always be decomposed.
          let h56 := h55.left
          let h57 := h55.right
          -- False on the left can always be used.
          apply False.elim h56
        case inr h58 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
  case inr h59 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_261388475336292012700405653497 : ((p5 → p1) → (((p1 ∧ (p2 ∨ ((p3 → (True ∧ (p1 ∨ False))) ∧ (p2 ∧ (((p1 → p1) ∧ False) → False))))) ∧ (p1 → False)) → (p5 ∨ p5))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h7 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h8 : p1 := by
      -- One of the premise coincides with the conclusion.
      exact h5
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h9 := h4 h8
    -- False on the left can always be used.
    apply False.elim h9
  case inr h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- Conjunctions on the left can always be decomposed.
    let h13 := h12.left
    let h14 := h12.right
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h15 : p1 := by
      -- One of the premise coincides with the conclusion.
      exact h5
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h16 := h4 h15
    -- False on the left can always be used.
    apply False.elim h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185830544243689804418236371481 : ((((True ∧ ((p2 ∧ ((p4 ∨ p3) → p3)) ∨ p4)) ∧ True) ∧ p3) → ((True → ((p3 ∧ False) ∧ p1)) ∨ (p3 ∧ (True ∨ (False ∨ (True ∨ p1)))))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h3
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h11 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h3
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_86746421922162760430252526188 : (((p4 → ((p2 → (p4 → (p1 ∧ p5))) → p5)) ∧ ((True → p3) ∧ (((p3 ∧ (False ∨ True)) ∧ ((p2 ∨ p1) → (p2 ∨ p1))) ∨ p5))) → p3) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h7.left
    let h10 := h7.right
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- False on the left can always be used.
      apply False.elim h11
    case inr h12 =>
      -- One of the premise coincides with the conclusion.
      exact h9
  case inr h13 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h14 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h15 := h4 h14
    -- One of the premise coincides with the conclusion.
    exact h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149337314404286170784241107504 : (((False ∨ p4) → (p2 ∨ (((((p3 ∨ p4) ∧ p2) ∨ True) ∨ (p3 → p3)) → (p2 ∨ ((p3 ∨ True) ∧ p3))))) ∨ (p5 ∨ (True ∨ (p1 ∧ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_692549778889535187278153036968 : ((((((False ∧ p2) → (p5 ∨ (((p4 → p4) ∨ p3) → p3))) → (False ∧ p1)) ∧ ((False ∨ (False → (p1 ∨ (False → False)))) ∨ (p2 → False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159936361093292250189954721462 : ((((p2 → ((p2 ∧ ((p4 ∧ (p2 ∨ (p2 ∧ (p4 ∨ p2)))) ∧ p1)) ∧ (p3 ∧ True))) → p1) → p2) → ((((p5 ∧ p3) ∨ False) → False) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_18761884736867506733419133003 : ((((((p1 ∨ (p1 → False)) ∧ p5) ∨ (((p1 ∧ ((p4 ∨ p5) ∨ p2)) ∨ p2) → False)) ∨ p5) ∨ (((p5 ∧ (p1 ∧ p5)) → p1) ∨ True)) ∧ True) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_674585065363706274530077127978 : ((((True → (p5 ∧ (p2 ∧ (p2 → ((p1 ∨ (((p1 ∧ True) ∨ (p2 → (False → False))) → (True ∧ False))) ∧ p2))))) → ((p3 ∨ True) → p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_327106241540510284570396011949 : (True → (((p2 ∧ p2) ∨ (p2 ∨ (p1 ∧ (((True → True) → p1) ∨ (((p5 ∧ (True ∧ (p4 ∨ p2))) ∨ ((False → True) ∧ p5)) ∨ p5))))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_588762974597211059599468538401 : (((((p5 ∧ (((p2 ∨ (True ∧ False)) ∨ ((((p4 ∨ p4) ∨ p3) ∨ p5) ∨ (p1 ∧ ((p1 ∧ False) → (p2 ∧ p5))))) → False)) ∨ p5) ∧ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_77175285168405258059179459291 : ((((True ∨ (p3 ∨ p1)) ∧ ((p4 ∧ False) ∨ ((((p4 → ((p4 → (p1 ∨ p2)) ∨ False)) ∨ p1) ∨ ((p4 ∧ p2) → p2)) ∧ True))) → False) → p2) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((True ∨ (p3 ∨ p1)) ∧ ((p4 ∧ False) ∨ ((((p4 → ((p4 → (p1 ∨ p2)) ∨ False)) ∨ p1) ∨ ((p4 ∧ p2) → p2)) ∧ True))) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- One of the premise coincides with the conclusion.
    exact h5
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h2
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_696507877963526581060626428939 : (((((p2 ∧ (True ∧ (p1 ∧ (p3 → ((p5 ∨ p1) ∧ p1))))) ∧ False) ∧ (((p1 ∨ False) ∧ (((True → p3) → (True ∧ False)) → p3)) ∧ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197236451263166068492814212127 : ((((((p4 ∨ p5) → True) ∨ False) → p3) → False) ∨ ((((False ∨ (p5 → False)) ∧ (p1 ∨ p3)) ∨ ((p1 → p1) ∨ (p3 ∨ (p2 ∧ p5)))) ∨ p3)) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_708512179439081055815591028312 : (((((((p3 ∨ (True ∧ p3)) ∧ False) → p1) ∨ p3) → (((p2 → (True → (p1 ∨ (p3 ∧ ((False → (p3 → p2)) ∨ p5))))) → p3) ∨ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53323783884027524803499753917 : (((p4 → (((p1 → (p1 ∨ p3)) → ((False ∨ p5) ∧ p3)) → p2)) ∨ ((p3 ∨ (p3 ∨ (p1 → (p4 ∧ p5)))) ∧ (p3 ∨ (p2 → p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135088381634986647901542598992 : ((((p1 ∧ (p2 → ((True → p2) ∧ (p3 → (p1 → (p2 ∧ p1)))))) → ((p5 ∨ (True → p3)) ∨ p1)) ∨ (p4 ∧ p5)) ∨ (True → (p2 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184056614666811226242065380306 : (((((p2 ∧ True) → ((p5 → p2) → p5)) ∨ (p5 ∧ True)) ∨ p3) ∨ ((p3 ∧ p2) → ((p3 ∨ p1) → (((True ∧ (p2 ∨ p5)) ∨ True) ∨ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h1.left
    let h5 := h1.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h1.left
    let h8 := h1.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_743142811257369617828065712667 : ((((p4 → p2) ∨ (p4 → ((((p4 → (p1 ∨ p3)) ∨ True) ∧ (p5 → p3)) ∧ ((False → p4) → ((p1 ∨ p5) ∧ (False → (p3 ∨ p5))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_618898135771291129449208898924 : (((((p1 → (p1 → p3)) ∧ (p3 → (((p1 ∧ p4) ∧ (((((p5 ∧ False) → True) ∧ False) ∧ p5) ∨ (p4 ∧ (p2 ∧ p1)))) ∧ p1))) ∨ True) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_215680598137782810617628474368 : ((False ∨ ((False ∧ p4) ∧ True)) ∨ (p3 ∨ (p2 ∨ (True ∧ ((p4 ∨ (p1 ∨ ((p4 ∧ p3) → (p4 ∧ ((p5 → (p5 ∨ p2)) ∧ p2))))) ∨ True))))) := by
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
theorem thm_5_vars_39385688387163673849259103740 : (((p3 ∧ (p1 ∨ ((((p2 → ((((p5 ∨ False) → True) ∧ ((p2 ∨ p4) → (p1 ∨ (p3 ∧ p3)))) → p2)) ∧ True) ∧ p3) → p1))) ∧ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110979687475382271244484132322 : (((((((True → (((False ∨ p4) ∧ (True → False)) → p5)) ∧ (False ∧ p5)) ∨ p2) → ((p5 → False) → p2)) → (p2 ∨ p2)) ∧ p2) ∨ (p2 → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_87791881893185134147380888702 : ((((p5 → ((p2 ∧ p2) ∨ True)) ∨ p5) → ((True ∧ (p4 → (p4 ∨ ((((p4 ∧ p4) ∧ p3) ∨ (p3 → (p2 → p5))) ∨ True)))) ∧ False)) → p4) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p5 → ((p2 ∧ p2) ∨ True)) ∨ p5) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
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
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322321242724917991257702245645 : (p5 ∨ ((((p3 ∨ (p5 ∨ False)) ∨ ((True → p4) ∨ (p4 → (p2 ∨ ((p4 ∨ p4) → (p1 ∨ (False ∨ (p1 ∨ True)))))))) ∧ (True ∨ True)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_698942018682986184980569680215 : ((((p4 ∧ (((p2 ∧ p1) → False) → (p3 ∨ ((p4 ∧ True) ∨ p3)))) ∨ (p3 → (((False ∧ p1) → False) ∧ (((p3 ∧ p3) ∨ p1) ∨ p4)))) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192924533998062557898032364589 : ((((((True ∧ p3) ∧ p3) ∨ True) → p2) ∨ (p2 ∧ True)) → ((((p1 ∨ (False → p4)) ∧ p4) ∨ (p4 → p4)) ∨ (p5 ∨ (p3 → (p4 ∧ False))))) := by
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
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227751814738376251105265950638 : ((p1 ∧ (p3 ∨ p3)) ∨ (((True ∧ p1) ∨ ((((p1 → True) ∨ (p5 → p2)) → p5) ∨ ((False → (True ∨ p5)) ∧ (p5 ∨ (False → p4))))) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149823075629269736026803978964 : ((p1 ∨ ((((p1 ∨ p2) ∧ ((False → p3) ∨ p4)) ∧ (p4 ∧ (((False ∨ p3) → False) ∧ (p3 ∨ False)))) → False)) ∨ (((p3 ∨ p4) ∧ p3) ∨ False)) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h3.left
      let h9 := h3.right
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
        have h13 : (False ∨ p3) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h12
        -- We have shown the premise of h10, we can now drive its conclusion.
        let h14 := h10 h13
        -- False on the left can always be used.
        apply False.elim h14
      case inr h15 =>
        -- False on the left can always be used.
        apply False.elim h15
    case inr h16 =>
      -- Conjunctions on the left can always be decomposed.
      let h17 := h3.left
      let h18 := h3.right
      -- Conjunctions on the left can always be decomposed.
      let h19 := h18.left
      let h20 := h18.right
      -- Disjunctions on the left can always be decomposed.
      cases h20
      case inl h21 =>
        -- We want to use the implication h19 based on <expert-advice>. So we show its premise.
        have h22 : (False ∨ p3) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h21
        -- We have shown the premise of h19, we can now drive its conclusion.
        let h23 := h19 h22
        -- False on the left can always be used.
        apply False.elim h23
      case inr h24 =>
        -- False on the left can always be used.
        apply False.elim h24
  case inr h25 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h26 =>
      -- Conjunctions on the left can always be decomposed.
      let h27 := h3.left
      let h28 := h3.right
      -- Conjunctions on the left can always be decomposed.
      let h29 := h28.left
      let h30 := h28.right
      -- Disjunctions on the left can always be decomposed.
      cases h30
      case inl h31 =>
        -- We want to use the implication h29 based on <expert-advice>. So we show its premise.
        have h32 : (False ∨ p3) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h31
        -- We have shown the premise of h29, we can now drive its conclusion.
        let h33 := h29 h32
        -- False on the left can always be used.
        apply False.elim h33
      case inr h34 =>
        -- False on the left can always be used.
        apply False.elim h34
    case inr h35 =>
      -- Conjunctions on the left can always be decomposed.
      let h36 := h3.left
      let h37 := h3.right
      -- Conjunctions on the left can always be decomposed.
      let h38 := h37.left
      let h39 := h37.right
      -- Disjunctions on the left can always be decomposed.
      cases h39
      case inl h40 =>
        -- We want to use the implication h38 based on <expert-advice>. So we show its premise.
        have h41 : (False ∨ p3) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h40
        -- We have shown the premise of h38, we can now drive its conclusion.
        let h42 := h38 h41
        -- False on the left can always be used.
        apply False.elim h42
      case inr h43 =>
        -- False on the left can always be used.
        apply False.elim h43



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_761485090327164356436968019139 : (((p3 ∧ ((p1 → ((p2 → ((p4 → ((True ∨ True) → (True → ((p5 ∧ (p4 → True)) → True)))) ∨ p2)) → (p3 → (p4 ∧ p3)))) ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41748319704031594505688154344 : ((((((p5 → True) → p4) ∧ p5) ∨ ((p3 ∧ (False ∨ ((p3 ∨ (p2 ∧ p2)) ∧ (p4 ∨ True)))) ∨ (False → ((p3 ∧ p5) → p3)))) ∨ False) ∨ p4) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55923714736521634134380551079 : (((False → (p2 ∧ (p1 → False))) ∧ (p2 ∧ ((p4 ∧ p5) ∨ ((((p4 ∨ (p5 ∧ p5)) ∨ p5) ∨ False) ∧ (True → ((True ∨ p5) → True)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42893763239684323100627408920 : (((p3 → (((p4 ∨ ((False ∧ False) → ((p2 ∨ p5) ∨ p3))) ∧ (p4 ∧ ((p4 ∧ (p2 ∧ p5)) ∧ p4))) ∧ ((p2 → p5) ∨ p5))) ∨ True) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_778751635238813135799236602867 : (((p1 ∨ (p4 ∨ ((True ∧ (p3 → p3)) → (((False ∨ ((p3 → (True → p5)) ∧ ((p2 → True) ∨ p4))) → (p1 ∧ p2)) ∨ (True ∧ p5))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_306196393114540306885906723562 : (p1 ∨ ((True → (p5 ∨ p3)) ∨ ((p2 ∨ ((((p3 → (p2 ∨ ((p5 ∧ p2) → p5))) → ((True ∨ False) ∧ True)) → False) → p5)) ∨ (False ∧ True)))) := by
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
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p3 → (p2 ∨ ((p5 ∧ p2) → p5))) → ((True ∨ False) ∧ True)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61344591632155452279793139971 : ((p1 ∧ ((((p4 ∨ (((False ∨ False) → (((p4 ∨ False) ∨ True) ∨ p2)) ∧ True)) → ((p1 ∨ False) ∨ p2)) ∧ ((p1 ∧ p1) ∧ p3)) ∧ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53566878717868462765261510466 : ((((((p4 ∨ True) ∧ p5) ∨ ((p5 ∧ p1) ∨ p3)) ∨ p3) ∧ ((p5 ∨ True) ∧ ((p4 → (p5 ∨ p2)) ∨ (p1 ∧ ((p4 → p4) ∧ False))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_195520593222590373164236797162 : ((((p4 ∧ p1) ∨ p4) → ((False ∧ True) ∨ p4)) ∧ (p3 ∨ ((((False ∧ p5) → p3) ∧ (False ∨ p2)) ∨ ((((p3 ∨ p5) → p5) → p2) ∨ True)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_83244043681710242764769318464 : ((((((p1 → p2) → (((((p2 → p4) ∧ p5) ∧ p4) → p4) → p4)) → (True ∨ p5)) → False) ∧ (p1 ∨ (p4 ∧ (False → (True ∧ True))))) → p5) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h5 : (((p1 → p2) → (((((p2 → p4) ∧ p5) ∧ p4) → p4) → p4)) → (True ∨ p5)) := by
      -- Implications on the right can always be decomposed.
      intro h6
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h7 := h2 h5
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h11 : (((p1 → p2) → (((((p2 → p4) ∧ p5) ∧ p4) → p4) → p4)) → (True ∨ p5)) := by
      -- Implications on the right can always be decomposed.
      intro h12
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h13 := h2 h11
    -- False on the left can always be used.
    apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64547612434988888800474460360 : ((p1 ∨ ((p1 → (False ∧ (True → (p2 ∨ p1)))) → ((((p5 ∨ p3) ∨ ((p5 → False) ∨ True)) ∨ (p1 → (p4 ∨ False))) → (p2 ∨ True)))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h10 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



