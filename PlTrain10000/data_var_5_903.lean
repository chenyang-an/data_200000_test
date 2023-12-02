variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_601251751464901666153884350183 : ((((p2 ∧ (((p1 ∨ (False → p2)) ∨ ((((((False → p1) ∨ True) ∧ ((False ∧ p3) → p3)) ∧ p3) → p1) → p1)) → (p2 ∧ p3))) ∧ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225765395386654416476520135832 : (((p5 → False) ∧ p1) ∨ (((False ∨ (((((p3 ∧ p2) ∧ ((False → p2) → p5)) ∨ (p2 ∨ (p2 → p1))) ∨ p5) → p3)) → p4) → (p4 → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200583159662077876517166074700 : ((True ∧ (((p2 ∧ False) ∨ p2) ∧ (False → p4))) → ((p3 ∨ (True → ((p3 ∨ p5) → p1))) ∨ ((p5 → p2) ∧ (((True ∨ p2) → p3) → True)))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h10
    -- One of the premise coincides with the conclusion.
    exact h9
    -- Implications on the right can always be decomposed.
    intro h11
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_162859380347793894765436752705 : ((((((True ∧ (p1 ∨ p5)) ∧ p2) ∨ (p4 → (True ∨ p4))) → (p4 ∧ True)) ∨ (p1 ∨ True)) ∧ (((p1 ∨ p5) ∧ (False → p5)) → (True ∨ p3))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h2
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164941381099637484865120685260 : (((((p1 ∨ (((p2 ∧ (p2 ∧ (True ∧ True))) ∧ p5) ∨ (p5 ∨ True))) ∧ p1) → p2) → False) ∨ (True → ((p4 → p3) → (False ∨ (p4 → p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118911115183434206811593084009 : ((True → (p3 → (p4 ∧ ((p3 ∨ ((p4 ∨ (False ∧ True)) ∧ ((p1 ∧ (True → (((p3 → p1) ∧ p5) → p5))) → p3))) → p1)))) ∨ (False → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172098997456509130619167157009 : (((True ∨ ((p5 → (p3 ∨ p5)) → (p1 ∧ ((p4 → p1) ∧ p4)))) → (True ∧ p4)) ∨ (False → ((p2 ∨ p4) ∨ ((True ∧ p2) ∨ (True → p1))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204731124600305928845774970220 : (((p2 → ((True ∨ p5) ∧ p1)) ∨ p5) ∨ ((p2 ∧ (((p2 ∨ ((p3 ∨ p4) ∨ p5)) ∨ (True ∨ p2)) ∨ ((True ∧ (p1 ∧ p3)) ∧ p2))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_819296158022901212976113786456 : (((((((True ∧ (p3 ∨ True)) ∨ ((p3 ∨ p5) ∨ (((True ∨ p5) ∧ p3) ∨ (True → (p2 → False))))) → p5) ∧ (p5 → (p4 ∨ p4))) ∧ True) → p4) ∧ True) := by
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
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h6 : ((True ∧ (p3 ∨ True)) ∨ ((p3 ∨ p5) ∨ (((True ∨ p5) ∧ p3) ∨ (True → (p2 → False))))) := by
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
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h7 := h4 h6
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h8 : p5 := by
    -- One of the premise coincides with the conclusion.
    exact h7
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h9 := h5 h8
  -- Disjunctions on the left can always be decomposed.
  cases h9
  case inl h10 =>
    -- One of the premise coincides with the conclusion.
    exact h10
  case inr h11 =>
    -- One of the premise coincides with the conclusion.
    exact h11
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38594420745274991722407844163 : ((((p5 ∨ ((False ∧ (p1 → True)) ∨ ((False ∨ p2) ∧ p1))) → (((p1 ∨ ((False ∨ (p2 ∧ p5)) ∨ p5)) ∧ p1) → (False ∧ True))) ∧ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191109659788131817706869598313 : (((p3 ∧ (p2 ∨ p5)) ∧ ((p1 ∨ p1) ∧ (p1 ∧ p5))) ∨ (((p5 → p1) → True) ∨ (((p1 ∨ p3) → (((p1 ∨ p3) ∨ True) → p1)) ∧ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41482622108743911257423631837 : ((((False ∧ (p2 ∧ (((p2 → p4) ∨ (p3 → p4)) → (p5 ∨ p1)))) ∨ (True → ((True ∧ (p4 ∧ (p3 → p4))) ∨ (True ∨ p1)))) ∨ p5) ∨ p4) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322336207337556268291727635913 : (p5 ∨ (((p4 → ((p4 ∧ (((p5 ∧ p5) ∧ False) ∨ (((p2 ∨ (((False ∨ p3) → p4) ∨ p3)) ∨ p3) ∧ p1))) ∨ p3)) ∨ (p2 ∨ True)) ∨ p2)) := by
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
theorem thm_5_vars_8211939651913682829395705426 : ((((((((((((((p1 → True) → (p4 ∨ p2)) → p2) ∨ p5) ∨ p1) → p4) ∧ p1) ∧ (p2 → p2)) → False) ∧ p4) ∧ True) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112220120217784372796571309797 : (((p1 ∨ ((False ∧ ((p4 ∨ p3) ∨ ((((((False ∧ p1) ∨ (False ∨ p1)) ∨ p4) ∨ p5) ∨ p4) ∨ p5))) ∧ (False → False))) ∨ p3) ∨ (p2 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197243260601247015056339952776 : (((((p2 ∧ False) ∧ (False ∧ p1)) → p1) → p2) ∨ ((p1 ∧ (True ∨ p3)) → (False → ((p4 ∨ (((p1 → (p1 ∧ True)) → p1) → p2)) → p2)))) := by
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
theorem thm_5_vars_312995330996419036765355373020 : (p3 ∨ (((((p3 → (((p3 ∨ p4) → True) → True)) → (p2 ∧ (True ∧ (((p4 → (p3 ∧ (p5 ∨ p1))) ∨ False) ∨ False)))) ∨ p3) ∨ False) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158014702811636519927930533479 : (((((p3 → p1) ∧ (p2 ∨ p2)) → p1) ∧ (((p2 ∨ (False → p5)) → (False ∧ p5)) ∨ (False ∧ False))) ∨ (((p5 ∨ p2) → (p3 ∨ True)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65212731326445283158948422974 : ((p3 ∨ (((p4 → (((p1 ∨ (p2 → p2)) ∧ p1) ∨ (False ∨ ((p2 ∨ False) ∧ (False → True))))) → (p3 ∨ (True ∧ (p3 ∧ True)))) ∨ True)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41447497016289854871214933547 : ((((((p3 ∧ (p2 ∨ (p2 ∧ p4))) ∧ ((p5 ∧ p4) ∨ p1)) ∧ True) ∧ (((p3 ∨ (p3 → (False → p4))) ∨ p4) ∨ (p2 → p3))) ∨ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192949511560297735225523472992 : ((((False → p5) ∨ (p5 ∨ (p1 → p5))) ∨ (False ∨ p4)) → ((p2 → (((p1 ∧ ((p3 ∨ True) ∧ (True ∨ (p3 ∨ True)))) → False) ∨ p2)) ∨ p3)) := by
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
      -- Implications on the right can always be decomposed.
      intro h4
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h7
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h7
      case inr h8 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h9
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h9
  case inr h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- False on the left can always be used.
      apply False.elim h11
    case inr h12 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h13
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_555984615976738350197640641923 : (((p3 ∨ (((True → p4) ∧ ((((p1 ∧ p3) ∨ p5) → (p2 → (p3 → (((p2 → p3) ∧ p3) ∧ p4)))) → (p1 ∨ (p5 ∨ p1)))) ∨ True)) ∧ True) ∧ True) := by
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
theorem thm_5_vars_695036308199432547051019097131 : (((((p1 ∧ ((p3 ∨ ((p4 ∧ p4) ∧ p4)) ∧ (False → (p5 → False)))) ∧ p2) → (False ∨ (p1 → (p5 ∨ ((p5 ∧ True) ∧ (p3 → p2)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_352271938867376847498711607325 : (p4 → ((((p3 ∨ False) ∨ False) → p3) → ((((p2 → p1) ∧ (p1 ∧ True)) ∧ True) ∨ (p2 → (((p3 ∨ p2) ∧ (p3 → (True ∧ p4))) ∨ p4))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_708937552684029834400508681219 : (((((p4 ∨ (p3 ∧ (p3 → p4))) ∨ (p5 ∨ False)) → ((p3 ∧ True) ∧ (((p2 ∨ (p2 → ((p2 ∧ p1) → p3))) ∨ p3) ∨ (False ∧ p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303880732246071653485551635683 : (p1 ∨ (((((((p1 ∨ p5) → False) ∧ p5) ∨ p1) ∨ ((True ∧ (p4 ∧ p5)) ∧ ((p1 ∧ p2) ∧ p2))) ∨ (((p2 → p1) ∧ p4) → True)) ∨ p2)) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337815888858792034561723024759 : (p1 → ((p1 → (((p2 ∨ True) → ((((p1 ∨ p5) ∨ False) ∨ p2) ∨ p2)) ∧ (p5 → False))) → (((p1 ∧ p5) → ((p4 ∨ False) ∧ p4)) ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h6 : p1 := by
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h7 := h2 h6
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
  have h9 : p5 := by
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h8, we can now drive its conclusion.
  let h10 := h8 h9
  -- False on the left can always be used.
  apply False.elim h10
  -- Conjunctions on the left can always be decomposed.
  let h11 := h3.left
  let h12 := h3.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h13 : p1 := by
    -- One of the premise coincides with the conclusion.
    exact h11
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h14 := h2 h13
  -- We need to get the right conjuct of h14 based on <expert-advice>.
  let h15 := h14.right
  -- We want to use the implication h15 based on <expert-advice>. So we show its premise.
  have h16 : p5 := by
    -- One of the premise coincides with the conclusion.
    exact h12
  -- We have shown the premise of h15, we can now drive its conclusion.
  let h17 := h15 h16
  -- False on the left can always be used.
  apply False.elim h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_610913224976909774261783540344 : ((((((False → (p3 ∧ (True ∨ (p2 ∧ (p3 → ((p4 ∨ False) ∨ p1)))))) → ((True ∧ (p3 → ((False → False) ∨ p2))) → p5)) → False) ∨ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206404966680284263262507355881 : ((p3 ∨ ((p2 ∨ p5) ∨ (p3 → p5))) ∨ (((p1 ∨ True) ∨ (((p2 → (True ∨ (p1 ∨ p2))) ∨ p5) ∨ ((p3 → (False ∨ p4)) ∧ p1))) ∨ p3)) := by
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
theorem thm_5_vars_76825099891050577432128090074 : ((((p4 → ((((True → (p5 ∧ p1)) → p3) → (p3 → p5)) → p3)) ∨ (False ∨ ((((p1 → p3) ∨ (p1 ∨ p4)) ∧ p3) → p3))) → False) → p4) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p4 → ((((True → (p5 ∧ p1)) → p3) → (p3 → p5)) → p3)) ∨ (False ∨ ((((p1 → p3) ∨ (p1 ∨ p4)) ∧ p3) → p3))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
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
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- One of the premise coincides with the conclusion.
        exact h5
      case inr h9 =>
        -- One of the premise coincides with the conclusion.
        exact h5
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h10 := h1 h2
  -- False on the left can always be used.
  apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1952093743403699853164637699 : (((p2 → (False ∧ (((False ∧ ((((True → False) ∨ p4) → p4) → False)) ∨ p3) ∧ p3))) ∨ (p5 ∨ True)) ∨ (p5 ∧ (p1 ∨ (p2 → p2)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342397259661691659424722079099 : (p2 → (((p1 ∧ p2) ∨ (((p2 → p1) → (p2 ∧ ((p3 → True) → (p2 ∧ p4)))) ∧ p3)) ∨ (p5 ∨ ((False ∧ p3) → ((p3 ∨ p2) ∧ False))))) := by
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
  apply False.elim h3
  -- Conjunctions on the left can always be decomposed.
  let h5 := h2.left
  let h6 := h2.right
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_196652062336367952295847861651 : (((((p1 ∨ (p3 ∧ False)) ∨ p4) ∧ p5) ∧ p2) ∨ (((p2 ∨ True) ∧ ((p1 ∨ p1) → ((p3 ∧ p5) → p3))) ∨ ((p1 ∧ p2) ∧ (p5 → p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  cases h1
  case inl h5 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h6 =>
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_721838786988612484067816564506 : ((((p3 ∨ (False ∨ (True → False))) → ((p5 ∧ (((p5 ∧ p4) ∨ (((p4 ∨ True) → p2) → (p4 ∨ ((p3 ∧ p3) ∧ True)))) ∨ p3)) ∨ p3)) ∨ p1) ∧ True) := by
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
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- False on the left can always be used.
      apply False.elim h4
    case inr h5 =>
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h6 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h7 := h5 h6
      -- False on the left can always be used.
      apply False.elim h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_611626066845984745035122966898 : (((((p2 ∨ ((((((p2 → p4) → True) → (p5 ∨ (False ∨ (p1 ∧ p4)))) ∨ p2) ∨ ((p3 ∨ p1) ∧ True)) ∧ (p1 ∨ True))) → p1) ∨ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193518324778027655547476407173 : (((p1 → p5) ∨ (p4 ∨ (((False ∨ p4) → p3) → p2))) → (((((p3 ∧ False) → p2) → p2) ∧ p4) → ((p1 ∧ (p5 → p4)) ∨ (p5 → p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h7 : ((p3 ∧ False) → p2) := by
      -- Implications on the right can always be decomposed.
      intro h8
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- False on the left can always be used.
      apply False.elim h10
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h11 := h3 h7
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
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h15 : ((p3 ∧ False) → p2) := by
        -- Implications on the right can always be decomposed.
        intro h16
        -- Conjunctions on the left can always be decomposed.
        let h17 := h16.left
        let h18 := h16.right
        -- False on the left can always be used.
        apply False.elim h18
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h19 := h3 h15
      -- One of the premise coincides with the conclusion.
      exact h19
    case inr h20 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h21
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h22 : ((p3 ∧ False) → p2) := by
        -- Implications on the right can always be decomposed.
        intro h23
        -- Conjunctions on the left can always be decomposed.
        let h24 := h23.left
        let h25 := h23.right
        -- False on the left can always be used.
        apply False.elim h25
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h26 := h3 h22
      -- One of the premise coincides with the conclusion.
      exact h26



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323440102561392351917665435348 : (p5 ∨ ((((p4 ∨ False) ∨ True) ∧ ((((p5 ∨ p2) ∨ p3) ∧ p4) ∨ (p2 → (p2 ∧ (((p5 ∧ p1) ∧ p2) → p2))))) ∧ (p2 → (p1 ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h7
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_264427305309776512448057716224 : (True ∧ ((((True ∧ p5) ∨ p2) ∨ p2) → (p4 ∨ (p4 ∨ (((((p4 ∧ p5) ∨ False) → p5) ∨ ((((True ∨ p1) ∨ True) ∨ p5) ∨ p4)) ∧ True))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h3 =>
      -- Conjunctions on the left can always be decomposed.
      let h4 := h3.left
      let h5 := h3.right
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h6 =>
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h7 =>
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246701016149727121263517821928 : ((p5 ∧ p4) ∨ ((((p5 ∨ (p4 ∨ p1)) ∨ (True ∨ ((True → True) → True))) → p1) ∨ ((p5 ∧ False) ∨ ((True → ((p5 ∧ True) → p2)) → True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_694485254210802041852719359519 : (((((p4 → p3) → ((p2 ∧ (True → (False → (True → p3)))) → (p4 ∨ p4))) ∨ ((((p1 → p5) ∧ False) ∧ (True ∨ False)) → (p1 ∧ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_16892858927205802467583835486 : (((False ∧ (((((p3 ∨ ((False ∨ (p2 ∨ (False ∨ (p3 ∧ (p1 ∧ p5))))) ∧ p1)) → p2) ∨ True) ∧ False) ∧ p3)) ∨ (True ∨ (p2 → p1))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_701595932751768716445965279273 : (((((p5 → True) ∧ ((p5 ∨ p2) → ((p4 ∨ False) → p3))) ∧ (False ∧ ((((p3 ∧ p4) ∨ (False ∧ p1)) ∧ p1) ∨ ((p5 ∨ False) ∨ p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40931116451695539488562865449 : (((((p4 ∧ ((False ∧ (((p5 → (p4 → ((p2 → False) → (p5 → (p1 ∨ p1))))) → False) ∨ p3)) ∧ p2)) ∧ p3) ∨ (p3 ∨ p5)) ∨ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55409172181084103859041216701 : ((((((False ∨ p4) ∨ p5) → p5) ∨ p3) → (((((((p2 ∧ p5) ∨ p2) ∨ False) → (False ∧ (p3 ∨ False))) ∨ (True ∧ True)) ∧ p4) → p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_776594234585397937999172714216 : (((p1 ∨ ((p3 ∧ (((((False ∨ (p4 ∨ True)) → ((True → False) ∨ p2)) ∧ ((p2 ∧ ((p3 ∧ False) → p5)) → p4)) → p3) ∨ p2)) ∨ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338167409913836073976048589267 : (p1 → (((p3 → (p3 → p2)) ∨ ((p2 ∨ p2) → True)) → (((p3 → p2) → False) ∨ (((p1 ∨ True) → (p4 → ((False → False) ∨ p2))) ∧ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h7
      -- False on the left can always be used.
      apply False.elim h7
    case inr h8 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h9
      -- False on the left can always be used.
      apply False.elim h9
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h10 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h11
    -- Implications on the right can always be decomposed.
    intro h12
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h13 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h14
      -- False on the left can always be used.
      apply False.elim h14
    case inr h15 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h16
      -- False on the left can always be used.
      apply False.elim h16
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_709986521969890775431645928748 : ((((((p3 ∧ p1) ∨ (p3 → p5)) ∧ p3) ∧ (p3 ∧ ((((((p3 ∧ (p1 → True)) → p5) ∨ p4) ∧ p4) ∨ (p1 ∧ (p4 ∧ True))) ∧ True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181299343646913165849565651673 : ((p5 ∧ ((True → p1) ∧ (False ∨ (p3 ∨ ((True → (p3 ∧ p1)) ∨ True))))) → ((((p2 → p2) → (((p2 ∨ p2) → p3) ∨ p4)) ∨ p2) ∨ p5)) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
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
theorem thm_5_vars_755434102295564925635532931423 : (((p1 ∧ ((((True ∨ (p5 → True)) → p4) ∨ ((p2 → (True ∧ ((p3 ∧ (((False → p5) → (False ∨ p1)) ∨ p2)) ∨ False))) ∨ p5)) ∧ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232663223223662509649231298111 : ((p1 ∧ (p2 ∧ True)) → ((p3 ∨ ((p1 ∧ p4) ∧ ((p4 ∧ (((False → ((p1 ∧ False) ∨ True)) ∧ (p4 ∧ p1)) ∨ p4)) ∧ (p3 ∨ p3)))) ∨ p1)) := by
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
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_262190188884738393923763711172 : (True ∧ ((((p5 → (False → (p1 ∧ (((((p2 → False) ∧ (False → (p4 ∧ p3))) ∨ True) ∨ p5) → True)))) ∧ (p5 → (p4 → p4))) → p2) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_799576285417949346272148408946 : (((p1 → (p4 ∨ (((True ∨ (((p3 ∧ (p5 ∧ p4)) ∨ p3) ∨ p2)) → False) ∧ (((((True → p5) ∨ True) ∧ False) → (p5 ∧ p2)) → p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301251438948128365121686241603 : (False ∨ ((((p1 ∨ p3) ∧ False) ∨ (p4 ∧ p1)) ∨ (((p3 → ((p1 → (p4 ∨ (p2 ∧ (p2 ∨ (True ∧ (p3 → True)))))) → p5)) ∨ False) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_316508626526631729378301896744 : (p3 ∨ (p2 ∨ (((p2 → False) ∧ ((((True ∨ p4) → p3) → p5) → (p5 ∨ (p3 ∨ p1)))) ∨ ((((p5 ∨ (p5 ∨ p1)) → p4) ∨ True) ∨ p2)))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_797331252607509916578705288194 : (((p1 → (((p1 → ((p4 → (True ∧ p1)) → (((p5 ∧ ((p4 ∧ p2) ∧ p1)) ∧ False) ∧ p5))) → ((False ∧ p1) ∧ (p4 ∨ p4))) ∨ p2)) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : p1 := by
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h5 : (p4 → (True ∧ p1)) := by
    -- Implications on the right can always be decomposed.
    intro h6
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h7 := h4 h5
  -- We need to get the left conjuct of h7 based on <expert-advice>.
  let h8 := h7.left
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- False on the left can always be used.
  apply False.elim h9
  -- One of the premise coincides with the conclusion.
  exact h1
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h10 : p1 := by
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h11 := h2 h10
  -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
  have h12 : (p4 → (True ∧ p1)) := by
    -- Implications on the right can always be decomposed.
    intro h13
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h11, we can now drive its conclusion.
  let h14 := h11 h12
  -- We need to get the left conjuct of h14 based on <expert-advice>.
  let h15 := h14.left
  -- We need to get the right conjuct of h15 based on <expert-advice>.
  let h16 := h15.right
  -- False on the left can always be used.
  apply False.elim h16
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114651082560177502219264464115 : (((((p4 → True) ∨ ((p5 ∧ (p4 ∧ False)) → (True ∨ p2))) → ((False ∨ p5) → p1)) ∨ ((p3 → (p2 ∧ (p2 → True))) ∧ p2)) ∨ (p3 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39046847770911472981154525335 : ((((False ∧ p3) ∨ ((False ∧ ((p2 ∧ p1) ∧ False)) ∧ ((p4 ∨ (((p5 ∨ (p5 ∨ p1)) ∧ (p5 → (p3 → False))) ∧ p4)) ∧ False))) ∧ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_752117263699850991813844058260 : (((True ∧ (p1 → (((p2 ∧ ((p2 ∧ p4) ∨ ((((p1 ∨ p4) → (p1 ∧ p4)) → False) ∨ p1))) ∧ (True ∨ False)) ∨ ((p2 → p4) → True)))) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_339723534210573893081619073235 : (p1 → (p4 ∨ (((p5 → (((p4 ∨ p5) ∨ (False ∨ p1)) ∧ (p4 ∨ ((p3 ∨ ((p2 ∧ p4) ∧ (p5 ∨ p1))) ∧ (p5 ∧ p4))))) ∨ p2) ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40537325176529555496690370992 : ((((p3 ∨ ((p2 ∨ (p3 ∧ (p2 ∧ (((p5 ∨ p5) → False) ∨ (((p5 ∨ p4) ∨ (p3 ∧ p1)) ∧ False))))) → (p3 ∧ p1))) ∨ p5) ∨ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_704653849311423425091007105069 : ((((True ∧ ((p3 ∨ (p4 → False)) ∨ (False → (False → p3)))) → ((p1 ∧ p1) → ((((False → p1) ∧ ((p1 → False) ∧ p4)) → False) ∧ True))) ∨ False) ∧ True) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h2.left
  let h9 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h10 := h1.left
  let h11 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h11
  case inl h12 =>
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h13 =>
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h14 : p1 := by
        -- One of the premise coincides with the conclusion.
        exact h9
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h15 := h6 h14
      -- False on the left can always be used.
      apply False.elim h15
    case inr h16 =>
      -- We want to use the implication h16 based on <expert-advice>. So we show its premise.
      have h17 : p4 := by
        -- One of the premise coincides with the conclusion.
        exact h7
      -- We have shown the premise of h16, we can now drive its conclusion.
      let h18 := h16 h17
      -- False on the left can always be used.
      apply False.elim h18
  case inr h19 =>
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h20 : p1 := by
      -- One of the premise coincides with the conclusion.
      exact h9
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h21 := h6 h20
    -- False on the left can always be used.
    apply False.elim h21
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299739695620594128779712684585 : (False ∨ (((True ∧ (True → ((p1 ∨ False) ∧ p5))) ∧ (((p1 ∧ (((p3 ∨ p1) ∨ False) ∧ (p1 ∧ (p2 ∨ p2)))) ∨ (p1 ∧ p5)) → p2)) → p5)) := by
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
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h6 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h7 := h5 h6
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_69053428961421688985478367965 : ((p5 → ((p5 ∧ (False ∨ ((((True → ((p5 ∨ p1) ∧ p1)) ∧ ((p4 ∧ (p1 ∨ (p3 → (p2 ∨ p2)))) ∧ p5)) ∧ p1) ∧ p2))) ∨ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165221565431538516875853083328 : (((((p5 ∧ ((p1 → p4) ∧ True)) ∨ False) → ((p4 → p5) ∧ (p2 ∧ False))) ∨ (p5 ∧ p5)) ∨ ((False ∨ (p3 ∧ (p3 → (p2 ∨ p2)))) → p3)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_130197209692267403743937327434 : (((p4 → (((((p5 → p5) → p2) ∨ (p1 → (p5 ∨ (p2 ∧ p2)))) → ((p4 → p2) → p1)) ∧ False)) ∨ (False → True)) ∧ ((p2 → False) → True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160565841180608875049650991728 : ((((((p2 → p2) → p2) ∨ (p3 → False)) ∨ ((p4 ∨ True) ∨ p4)) → (((p4 ∧ p3) ∧ False) ∧ False)) → (p2 ∨ (True ∧ ((p3 → p2) ∨ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((((p2 → p2) → p2) ∨ (p3 → False)) ∨ ((p4 ∨ True) ∨ p4)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159865697267833289119739731038 : (((((((p5 ∧ p5) ∨ (p1 ∧ True)) ∨ (p2 ∧ (p1 ∧ ((p1 → p2) ∧ p1)))) ∨ p2) ∧ p2) → p3) → ((p4 ∧ (p2 ∧ (p4 → p1))) → p1)) := by
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
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h7 : p4 := by
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h8 := h6 h7
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258758312195627308889485372979 : ((True → False) → (((p5 ∨ (p1 ∨ ((p4 ∧ (((False → (p5 → p2)) ∧ ((p2 ∧ p4) ∧ p4)) → (p4 ∨ p5))) ∧ p4))) ∧ (p5 ∧ p2)) ∧ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h4
  -- False on the left can always be used.
  apply False.elim h5
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h6 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h7 := h1 h6
  -- False on the left can always be used.
  apply False.elim h7
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h8 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h9 := h1 h8
  -- False on the left can always be used.
  apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198272944612761567091840451728 : ((False ∧ ((p3 ∧ False) ∨ (p3 ∧ (p3 → p5)))) ∨ (((p2 ∨ (((False → p2) → ((p3 ∨ p5) → (p1 ∨ p1))) → p3)) ∨ p2) ∨ (True ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47257230549541613622901419855 : ((((p2 → ((p3 ∧ p1) ∨ (False ∨ p5))) ∨ ((((p5 ∨ ((p4 ∧ ((False → p4) ∨ False)) ∧ p1)) → p2) ∧ p2) ∧ p4)) ∨ (p5 ∨ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186714902742876428485244205344 : ((((p3 → p4) ∧ ((p4 → True) ∧ p5)) ∨ ((False ∨ p1) ∧ False)) → ((((p5 → p5) ∨ False) ∧ (True → (((p4 → False) ∨ p5) → p1))) ∨ True)) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h10 =>
      -- False on the left can always be used.
      apply False.elim h10
    case inr h11 =>
      -- False on the left can always be used.
      apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41947351292168000616704181422 : ((((p1 ∧ False) ∧ ((p5 ∨ (p3 → (p1 ∧ (((p5 ∨ ((p4 ∨ (p2 ∧ (p5 ∧ True))) ∧ p2)) ∧ (p3 → p3)) ∧ p5)))) ∨ p5)) ∨ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_601722279633756936250838435326 : ((((p4 ∧ ((((p4 ∧ p1) ∧ False) ∨ ((p2 ∨ (p3 ∨ (False ∨ p2))) ∨ ((p3 → p5) ∨ ((p4 ∨ p5) ∧ (p4 ∧ True))))) ∧ False)) ∧ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313096548738785367754183025916 : (p3 ∨ ((((((p4 → p1) → True) → False) ∧ (True ∨ (((((p1 → p4) ∨ p5) ∧ (False → (p2 ∧ p3))) ∧ p4) ∧ p2))) → (p3 ∧ True)) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h5 : ((p4 → p1) → True) := by
      -- Implications on the right can always be decomposed.
      intro h6
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
    -- Conjunctions on the left can always be decomposed.
    let h11 := h9.left
    let h12 := h9.right
    -- Conjunctions on the left can always be decomposed.
    let h13 := h11.left
    let h14 := h11.right
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h15 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h16 : ((p4 → p1) → True) := by
        -- Implications on the right can always be decomposed.
        intro h17
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h18 := h2 h16
      -- False on the left can always be used.
      apply False.elim h18
    case inr h19 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h20 : ((p4 → p1) → True) := by
        -- Implications on the right can always be decomposed.
        intro h21
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h22 := h2 h20
      -- False on the left can always be used.
      apply False.elim h22
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_209363235065144379116465267151 : ((p1 → (((p3 → p2) ∧ p2) ∧ p3)) → (((((p5 → p2) → (p2 → p1)) ∨ p1) ∧ p1) → (((((p1 ∧ p3) ∧ p3) → False) ∨ p1) → p3))) := by
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
    let h5 := h2.left
    let h6 := h2.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h8 : p1 := by
        -- One of the premise coincides with the conclusion.
        exact h6
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h9 := h1 h8
      -- We need to get the right conjuct of h9 based on <expert-advice>.
      let h10 := h9.right
      -- One of the premise coincides with the conclusion.
      exact h10
    case inr h11 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h12 : p1 := by
        -- One of the premise coincides with the conclusion.
        exact h6
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h13 := h1 h12
      -- We need to get the right conjuct of h13 based on <expert-advice>.
      let h14 := h13.right
      -- One of the premise coincides with the conclusion.
      exact h14
  case inr h15 =>
    -- Conjunctions on the left can always be decomposed.
    let h16 := h2.left
    let h17 := h2.right
    -- Disjunctions on the left can always be decomposed.
    cases h16
    case inl h18 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h19 : p1 := by
        -- One of the premise coincides with the conclusion.
        exact h17
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h20 := h1 h19
      -- We need to get the right conjuct of h20 based on <expert-advice>.
      let h21 := h20.right
      -- One of the premise coincides with the conclusion.
      exact h21
    case inr h22 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h23 : p1 := by
        -- One of the premise coincides with the conclusion.
        exact h17
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h24 := h1 h23
      -- We need to get the right conjuct of h24 based on <expert-advice>.
      let h25 := h24.right
      -- One of the premise coincides with the conclusion.
      exact h25



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166561058433834611746304863606 : ((p5 ∨ (p4 ∧ (((p2 → False) → False) ∧ ((p1 → (p5 ∧ (p5 → (p5 → p3)))) → p1)))) ∨ ((((False ∨ False) ∨ p5) ∧ True) → (p1 → p1))) := by
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
  cases h3
  case inl h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- False on the left can always be used.
      apply False.elim h6
    case inr h7 =>
      -- False on the left can always be used.
      apply False.elim h7
  case inr h8 =>
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_808685187034501468148112139050 : (((p4 → (p2 → ((((((((((p3 ∨ p1) ∨ p3) ∨ (False → p5)) → p3) → (p4 → p5)) ∨ p3) ∨ p1) → (p4 ∧ p3)) ∨ p4) ∨ p3))) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_176261598746040850012948259576 : (((((((p2 ∨ (p2 ∨ p1)) ∧ p1) ∧ p3) ∨ True) ∨ True) ∨ (p4 ∧ True)) ∧ (p3 ∨ (((True ∨ ((p4 → (p1 ∧ False)) → False)) ∧ p5) ∨ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_807139909503876344780768111903 : (((p4 → ((p1 ∨ (((p4 ∧ (((p4 ∨ (False ∧ (p5 ∧ p5))) ∧ p5) ∧ False)) ∨ (p3 ∨ True)) ∧ p1)) → ((p1 → (p4 ∧ p5)) → p5))) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h5 : p1 := by
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h6 := h3 h5
    -- We need to get the right conjuct of h6 based on <expert-advice>.
    let h7 := h6.right
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- Conjunctions on the left can always be decomposed.
      let h14 := h13.left
      let h15 := h13.right
      -- Conjunctions on the left can always be decomposed.
      let h16 := h14.left
      let h17 := h14.right
      -- Disjunctions on the left can always be decomposed.
      cases h16
      case inl h18 =>
        -- False on the left can always be used.
        apply False.elim h15
      case inr h19 =>
        -- Conjunctions on the left can always be decomposed.
        let h20 := h19.left
        let h21 := h19.right
        -- False on the left can always be used.
        apply False.elim h20
    case inr h22 =>
      -- Disjunctions on the left can always be decomposed.
      cases h22
      case inl h23 =>
        -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
        have h24 : p1 := by
          -- One of the premise coincides with the conclusion.
          exact h10
        -- We have shown the premise of h3, we can now drive its conclusion.
        let h25 := h3 h24
        -- We need to get the right conjuct of h25 based on <expert-advice>.
        let h26 := h25.right
        -- One of the premise coincides with the conclusion.
        exact h26
      case inr h27 =>
        -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
        have h28 : p1 := by
          -- One of the premise coincides with the conclusion.
          exact h10
        -- We have shown the premise of h3, we can now drive its conclusion.
        let h29 := h3 h28
        -- We need to get the right conjuct of h29 based on <expert-advice>.
        let h30 := h29.right
        -- One of the premise coincides with the conclusion.
        exact h30
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117495636803816345479837542110 : ((p1 ∧ (p4 → (p3 ∧ ((((False ∨ ((p5 → p3) ∨ (p1 ∧ p1))) → ((((p5 → False) → p2) ∧ p3) → p5)) ∧ p5) ∧ p1)))) ∨ (True ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_647999627344523374188246694296 : (((((((p1 ∧ (((p1 ∧ (True ∨ p3)) ∨ False) ∧ (True → p3))) → (p5 ∨ True)) ∧ ((p3 ∨ (True ∨ True)) ∨ p3)) ∧ False) ∧ (p2 ∨ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138487001807974005448342057816 : (((((p2 → ((p2 ∧ p1) → (True ∨ (p1 → ((p1 ∧ p1) ∧ (p4 → p2)))))) ∨ ((p4 ∨ p3) → p4)) ∧ p2) ∧ p2) → ((p2 → False) → p5)) := by
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
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h8 : p2 := by
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h9 := h2 h8
    -- False on the left can always be used.
    apply False.elim h9
  case inr h10 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h11 : p2 := by
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h12 := h2 h11
    -- False on the left can always be used.
    apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228710952544244697319059565963 : ((p2 ∨ (True → False)) ∨ (((p1 → (False → (p4 ∧ p3))) → ((p3 → p2) ∨ (((p5 ∨ (p5 ∨ p1)) → p5) ∧ (p1 ∧ (p5 ∧ p2))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47182320046302434134526584511 : ((((p3 ∨ ((True → ((p3 ∨ (p3 ∧ True)) → (p1 → p3))) ∨ (False → p2))) → ((p1 → p3) ∧ (p2 → (p2 ∨ p5)))) ∨ (p3 → True)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351577833667536013374773025970 : (p4 → (((p4 → p3) ∨ (((p3 ∨ p1) ∨ True) ∨ ((((p3 ∨ p5) ∧ p4) → p4) → (p4 ∧ p4)))) → ((False ∨ ((p4 ∧ False) → p2)) ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
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
        -- Disjunctions on the left can always be decomposed.
        cases h9
        case inl h10 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h11
          -- Conjunctions on the left can always be decomposed.
          let h12 := h11.left
          let h13 := h11.right
          -- False on the left can always be used.
          apply False.elim h13
        case inr h14 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h15
          -- Conjunctions on the left can always be decomposed.
          let h16 := h15.left
          let h17 := h15.right
          -- False on the left can always be used.
          apply False.elim h17
      case inr h18 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h19
        -- Conjunctions on the left can always be decomposed.
        let h20 := h19.left
        let h21 := h19.right
        -- False on the left can always be used.
        apply False.elim h21
    case inr h22 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h23
      -- Conjunctions on the left can always be decomposed.
      let h24 := h23.left
      let h25 := h23.right
      -- False on the left can always be used.
      apply False.elim h25



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_728345280323032596097549372200 : ((((p1 → (False ∧ p4)) ∨ (((p1 ∧ p5) → (p2 → ((p3 ∧ ((p4 ∧ p5) ∨ False)) ∨ ((p4 ∨ (p4 → p3)) ∨ True)))) ∧ (True ∨ True))) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181625305634397133334668630564 : ((p2 → (p3 ∧ ((True ∧ p5) ∧ ((p4 → False) → (p1 ∨ (p5 → p2)))))) → (((p5 ∨ (p5 → ((p3 ∨ (p2 ∧ p5)) ∨ False))) ∨ p1) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_3053452127847918113971847396 : ((p5 → (True ∧ False)) → (((True ∨ ((True ∧ ((p4 ∨ True) ∧ p1)) → (True ∧ p2))) ∧ (True ∨ True)) → (p5 → (p1 ∨ (p3 ∧ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h8 : p5 := by
        -- One of the premise coincides with the conclusion.
        exact h3
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h9 := h1 h8
      -- We need to get the right conjuct of h9 based on <expert-advice>.
      let h10 := h9.right
      -- False on the left can always be used.
      apply False.elim h10
    case inr h11 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h12 : p5 := by
        -- One of the premise coincides with the conclusion.
        exact h3
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h13 := h1 h12
      -- We need to get the right conjuct of h13 based on <expert-advice>.
      let h14 := h13.right
      -- False on the left can always be used.
      apply False.elim h14
  case inr h15 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h16 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h17 : p5 := by
        -- One of the premise coincides with the conclusion.
        exact h3
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h18 := h1 h17
      -- We need to get the right conjuct of h18 based on <expert-advice>.
      let h19 := h18.right
      -- False on the left can always be used.
      apply False.elim h19
    case inr h20 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h21 : p5 := by
        -- One of the premise coincides with the conclusion.
        exact h3
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h22 := h1 h21
      -- We need to get the right conjuct of h22 based on <expert-advice>.
      let h23 := h22.right
      -- False on the left can always be used.
      apply False.elim h23



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214409630790113384591108039436 : (((p1 → (p1 → True)) → False) ∨ ((False ∨ ((p1 ∧ p3) ∨ p1)) ∨ (((p3 → p3) ∨ p3) ∨ ((p3 ∧ (p2 ∧ ((True ∧ False) → p2))) → False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147498894964595293184427392668 : (((False ∨ (((p5 ∧ p2) ∧ (((((p5 → p4) → p1) ∧ p3) ∨ p5) → p5)) ∨ (False → (p2 ∨ True)))) ∨ p5) ∨ (((p1 ∨ p1) → p5) ∧ False)) := by
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
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215681774139764181082385484910 : ((False ∨ ((p2 ∧ p5) ∧ p4)) ∨ ((False ∨ True) ∨ ((((p1 ∨ True) ∨ p1) ∨ ((True ∧ p5) → p4)) ∧ (((p3 ∧ p1) ∨ p1) ∧ (True ∨ p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_978324989197071329691894781989 : (((True ∧ (False ∨ (((((p3 → (p1 ∨ (False ∧ p2))) → False) ∧ (((p1 ∨ p1) ∧ p3) ∧ (((p2 ∧ p4) → True) ∨ p2))) → p4) → False))) → p5) ∧ True) := by
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
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h6 : ((((p3 → (p1 ∨ (False ∧ p2))) → False) ∧ (((p1 ∨ p1) ∧ p3) ∧ (((p2 ∧ p4) → True) ∨ p2))) → p4) := by
      -- Implications on the right can always be decomposed.
      intro h7
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- Conjunctions on the left can always be decomposed.
      let h12 := h10.left
      let h13 := h10.right
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h14 =>
        -- Disjunctions on the left can always be decomposed.
        cases h11
        case inl h15 =>
          -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
          have h16 : (p3 → (p1 ∨ (False ∧ p2))) := by
            -- Implications on the right can always be decomposed.
            intro h17
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h14
          -- We have shown the premise of h8, we can now drive its conclusion.
          let h18 := h8 h16
          -- False on the left can always be used.
          apply False.elim h18
        case inr h19 =>
          -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
          have h20 : (p3 → (p1 ∨ (False ∧ p2))) := by
            -- Implications on the right can always be decomposed.
            intro h21
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h14
          -- We have shown the premise of h8, we can now drive its conclusion.
          let h22 := h8 h20
          -- False on the left can always be used.
          apply False.elim h22
      case inr h23 =>
        -- Disjunctions on the left can always be decomposed.
        cases h11
        case inl h24 =>
          -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
          have h25 : (p3 → (p1 ∨ (False ∧ p2))) := by
            -- Implications on the right can always be decomposed.
            intro h26
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h23
          -- We have shown the premise of h8, we can now drive its conclusion.
          let h27 := h8 h25
          -- False on the left can always be used.
          apply False.elim h27
        case inr h28 =>
          -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
          have h29 : (p3 → (p1 ∨ (False ∧ p2))) := by
            -- Implications on the right can always be decomposed.
            intro h30
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h23
          -- We have shown the premise of h8, we can now drive its conclusion.
          let h31 := h8 h29
          -- False on the left can always be used.
          apply False.elim h31
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h32 := h5 h6
    -- False on the left can always be used.
    apply False.elim h32
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_18726192147907021136500867747 : (((((((((p3 ∧ p5) ∧ p3) → (True ∧ p5)) → ((p1 ∨ p2) ∨ p5)) → p2) ∨ p2) ∧ p5) ∨ (True ∧ (p5 → ((p1 → p4) ∨ True)))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233107727773003031704821154493 : ((p4 ∧ (p4 → True)) → ((((p2 ∧ p1) ∧ ((p1 → p5) → p2)) ∨ p5) ∨ ((p1 → ((False ∨ (p4 ∨ False)) ∨ p3)) ∨ (p4 → (p5 → p4))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_711909519133240398451659065797 : (((((False → (p3 ∨ (True → p3))) ∧ p1) ∨ (((p2 ∨ (((((False ∧ True) ∨ p2) ∧ p4) → (True ∨ p4)) ∧ True)) → p1) ∨ (False ∨ True))) ∨ False) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_800383239798302146458547605768 : (((p2 → (((False → p2) → ((p4 ∧ ((((p1 ∨ (p3 ∨ p3)) ∨ (p2 ∨ p3)) → (True → False)) → False)) ∨ ((p1 → p2) ∨ p5))) ∨ p3)) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38239792267333608978408642106 : ((((((p5 ∨ p1) ∨ ((p1 ∨ (((p3 ∨ p2) ∨ (p1 ∧ False)) → False)) ∨ (False → p2))) ∨ True) ∧ (((True ∧ p5) ∨ p5) ∨ p2)) ∧ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165452948556000298122060728533 : ((((((p1 ∧ (p3 ∧ False)) → False) ∨ False) ∧ (p2 ∧ p4)) ∧ (p5 ∧ ((p1 → p2) → p4))) ∨ (((True → (True ∨ p3)) ∨ p1) ∨ (True ∧ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215915865228970328209972786883 : ((p3 ∨ (p2 ∧ (True ∧ True))) ∨ ((((((p5 ∨ p3) ∨ p1) ∨ (p5 → p3)) → p1) → p1) ∨ (p5 ∨ (((p2 ∨ p3) → p3) ∨ (False → False))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_150689006631047964957694696278 : (((p3 → (((p5 ∧ False) → p4) → (p2 → (((False ∧ False) ∧ ((p5 → (p3 ∨ True)) ∨ p3)) → p1)))) ∧ p2) → (p1 ∨ (p2 → (False ∨ True)))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



