variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317703182162754584449432007525 : (p4 ∨ ((((p1 ∧ ((((p3 → p5) ∧ p2) ∧ (False → ((p3 ∧ (((False → p3) ∧ p4) → False)) ∨ p3))) ∨ p2)) ∧ p2) ∨ (False → p2)) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119407497580832668673714452396 : ((p4 → ((p2 ∨ (p5 → (((((p1 ∨ p5) ∧ ((p1 ∨ True) ∧ (False → False))) → False) ∧ p3) → (p3 → (p2 ∨ p2))))) ∨ False)) ∨ (p3 → p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h7 : ((p1 ∨ p5) ∧ ((p1 ∨ True) ∧ (False → False))) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
    -- Implications on the right can always be decomposed.
    intro h8
    -- False on the left can always be used.
    apply False.elim h8
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h9 := h5 h7
  -- False on the left can always be used.
  apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52036947458170549866575781615 : (((p5 ∨ ((p3 ∨ ((((p2 → (p2 → (p1 → p3))) ∧ p4) → p3) ∨ p2)) ∧ True)) ∨ ((p2 ∨ True) ∨ ((True → p2) → (p3 ∧ p4)))) ∨ p4) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171762691126387868347492391910 : (((((p4 ∧ ((p4 ∧ (p1 ∧ (True ∨ p3))) ∧ p2)) → (p3 → p3)) → True) → p1) ∨ (p5 ∨ ((p4 → ((p2 ∨ (False ∧ p1)) ∨ True)) ∨ p1))) := by
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
theorem thm_5_vars_135276893442492162019324697960 : (((p5 ∨ ((((p5 ∧ p5) ∧ (((False ∨ ((p5 ∧ p2) ∧ (False → p5))) → p1) ∨ True)) ∨ True) ∧ p4)) → (p3 ∨ p2)) ∨ ((True ∨ False) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319294138439383815675051352749 : (p4 ∨ ((((((p4 ∨ False) → (p2 → (p3 ∨ p2))) ∧ (False → (p2 ∧ True))) → p2) ∧ p4) → (p2 ∨ ((p5 → p2) → (p3 ∧ (p4 ∨ p4)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (((p4 ∨ False) → (p2 → (p3 ∨ p2))) ∧ (False → (p2 ∧ True))) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h5
    -- Implications on the right can always be decomposed.
    intro h6
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h8 =>
      -- False on the left can always be used.
      apply False.elim h8
    -- Implications on the right can always be decomposed.
    intro h9
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- False on the left can always be used.
    apply False.elim h9
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h10 := h2 h4
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_754843562275549667821676221026 : (((False ∧ (p2 ∨ (((True → ((False ∨ ((p1 ∧ p1) → ((p2 ∧ (p2 ∨ p2)) → p4))) ∧ False)) → (((p4 → p2) ∧ False) ∧ p2)) ∧ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157961926280634282169594587391 : ((((((p5 ∨ p2) → p4) → p1) ∨ (p3 ∧ False)) ∨ (False → (((p5 ∨ p3) → p3) ∧ (p4 → True)))) ∨ (p2 → ((False ∨ p5) → (False → True)))) := by
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
theorem thm_5_vars_59466200190533630018706912087 : (((p1 → False) ∨ ((p5 ∨ p2) → (p2 ∧ ((True ∨ ((p4 → ((p3 ∨ p2) → True)) ∨ (True ∨ p2))) → (p2 ∨ ((p1 ∨ p4) → p2)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134462979552766665541093664059 : (((((p1 ∧ (p3 ∧ p2)) → (((p1 → (p4 ∧ (False ∧ p4))) → True) ∧ ((True → (p3 ∨ p5)) → p3))) ∧ p1) → p2) ∨ ((p4 ∧ p3) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46124649311505249449811750316 : ((((p3 → ((False ∨ (p5 → (((p1 ∨ ((True → ((p2 ∧ p1) ∧ p3)) → p1)) → (p1 → p1)) ∨ True))) → p4)) ∨ p5) ∧ (p2 ∨ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_608257407594261354641455259565 : (((((((p3 → (p3 → ((((p1 → p3) → p3) ∨ (p1 → (p2 ∧ (True ∧ (p2 ∨ p3))))) ∧ (False ∨ False)))) ∨ p2) ∨ p5) ∨ p3) ∨ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61568301671970311224350222571 : ((p1 ∧ ((p2 → ((p2 → p1) ∧ (True → p1))) ∨ (True → (((False → (True ∨ True)) ∨ p1) → (p4 → (False ∨ ((p5 → False) ∨ True))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40448330475998162758606809046 : ((((((False ∨ (p4 ∧ p1)) ∧ (p4 ∧ p1)) ∨ (True ∨ ((((p5 → (False → p3)) ∧ p1) → p3) ∧ ((p3 → p5) ∧ True)))) ∨ True) ∨ p5) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_555337597895299284876226792565 : (((p2 ∨ (p1 → ((True → ((((p4 → (p4 → (p1 ∨ ((True ∨ p2) ∧ ((p5 ∨ p4) ∧ p2))))) → False) ∨ p5) ∨ (p1 ∨ p5))) ∨ p3))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157050277079066253006614655709 : (((p2 ∧ (((p5 ∧ ((((p3 ∧ p2) ∨ False) ∧ (p5 → (p1 → False))) ∧ True)) → p1) ∨ p2)) ∨ p1) ∨ ((p4 → (p5 ∧ p5)) → (p4 → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_253908368217688129114386750993 : ((p1 ∧ p4) → ((p5 ∧ (((((p3 ∧ p3) ∨ (False ∧ True)) ∧ (p4 ∧ (p1 ∨ p3))) → (((p1 ∧ p3) → (False ∧ False)) ∧ p5)) → False)) ∨ p4)) := by
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
theorem thm_5_vars_314429212197427508035222701154 : (p3 ∨ (((p5 ∨ (p3 → p3)) → (((p3 ∧ True) → p2) → ((p1 → p5) ∨ (((p4 ∧ p2) ∨ p1) → p5)))) ∨ ((True ∧ False) → (False → p2)))) := by
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
theorem thm_5_vars_148713259162853832618512692379 : ((((p2 → (False → p2)) ∧ ((p5 ∧ p4) → p2)) → (p5 ∨ ((((True ∨ (True ∨ p5)) → True) → True) ∧ p5))) ∨ ((p3 ∧ (p5 ∨ True)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_343131322017920676689476084493 : (p2 → (((p4 ∨ p4) ∧ True) ∨ (((((p1 → p2) ∨ p4) → True) → p5) → ((((p4 ∨ p5) → True) ∨ (p5 ∨ True)) → ((p3 ∨ p5) ∨ p1))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h5 : (((p1 → p2) ∨ p4) → True) := by
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h9
    case inr h10 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h11 : (((p1 → p2) ∨ p4) → True) := by
        -- Implications on the right can always be decomposed.
        intro h12
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h13 := h2 h11
      -- One of the premise coincides with the conclusion.
      exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_140875901618877393111823580347 : ((((False → p3) ∧ (((p5 ∧ False) ∧ p2) ∧ ((p5 ∧ p1) → False))) → (((((True → p1) ∧ p2) ∧ False) ∨ p3) ∨ p4)) → ((True → False) → p5)) := by
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
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61647904478239897689847587990 : ((p1 ∧ (False ∧ (p5 ∨ ((p1 ∧ ((True ∧ p4) ∧ (((p1 ∨ (p4 ∨ p1)) ∨ p3) → (p1 ∨ True)))) ∧ (p1 → (False ∨ (False → p4))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_737033480904456637167242218991 : ((((p3 → p1) ∧ (p2 ∧ (p4 ∧ (((p1 ∧ p5) ∨ (((p3 ∧ (False → p3)) ∧ (p4 ∧ True)) ∧ True)) ∨ ((p2 → p5) ∧ (False ∧ p5)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184121015579626582509399725083 : ((((p5 → p4) → ((True ∧ False) ∧ ((p1 → p1) → p1))) ∨ True) ∨ ((p4 ∧ (p1 ∧ (((p3 ∨ True) → (False → p1)) → (True → p3)))) → p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_607727815774764738731303742263 : (((((False ∨ ((p4 ∨ p5) → ((((((p1 ∨ p1) ∨ ((False → True) → (p4 ∧ p2))) ∧ p4) ∧ True) ∧ p3) → (p1 ∨ p2)))) ∧ p1) ∨ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48905214447087167762188562743 : (((p4 → ((((((True ∧ True) → ((p3 → p1) ∧ (p3 ∧ p2))) → (p4 → False)) ∧ True) ∨ p1) ∧ (p3 ∨ False))) ∧ (p5 ∧ (p4 ∧ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_742312596964515269394337647487 : ((((p1 → p2) ∨ (p4 ∨ ((True ∧ (p4 ∨ p3)) ∨ ((((p1 ∨ True) ∧ p1) → (p4 ∨ (False ∨ False))) ∨ (p3 ∨ (p1 → (p3 ∧ p1))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_243296263066542989937728643983 : ((p4 → p4) ∧ ((((False → (p3 ∨ True)) → (((p2 → ((p3 ∨ True) ∧ p1)) ∧ True) ∨ p2)) ∧ (p4 → p5)) → (p1 ∨ (True ∨ (p4 → True))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_302978271117126466627869015346 : (False ∨ (p1 → (((p2 ∧ (((((p3 ∧ True) → p5) ∨ p3) → False) → p4)) → ((p2 ∧ p4) ∨ (p2 ∨ (((True ∧ p1) → p3) ∧ p5)))) ∧ True))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150212838742352968980379718158 : ((p2 → ((p4 ∨ (p4 → (True → True))) → ((p3 ∨ False) ∧ (((p3 → False) → (p5 ∧ p2)) → (p5 ∧ p5))))) ∨ (p2 ∨ (p2 → (p2 ∨ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_247862676005777237819911792426 : ((p1 ∨ p2) ∨ (((False ∨ False) ∧ p4) ∨ (((p4 ∨ (True ∧ p3)) ∨ ((p4 ∧ (p3 → p3)) → p5)) ∨ (True → (p5 ∨ (False ∨ (p4 → p4))))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_732907626170413231595428064204 : ((((p2 ∧ p1) ∧ (p2 → ((p2 ∧ ((((True ∧ True) ∨ False) ∧ p5) ∨ ((p2 ∧ ((p3 ∨ False) → False)) ∧ p4))) ∨ (p3 ∧ (p2 → p4))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_680314533792107719968394383340 : (((((((((p4 ∧ p3) ∧ p1) ∧ (((True ∧ p2) ∨ True) → p1)) ∧ p5) ∧ p4) ∨ ((p2 ∨ p4) ∨ True)) → (p3 ∨ ((p1 ∧ p3) ∨ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165724464588075576622856830420 : (((p1 ∨ (False ∧ (p4 ∧ True))) ∧ (False ∨ ((p2 → (True → (p5 ∧ p5))) ∨ (p5 ∧ p2)))) ∨ ((p1 → p3) ∨ ((p4 → p4) → (p3 → True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67294534275415363874998657477 : ((p1 → (((False ∧ ((((True ∧ (p4 → (p4 ∨ p3))) → ((True ∧ p4) ∧ False)) ∧ p4) ∨ ((True ∨ p5) ∧ p5))) ∨ (True → p5)) ∧ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356477035867935165806201920651 : (p5 → (((p5 → p1) ∧ (((False ∨ p2) → ((p2 → p2) ∨ p3)) ∨ p5)) → ((p5 ∨ ((False ∨ ((p4 → p3) ∨ (p5 → p4))) ∧ True)) → p1))) := by
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
    cases h6
    case inl h7 =>
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h8 : p5 := by
        -- One of the premise coincides with the conclusion.
        exact h1
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h9 := h5 h8
      -- One of the premise coincides with the conclusion.
      exact h9
    case inr h10 =>
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h11 : p5 := by
        -- One of the premise coincides with the conclusion.
        exact h1
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h12 := h5 h11
      -- One of the premise coincides with the conclusion.
      exact h12
  case inr h13 =>
    -- Conjunctions on the left can always be decomposed.
    let h14 := h13.left
    let h15 := h13.right
    -- Disjunctions on the left can always be decomposed.
    cases h14
    case inl h16 =>
      -- False on the left can always be used.
      apply False.elim h16
    case inr h17 =>
      -- Disjunctions on the left can always be decomposed.
      cases h17
      case inl h18 =>
        -- Conjunctions on the left can always be decomposed.
        let h19 := h2.left
        let h20 := h2.right
        -- Disjunctions on the left can always be decomposed.
        cases h20
        case inl h21 =>
          -- We want to use the implication h19 based on <expert-advice>. So we show its premise.
          have h22 : p5 := by
            -- One of the premise coincides with the conclusion.
            exact h1
          -- We have shown the premise of h19, we can now drive its conclusion.
          let h23 := h19 h22
          -- One of the premise coincides with the conclusion.
          exact h23
        case inr h24 =>
          -- We want to use the implication h19 based on <expert-advice>. So we show its premise.
          have h25 : p5 := by
            -- One of the premise coincides with the conclusion.
            exact h1
          -- We have shown the premise of h19, we can now drive its conclusion.
          let h26 := h19 h25
          -- One of the premise coincides with the conclusion.
          exact h26
      case inr h27 =>
        -- Conjunctions on the left can always be decomposed.
        let h28 := h2.left
        let h29 := h2.right
        -- Disjunctions on the left can always be decomposed.
        cases h29
        case inl h30 =>
          -- We want to use the implication h28 based on <expert-advice>. So we show its premise.
          have h31 : p5 := by
            -- One of the premise coincides with the conclusion.
            exact h1
          -- We have shown the premise of h28, we can now drive its conclusion.
          let h32 := h28 h31
          -- One of the premise coincides with the conclusion.
          exact h32
        case inr h33 =>
          -- We want to use the implication h28 based on <expert-advice>. So we show its premise.
          have h34 : p5 := by
            -- One of the premise coincides with the conclusion.
            exact h1
          -- We have shown the premise of h28, we can now drive its conclusion.
          let h35 := h28 h34
          -- One of the premise coincides with the conclusion.
          exact h35



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324412320527516266010135517502 : (p5 ∨ (((False → False) → ((p1 → True) ∧ p4)) → (((p4 → False) ∧ (p3 ∧ (False ∨ (p5 ∨ (((p2 ∨ True) → p3) → p2))))) → (p2 → False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h11 : p4 := by
        -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
        have h12 : (False → False) := by
          -- Implications on the right can always be decomposed.
          intro h13
          -- False on the left can always be used.
          apply False.elim h13
        -- We have shown the premise of h1, we can now drive its conclusion.
        let h14 := h1 h12
        -- We need to get the right conjuct of h14 based on <expert-advice>.
        let h15 := h14.right
        -- One of the premise coincides with the conclusion.
        exact h15
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h16 := h4 h11
      -- False on the left can always be used.
      apply False.elim h16
    case inr h17 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h18 : p4 := by
        -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
        have h19 : (False → False) := by
          -- Implications on the right can always be decomposed.
          intro h20
          -- False on the left can always be used.
          apply False.elim h20
        -- We have shown the premise of h1, we can now drive its conclusion.
        let h21 := h1 h19
        -- We need to get the right conjuct of h21 based on <expert-advice>.
        let h22 := h21.right
        -- One of the premise coincides with the conclusion.
        exact h22
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h23 := h4 h18
      -- False on the left can always be used.
      apply False.elim h23



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149131717555100301658315166903 : (((p3 ∧ p3) ∧ (((True ∨ (p3 ∨ ((p4 ∧ p5) ∧ (p3 ∧ False)))) ∨ (p2 → p5)) → (p3 → (p3 ∧ p4)))) ∨ (False → ((p2 ∨ False) ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_655022212034052286513711389614 : ((((((p2 ∨ p2) → ((((p4 → ((p4 ∨ p4) → p4)) ∨ p4) ∧ p5) ∨ ((p1 ∨ p2) ∧ (True ∧ (p5 → True))))) → p4) ∨ (False → p1)) ∨ p1) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301984800767583314683083700634 : (False ∨ ((p2 → p3) → ((False ∨ ((True ∧ (False ∧ (False → (True → ((p5 → False) ∧ p1))))) ∨ (p1 ∧ True))) → (p3 ∨ ((p2 → True) ∧ p1))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- False on the left can always be used.
      apply False.elim h8
    case inr h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h13
      -- True on the right can always be proven directly.
      apply True.intro
      -- One of the premise coincides with the conclusion.
      exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_677389837606588086792977060882 : ((((((((p1 ∨ (p1 ∧ ((((True ∨ p2) ∧ p4) → p3) ∧ False))) ∨ p1) ∧ (p3 ∨ p1)) ∨ p1) ∨ p2) ∨ (False ∧ ((p5 → p1) ∨ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57150545517256988837944912701 : ((((p5 → p4) ∧ True) ∨ (((True → False) ∨ (p4 ∧ p1)) ∨ (((p1 → True) ∨ p1) ∧ ((((False → (p4 → p2)) ∧ p2) ∨ False) → p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118575320236584627862528285525 : ((p4 ∨ (((p1 ∨ ((False ∧ (p1 ∨ p2)) → (p1 ∧ ((((False ∧ p2) ∧ p1) ∨ p1) → (p3 → True))))) → (p5 ∧ p3)) ∨ True)) ∨ (p4 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207550591124547359208368400250 : (((((p3 ∨ p5) ∧ p5) ∨ p5) → True) → (((p3 → (((p1 ∧ False) → p1) ∧ ((True → (False → ((p5 ∨ p2) ∨ p3))) → p5))) ∧ p3) → p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h5 : p3 := by
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h5
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
  have h8 : (True → (False → ((p5 ∨ p2) ∨ p3))) := by
    -- Implications on the right can always be decomposed.
    intro h9
    -- Implications on the right can always be decomposed.
    intro h10
    -- False on the left can always be used.
    apply False.elim h10
  -- We have shown the premise of h7, we can now drive its conclusion.
  let h11 := h7 h8
  -- One of the premise coincides with the conclusion.
  exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_316512852144375472160536962382 : (p3 ∨ (p2 ∨ ((((False ∨ (p2 → True)) ∨ (p2 → True)) → False) → ((((((p4 ∨ p5) ∨ (p1 ∧ False)) ∨ p1) → p1) ∨ True) ∧ (p1 ∧ p3))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((False ∨ (p2 → True)) ∨ (p2 → True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- False on the left can always be used.
  apply False.elim h4
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h5 : ((False ∨ (p2 → True)) ∨ (p2 → True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h7 := h1 h5
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_739050761335393214354352590906 : ((((p3 ∧ p4) ∨ ((((((((p2 ∧ (False → (True ∨ p5))) ∨ p2) ∧ False) ∧ p4) → (p1 ∨ (False ∨ p4))) ∧ (p2 → p5)) → p4) ∧ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51484859773042091082457466955 : (((((p5 ∧ True) → (False → (p5 ∧ p5))) → ((p5 ∨ (False ∨ True)) ∨ ((p5 ∨ p3) → p2))) → (((False → p5) → (False → False)) ∧ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49197458523526010386513627326 : (((((False ∧ p4) ∨ p5) ∨ (False ∨ ((p1 ∨ (False ∨ (p3 ∨ (p4 ∨ (((False → p3) ∧ True) ∨ p1))))) ∨ True))) ∨ ((p3 → p1) ∧ True)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_51958527663328882221133877166 : ((((p1 ∧ (p5 → (p2 ∨ p5))) ∨ (p2 → ((p1 → (p3 → (p3 → p4))) ∧ p2))) ∨ ((p1 ∨ p3) ∧ ((p5 ∧ (p2 ∧ True)) ∧ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_793831927188159059963158853506 : (((True → (p2 → (p1 ∧ ((p1 ∨ (((p3 ∧ (p3 ∧ (p4 ∨ p1))) → False) → p3)) → (((True ∨ p2) → (p1 ∨ (False ∨ p4))) ∨ p4))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300053402724410917846354371905 : (False ∨ ((((p1 → (p1 ∧ (((p1 ∨ p4) ∧ p3) → (False → (p5 ∨ (p2 → (False ∨ (False ∧ p2)))))))) → (p2 → p3)) ∧ p2) ∨ (False → False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58951268725252075969900592016 : (((p2 ∧ False) ∨ (((((False ∨ ((p3 → (p4 ∨ (p4 → p3))) ∧ p5)) ∨ True) ∧ p2) → (p2 ∧ (p2 ∧ ((p4 → p2) ∧ False)))) ∨ True)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157540120623855611031954124799 : (((((p1 ∨ p1) ∨ (p3 ∧ ((p1 ∨ p1) ∧ (p2 ∨ (p2 ∨ (p5 → p2)))))) ∨ p4) → (False ∨ p5)) ∨ ((p4 ∨ ((p1 → False) → p4)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119335493947296569675218219797 : ((p3 → (((p4 → (True → False)) ∧ p5) ∧ ((((p4 ∧ ((p2 ∨ p5) ∧ p3)) → False) ∧ (p3 ∨ p5)) → ((p4 → p4) ∧ p2)))) ∨ (p3 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_706811746687956049169909364604 : ((((((True → p2) → ((True ∨ p5) ∧ p1)) ∧ p2) ∨ ((p5 ∨ (((p4 → (True → False)) → (p3 ∧ ((False ∧ True) ∨ p1))) ∧ p1)) ∧ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_226038584359751015922613035208 : (((p5 ∧ True) ∨ p5) ∨ (((p4 ∧ p1) ∧ ((((False → ((p2 ∧ p1) ∨ True)) → (p2 → p1)) ∧ p4) → p2)) ∨ (p2 → ((p1 ∨ p2) ∧ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51682136888229279603130191855 : (((((((False ∧ p1) ∧ (p5 ∧ (p3 ∧ p1))) ∧ (p4 ∨ p4)) ∨ True) ∨ (p1 → p4)) ∧ (p5 ∨ (((True ∧ (p4 → p2)) ∨ p2) ∧ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328297119037228267032270399685 : (True → ((((p3 ∧ p1) ∨ False) ∨ (((p1 → ((p4 ∧ p2) ∨ ((p4 ∧ p3) ∨ False))) → (True ∧ p2)) ∧ p1)) ∨ ((p1 ∨ p2) → (p1 → p1)))) := by
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
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205466196899393748746258334914 : (((p3 → (p1 ∧ p3)) → (False ∨ p2)) ∨ ((False → False) ∨ ((((p4 ∧ p2) ∨ p5) ∨ p1) ∧ (True ∧ ((p1 → ((p4 ∧ p3) → p5)) ∨ p3))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_641496940372292214912382818634 : (((((False ∧ p4) → (p5 ∨ (((False ∨ True) ∨ p1) ∨ (p5 ∨ (p4 → ((p1 ∨ ((p1 → p5) → p2)) ∨ ((False → p1) ∧ p1))))))) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157042482910494754493126739745 : (((True ∧ (p3 → ((((p4 ∨ False) ∧ False) → (p1 → (p3 ∧ p3))) → ((p3 ∨ p1) → p2)))) ∨ False) ∨ ((p4 → (p2 ∨ True)) → (p1 → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111563135297576589562138729174 : ((((((p2 ∧ (p1 ∨ (p5 ∧ p1))) ∧ p4) ∧ (p1 → (p1 ∨ ((p5 → p3) → (((False ∨ p1) → p3) → p1))))) ∧ p2) ∨ p2) ∨ (True ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_20465034445536744813910738060 : (((((p1 ∨ p1) → True) ∧ (((False ∧ p4) ∧ (p2 ∧ p2)) ∨ (False → p3))) → ((p3 ∨ (p2 ∨ (p3 → p3))) ∨ ((p4 ∨ p2) → True))) ∧ True) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- False on the left can always be used.
    apply False.elim h7
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h10
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218433246780463865920723814362 : (((p2 ∧ p4) → (p3 → p1)) → ((p1 ∧ p2) → ((p1 → p4) → (p1 → (((False ∧ (p4 ∨ (True ∨ p5))) ∨ (p4 ∧ (p1 → p5))) ∨ p4))))) := by
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
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h7 : p1 := by
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h8 := h3 h7
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135685397050712686844130254318 : ((((p2 ∧ (((p5 ∧ p2) ∧ ((p1 ∧ (p4 ∨ p3)) ∨ p2)) ∧ p5)) ∨ p3) ∧ ((p4 ∧ p4) → ((p1 → True) ∧ False))) ∨ ((p1 → True) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_352832294486235387013885115619 : (p4 → ((p1 → p2) → (p1 → ((((((p3 ∧ (False ∧ ((((p5 → p3) → p1) ∨ p4) ∨ p4))) ∨ p5) → p5) → p3) ∨ (True ∨ p4)) ∧ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37490434477270024676519321364 : ((((((True ∧ p1) ∨ p4) ∨ ((p5 → (p3 → (p1 ∧ ((p5 ∧ (p5 → (p1 ∧ p5))) ∧ True)))) ∨ ((p3 ∨ False) ∨ True))) ∨ p1) ∧ True) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_594542925725641968239752901684 : ((((((p2 ∨ (p3 ∧ p2)) ∨ ((p4 ∧ p5) ∧ ((False ∨ (True ∧ (p4 ∧ p3))) → p1))) ∨ (((True ∧ False) → (p3 → False)) ∧ p3)) ∧ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197154475141296309497295413566 : (((p2 → (p1 → (p3 ∧ (p1 → p1)))) ∨ p5) ∨ ((((True ∨ p2) → p5) ∧ (((p4 ∨ p4) ∧ (True → (False ∧ (p1 ∨ p5)))) ∨ p2)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_75094882886051570249387262357 : (((True → (((p5 ∧ (False ∧ True)) ∨ (((p4 ∧ p5) → ((False → p1) ∧ False)) → ((p1 ∧ (p3 ∧ p4)) ∨ p3))) ∧ (p4 ∧ p2))) ∨ False) → p4) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
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
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- False on the left can always be used.
    apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117034271315934112615569107457 : (((p3 ∨ True) → (False ∧ (p4 ∨ (True → ((p3 ∨ (True ∨ (p4 → (True ∧ p2)))) ∨ ((p4 ∨ (p1 ∨ p5)) ∨ (p3 ∨ p5))))))) ∨ (p2 → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184320508367091812441241301675 : ((((p3 ∨ p5) ∨ (p3 → ((p1 ∧ p3) → (True ∨ False)))) → p5) ∨ (True ∨ ((True ∧ ((p3 ∨ p2) ∧ ((p4 ∧ (p5 ∨ p1)) ∧ p1))) → False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_663502470752114299390004426478 : (((((p4 → p1) → ((True ∧ p2) → ((p4 ∧ True) ∨ (p3 ∨ ((((p2 ∧ p4) → ((True ∧ p3) ∨ p3)) ∨ False) ∧ False))))) → (p2 ∨ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160150955390007513578688930322 : (((((True → (p4 ∧ ((p5 ∧ p1) ∨ ((True ∨ p2) ∧ p3)))) → False) → (p5 → False)) ∧ (p2 → False)) → (((True → p2) ∨ p2) → (p5 ∧ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h1.left
    let h5 := h1.right
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h6 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h7 := h3 h6
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h8 : p2 := by
      -- One of the premise coincides with the conclusion.
      exact h7
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h9 := h5 h8
    -- False on the left can always be used.
    apply False.elim h9
  case inr h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h1.left
    let h12 := h1.right
    -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
    have h13 : p2 := by
      -- One of the premise coincides with the conclusion.
      exact h10
    -- We have shown the premise of h12, we can now drive its conclusion.
    let h14 := h12 h13
    -- False on the left can always be used.
    apply False.elim h14
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168020724732715156521110543932 : (((p5 ∧ (((False ∧ True) ∧ p1) → p5)) ∨ (p5 ∨ ((p3 ∧ ((True ∧ p5) ∧ p1)) ∧ p1))) → ((((True ∧ p2) → True) → (p3 ∧ p1)) ∨ True)) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Conjunctions on the left can always be decomposed.
      let h10 := h8.left
      let h11 := h8.right
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- Conjunctions on the left can always be decomposed.
      let h14 := h12.left
      let h15 := h12.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_203909466794194202260542937171 : ((p1 → (False → ((p3 → p1) ∧ False))) ∧ (p4 → ((p2 ∨ ((p5 ∨ p1) → p5)) → ((True → (p5 ∨ (p2 → p5))) ∨ ((False → p3) ∨ p4))))) := by
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
  -- False on the left can always be used.
  apply False.elim h2
  -- False on the left can always be used.
  apply False.elim h2
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134114915851321630180498927796 : ((((p5 ∨ (p5 ∨ (((p5 ∨ p2) → ((p4 → (p4 → p4)) ∧ ((False ∨ p5) ∧ p5))) ∧ p3))) ∧ (p1 ∧ False)) ∨ True) ∨ (p5 ∨ (p3 ∧ p5))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191460562932435172801558693837 : (((p4 → p1) → (p5 ∨ (p5 ∨ (p4 ∨ (True ∧ p3))))) ∨ ((p4 → ((p3 → p3) ∨ p3)) ∨ (((p5 → (True → True)) → p2) ∧ (p1 ∧ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_957462627169809122985365263276 : ((((True ∨ (p5 ∨ False)) → ((True → (False ∨ ((p2 → p4) ∨ p3))) ∧ ((p4 → ((p3 ∨ (p4 ∨ ((p4 ∧ p1) ∧ True))) ∨ False)) → False))) → p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (True ∨ (p5 ∨ False)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h5 : (p4 → ((p3 ∨ (p4 ∨ ((p4 ∧ p1) ∧ True))) ∨ False)) := by
    -- Implications on the right can always be decomposed.
    intro h6
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h6
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h7 := h4 h5
  -- False on the left can always be used.
  apply False.elim h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60185938562606244627906289609 : (((p5 ∨ p2) → ((p2 ∨ p3) → ((p5 → (((p1 ∨ (((True ∨ p4) → True) ∨ p2)) ∧ p1) ∧ (((p4 ∧ p1) ∧ False) ∨ p1))) ∧ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246751393528333218739875299702 : ((p5 ∧ p5) ∨ ((((p4 → p1) ∧ ((p4 ∨ (p5 → p4)) → p4)) → (p1 ∨ ((p3 ∨ p5) → (p2 ∨ ((p4 ∨ p2) ∧ False))))) ∨ (True ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_646152563009795503764795164164 : ((((False → (((p2 ∧ (((((p1 ∨ p2) ∨ p4) ∨ p5) ∧ (((p4 → (p1 ∨ True)) ∨ False) ∨ False)) ∨ (p5 → p4))) ∨ p4) ∨ False)) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_668723814020678430319813723005 : ((((((((((p2 ∨ p5) ∧ True) → False) ∧ p3) ∨ ((p4 ∧ ((p3 ∨ p3) → (p4 → p2))) ∧ p1)) ∨ True) ∨ p5) ∨ (p1 → (p3 → True))) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_344120086718877872299692346149 : (p2 → (False ∨ (((p5 → p4) ∨ (p4 ∧ (p1 ∧ (p3 ∨ ((p3 ∨ (p4 ∨ ((p4 → p1) ∨ p5))) ∨ (p2 → p4)))))) ∨ ((False → False) ∨ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134738022148738272381397602726 : ((((p4 ∨ p4) ∧ ((p4 ∨ ((((p2 → (p4 ∧ p4)) → ((p4 → p1) ∨ p4)) → (p2 ∧ p4)) ∧ p4)) → p4)) → False) ∨ ((p3 ∧ p4) → p4)) := by
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
theorem thm_5_vars_197689567094111942954871238749 : (((p1 ∨ ((p4 ∨ p1) → p4)) → (p1 ∨ False)) ∨ ((True ∨ (p1 ∧ (p3 ∨ (((p2 → False) ∨ (((p3 ∧ True) ∧ p1) ∨ p1)) → p4)))) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_131283197456494410867034402397 : (((False ∧ (p4 ∨ ((p5 → p3) ∧ p1))) ∨ ((((p5 ∧ p2) → (p1 ∨ ((p5 ∨ (True ∨ False)) ∨ p3))) → False) ∨ True)) ∧ (p3 → (p2 ∨ True))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_957786717460035070100414410097 : ((((p3 ∨ (p2 → p2)) → ((((p5 ∨ True) ∧ False) ∨ ((p1 ∨ ((((True → p2) → p5) ∧ p4) ∨ p4)) ∨ ((p3 ∧ p2) → p2))) ∧ p5)) → p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p3 ∨ (p2 → p2)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- One of the premise coincides with the conclusion.
  exact h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_223430304766754517494039004830 : ((True ∨ (p5 → True)) ∧ (((p2 ∧ False) ∨ (((p2 → (False ∧ (p1 ∨ p4))) ∨ True) ∧ True)) ∨ ((p2 → p5) ∨ (p4 → ((p1 → False) ∧ p4))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347235083270645584125419059658 : (p3 → ((p4 ∧ ((((p1 ∧ True) ∧ ((p3 ∧ p1) ∨ p3)) → p1) ∨ p3)) → (p1 ∨ ((p2 ∧ p1) ∨ (((p5 → (True ∧ p4)) → p3) → p3))))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134824707066558806728807411651 : (((p1 ∨ ((((False ∧ True) → ((p2 ∧ (p3 → (p4 ∧ (False → (p5 → p1))))) → p2)) → (p2 ∧ p3)) ∨ p4)) → p3) ∨ ((False → p5) ∧ True)) := by
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
theorem thm_5_vars_41181087520102632198213168611 : ((((((((p1 → False) ∧ (p3 ∧ False)) → ((p2 → p5) ∧ p5)) ∨ (p4 → (False ∧ p3))) ∨ (p2 ∨ p2)) → (p3 ∨ (p5 → p2))) ∨ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_615212059031186544389597502122 : ((((((p3 ∧ p3) → ((p1 → False) → (((True → p3) → (p2 ∨ p5)) ∨ (p1 ∧ True)))) ∧ ((p2 → (False ∨ (p5 → p4))) ∨ p3)) ∨ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156959082418657507598745005416 : ((((p5 ∧ (((p2 → p4) ∧ p4) ∧ (p5 ∨ ((True ∨ p3) ∧ p5)))) ∨ ((p3 → False) ∧ p4)) ∨ p3) ∨ (p4 ∨ (((True ∧ p5) → p2) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158992628867930636772030548925 : ((p3 ∨ (p1 ∧ (((p5 ∧ (((((p4 → True) ∧ p2) → True) → p5) ∧ p2)) → p3) ∧ (p1 ∧ p5)))) ∨ (p5 ∨ (False → (p1 ∧ (p2 ∨ False))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_342488889599202445636298581677 : (p2 → ((((p1 → p5) ∨ p1) → ((False → p4) → ((True ∧ p2) ∧ (p5 → p5)))) ∨ ((p5 ∧ (((p2 ∨ (p2 ∧ p1)) → p1) → p5)) ∧ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h5 =>
    -- One of the premise coincides with the conclusion.
    exact h1
  -- Implications on the right can always be decomposed.
  intro h6
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h7 =>
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h8 =>
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340439496383949726700623717845 : (p2 → (((((((p1 → p1) ∧ p4) ∧ (p5 → False)) → (True ∧ (p1 ∨ False))) ∨ ((p1 ∧ p5) → True)) ∨ (((p5 ∨ False) → p5) ∧ p4)) ∧ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181228876035276235944602953680 : ((p3 ∧ (((((True ∨ (True ∧ (p4 → p3))) → p1) → p5) ∧ p3) → True)) → (p1 → (p4 ∨ ((False → p4) → (p2 ∨ ((p3 → p1) ∨ p5)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h5
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h6
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199185331177582808067168472464 : (((p2 ∧ (p2 → ((p3 → p2) ∨ p2))) ∧ p1) → ((((((True ∧ False) → p2) ∨ (p1 ∧ p1)) → False) ∧ p3) ∨ (p3 → (p2 ∨ (p2 ∨ p3))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h6
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301626419029242459269349559411 : (False ∨ ((p5 ∧ (True ∨ p2)) → ((((p4 ∧ p5) ∨ ((p2 ∨ (p4 → p4)) ∧ p3)) ∨ False) ∨ (p5 ∨ ((True → (p4 → False)) → (p4 ∨ True)))))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2



