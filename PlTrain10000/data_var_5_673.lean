variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190277134441993733398887530834 : ((((p5 ∧ ((p5 ∨ p5) ∨ (True ∧ p4))) ∨ p5) ∨ True) ∨ (True → ((p4 ∧ p2) → (((p2 → (((p2 → p5) → p2) → p2)) → p4) ∨ p2)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219076638858880441936265797409 : ((p5 ∧ (False → (p2 ∨ p4))) → ((True → p2) → (((p3 ∨ (p3 ∧ p1)) → p3) → (p2 ∧ (((False ∧ p4) ∨ (False ∨ True)) ∧ (p1 → True)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h6 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h7 := h2 h6
  -- One of the premise coincides with the conclusion.
  exact h7
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h8 := h1.left
  let h9 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h10
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_797632583132655215328057412066 : (((p1 → ((((((False ∧ p1) → p3) ∧ (p5 ∧ True)) → False) → (p1 ∧ (True → (p1 → (p2 ∨ (p4 → ((True → True) → False))))))) → p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2185441027621934264752565306 : (((False ∧ ((False ∨ (True ∧ (p2 ∧ p1))) ∨ ((p5 ∨ p5) ∨ p5))) ∨ (p2 ∧ p2)) ∨ (((p4 → (p2 → True)) ∨ (True → p4)) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_633640765043561294153161087977 : ((((((False → p2) ∨ (((p1 → (p3 ∧ (p2 ∨ ((p5 → False) ∧ ((False ∧ p2) ∧ (p5 → p3)))))) ∧ p5) ∧ p2)) ∨ (p2 → False)) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157353623873846304838839928261 : (((True → ((p2 ∨ True) → (((p1 ∧ p4) ∨ True) → ((False → True) → ((p2 ∨ p5) ∧ p2))))) → p1) ∨ (p5 → ((p5 ∨ (True → p2)) ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40122132637061788283309159640 : (((((((p5 ∧ (p2 → p3)) ∧ ((p3 → (p2 → (p5 ∨ True))) ∧ (True ∧ p1))) → (True ∧ p3)) ∧ ((False → True) ∨ p5)) ∧ False) ∨ True) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68362866737651868198424736870 : ((p3 → ((p2 → (p5 ∧ ((False ∨ p4) ∨ (p3 ∧ p4)))) → (p2 ∧ ((True ∧ p4) → ((p5 ∧ (((False ∨ p3) → p1) ∨ False)) → p3))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_730319717438644150539325011968 : (((((p5 → True) → False) → ((False ∨ ((((False ∨ (p2 → (False ∨ (p2 ∧ False)))) → p1) ∧ p3) → (p2 ∨ p5))) ∨ ((p2 ∧ p2) ∨ p5))) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p5 → True) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- False on the left can always be used.
  apply False.elim h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137458496950686372337825770962 : ((p4 ∧ ((False → p3) → ((p3 ∨ True) ∧ (((p2 ∧ ((p4 ∧ True) → False)) → p4) → ((p4 → True) ∧ (p2 ∨ p4)))))) ∨ (p5 → (p5 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_613584825952060730700187741794 : (((((((p1 ∨ (((p5 ∧ (p3 ∧ False)) → (((p2 ∨ p1) → (p3 ∧ p1)) → p4)) ∨ p3)) ∨ p4) → False) ∧ ((True ∧ p4) ∧ p3)) ∨ True) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_135206900808833067751437123090 : (((((p5 ∨ (p3 ∧ (p5 → True))) → ((p1 ∨ ((False → (p5 ∧ p5)) ∨ False)) → p4)) → (True ∨ p1)) → (p4 ∨ p4)) ∨ ((p3 → p1) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59332355655681485868997926217 : (((p4 ∨ p4) ∨ (True → ((((False ∧ (p2 → (True ∨ (p4 ∨ (p1 → (((p2 ∧ p4) → p5) → True)))))) ∨ (p2 ∧ p1)) ∨ False) ∨ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_261663213835646626417749036814 : ((p5 → p5) → (p2 ∨ (((p4 ∧ p1) ∨ (p5 ∧ ((True ∨ False) ∧ p2))) ∨ ((((p3 → p4) ∧ ((p4 ∨ p1) ∨ p3)) → p1) ∨ (False → True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_141080467267376963312541121917 : (((p1 ∨ ((True → p4) → (p3 ∧ (True → p3)))) ∨ (p5 → ((True ∧ (((False ∧ (p5 ∨ p4)) ∧ p5) → p2)) ∧ p3))) → (p5 ∨ (p3 ∨ True))) := by
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
theorem thm_5_vars_137732713603482004190354723018 : ((p1 ∨ (p2 ∨ ((p4 ∧ (False ∨ (False ∨ ((p4 ∨ (p1 ∧ False)) ∨ (True ∨ (True → p2)))))) ∨ (False ∨ (p1 ∧ p2))))) ∨ ((False → p4) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_752938215799539782915607186797 : (((False ∧ ((((True ∧ (p5 ∧ ((True ∨ (p1 ∧ p2)) ∧ p2))) ∧ (True ∨ (p4 ∧ (True ∨ ((p5 ∧ p5) → p4))))) ∨ (p5 → p2)) → p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207679171313804586898766756962 : ((((False ∧ p4) → (p3 → p5)) → p5) → (((True → p1) ∨ (p3 ∨ p4)) → (p1 → ((((p4 ∧ p3) ∨ (p3 ∨ p5)) ∧ (p1 ∨ p1)) ∨ False)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h5 : ((False ∧ p4) → (p3 → p5)) := by
      -- Implications on the right can always be decomposed.
      intro h6
      -- Implications on the right can always be decomposed.
      intro h7
      -- Conjunctions on the left can always be decomposed.
      let h8 := h6.left
      let h9 := h6.right
      -- False on the left can always be used.
      apply False.elim h8
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h10 := h1 h5
    -- One of the premise coincides with the conclusion.
    exact h10
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h12
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h13 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h14 : ((False ∧ p4) → (p3 → p5)) := by
        -- Implications on the right can always be decomposed.
        intro h15
        -- Implications on the right can always be decomposed.
        intro h16
        -- Conjunctions on the left can always be decomposed.
        let h17 := h15.left
        let h18 := h15.right
        -- False on the left can always be used.
        apply False.elim h17
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h19 := h1 h14
      -- One of the premise coincides with the conclusion.
      exact h19
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115690777998740557564313410610 : (((p5 ∨ ((p5 ∧ False) ∨ (p2 ∧ p4))) ∨ ((((p5 ∨ (p5 ∨ p2)) ∧ (((True ∨ (p2 ∨ p2)) → False) ∧ p2)) → p2) ∨ p2)) ∨ (p1 ∧ p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    let h5 := h3.left
    let h6 := h3.right
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h3.left
      let h10 := h3.right
      -- One of the premise coincides with the conclusion.
      exact h10
    case inr h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h3.left
      let h13 := h3.right
      -- One of the premise coincides with the conclusion.
      exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256884651596154481070846406256 : ((p1 ∨ p4) → ((p5 ∨ ((((p1 → p3) → ((p5 → p3) ∧ (((p2 ∧ (True → p2)) → p5) ∧ (True ∨ p2)))) ∨ False) ∧ (p3 ∧ p1))) ∨ True)) := by
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
theorem thm_5_vars_343827567125804871820975176314 : (p2 → (p2 ∧ (((False → ((p2 ∨ p4) → True)) → p4) → ((((False ∨ False) ∨ p4) ∨ (p2 ∧ (((False → p1) ∧ False) ∨ False))) ∧ (p5 ∨ p2))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (False → ((p2 ∨ p4) → True)) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h6
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149609315470883012755788598967 : ((p3 ∧ ((p2 ∧ False) ∨ ((p4 → True) → (((((p3 → p1) → p3) ∧ (p1 ∨ p3)) ∧ p5) → (p4 → False))))) ∨ (True → (p4 ∨ (True ∨ p5)))) := by
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
theorem thm_5_vars_60412616236209228333276286156 : (((p4 → p1) → (((((p2 ∨ (((p5 → (p2 ∨ (p2 ∨ p2))) ∧ (p5 → ((True ∨ p4) ∧ False))) ∨ p3)) → True) ∨ p4) → p1) ∧ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51605874205386769157868449310 : (((p5 → ((False ∨ ((p4 → p5) → (p1 ∨ p3))) ∧ ((p3 ∧ (p3 → p4)) ∧ (True ∨ True)))) → (p3 → (False ∧ (p1 ∨ (p3 ∨ p2))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354790016780070685195841770094 : (p5 → ((((True → ((p3 ∧ p2) → p3)) → p2) ∧ ((((p4 ∨ (p2 ∧ False)) ∧ (p4 ∨ p4)) ∨ (False ∧ ((p3 ∨ p4) ∧ p2))) ∧ True)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314966297051209085829114910675 : (p3 ∨ ((p3 ∨ ((True → False) ∨ ((p3 → p5) ∧ (True ∧ p1)))) → (((p2 ∧ p3) ∨ (p1 ∧ ((((p5 ∨ False) ∨ p1) ∧ False) → p2))) ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h5 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h6 := h4 h5
      -- False on the left can always be used.
      apply False.elim h6
    case inr h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h11
      -- Implications on the right can always be decomposed.
      intro h12
      -- Conjunctions on the left can always be decomposed.
      let h13 := h12.left
      let h14 := h12.right
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h15 =>
        -- Disjunctions on the left can always be decomposed.
        cases h15
        case inl h16 =>
          -- False on the left can always be used.
          apply False.elim h14
        case inr h17 =>
          -- False on the left can always be used.
          apply False.elim h17
      case inr h18 =>
        -- False on the left can always be used.
        apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_823205089619072666790466691859 : (((((((True → True) → False) ∧ (False → False)) ∧ (p4 → (True → ((p1 → (p3 ∨ (((p4 ∧ p2) ∨ (p1 ∧ p2)) ∨ p5))) → True)))) ∧ True) → p5) ∧ True) := by
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
  let h6 := h4.left
  let h7 := h4.right
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h8 : (True → True) := by
    -- Implications on the right can always be decomposed.
    intro h9
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h10 := h6 h8
  -- False on the left can always be used.
  apply False.elim h10
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346873115493313529273130990313 : (p3 → ((((p1 ∧ p4) ∨ (True ∨ (p4 ∨ (p4 ∨ p1)))) → ((p3 ∧ ((False → p2) → p1)) ∨ p3)) ∧ (p1 → (((False ∧ p1) → p2) ∧ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h1
      case inr h10 =>
        -- Disjunctions on the left can always be decomposed.
        cases h10
        case inl h11 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h1
        case inr h12 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h1
  -- Implications on the right can always be decomposed.
  intro h13
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h14
  -- Conjunctions on the left can always be decomposed.
  let h15 := h14.left
  let h16 := h14.right
  -- False on the left can always be used.
  apply False.elim h15
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66279947021391049465783554010 : ((p5 ∨ ((p3 → (p5 ∧ False)) → (((p5 ∨ p1) → (((p4 → True) ∨ (p4 → (True ∧ (False ∨ p1)))) → (p5 ∧ (p3 ∧ p5)))) ∨ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199480643003788352213954218923 : (((p3 ∨ ((p1 ∨ p5) ∨ (True ∧ p4))) ∨ p4) → (((p5 ∨ (p3 ∨ p4)) ∧ (p1 ∨ (p3 → (p1 → p3)))) → ((p2 ∨ (p5 → True)) ∨ True))) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h7 =>
        -- Disjunctions on the left can always be decomposed.
        cases h7
        case inl h8 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h9 =>
          -- Disjunctions on the left can always be decomposed.
          cases h9
          case inl h10 =>
            -- Disjunctions on the left can always be decomposed.
            cases h10
            case inl h11 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- True on the right can always be proven directly.
              apply True.intro
            case inr h12 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- True on the right can always be proven directly.
              apply True.intro
          case inr h13 =>
            -- Conjunctions on the left can always be decomposed.
            let h14 := h13.left
            let h15 := h13.right
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
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h18 =>
        -- Disjunctions on the left can always be decomposed.
        cases h18
        case inl h19 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h20 =>
          -- Disjunctions on the left can always be decomposed.
          cases h20
          case inl h21 =>
            -- Disjunctions on the left can always be decomposed.
            cases h21
            case inl h22 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- True on the right can always be proven directly.
              apply True.intro
            case inr h23 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- True on the right can always be proven directly.
              apply True.intro
          case inr h24 =>
            -- Conjunctions on the left can always be decomposed.
            let h25 := h24.left
            let h26 := h24.right
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
      case inr h27 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h28 =>
    -- Disjunctions on the left can always be decomposed.
    cases h28
    case inl h29 =>
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h30 =>
        -- Disjunctions on the left can always be decomposed.
        cases h1
        case inl h31 =>
          -- Disjunctions on the left can always be decomposed.
          cases h31
          case inl h32 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h33 =>
            -- Disjunctions on the left can always be decomposed.
            cases h33
            case inl h34 =>
              -- Disjunctions on the left can always be decomposed.
              cases h34
              case inl h35 =>
                -- Show the right disjunct based on <expert-advice>.
                apply Or.inr
                -- True on the right can always be proven directly.
                apply True.intro
              case inr h36 =>
                -- Show the right disjunct based on <expert-advice>.
                apply Or.inr
                -- True on the right can always be proven directly.
                apply True.intro
            case inr h37 =>
              -- Conjunctions on the left can always be decomposed.
              let h38 := h37.left
              let h39 := h37.right
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- True on the right can always be proven directly.
              apply True.intro
        case inr h40 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h41 =>
        -- Disjunctions on the left can always be decomposed.
        cases h1
        case inl h42 =>
          -- Disjunctions on the left can always be decomposed.
          cases h42
          case inl h43 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h44 =>
            -- Disjunctions on the left can always be decomposed.
            cases h44
            case inl h45 =>
              -- Disjunctions on the left can always be decomposed.
              cases h45
              case inl h46 =>
                -- Show the right disjunct based on <expert-advice>.
                apply Or.inr
                -- True on the right can always be proven directly.
                apply True.intro
              case inr h47 =>
                -- Show the right disjunct based on <expert-advice>.
                apply Or.inr
                -- True on the right can always be proven directly.
                apply True.intro
            case inr h48 =>
              -- Conjunctions on the left can always be decomposed.
              let h49 := h48.left
              let h50 := h48.right
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- True on the right can always be proven directly.
              apply True.intro
        case inr h51 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
    case inr h52 =>
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h53 =>
        -- Disjunctions on the left can always be decomposed.
        cases h1
        case inl h54 =>
          -- Disjunctions on the left can always be decomposed.
          cases h54
          case inl h55 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h56 =>
            -- Disjunctions on the left can always be decomposed.
            cases h56
            case inl h57 =>
              -- Disjunctions on the left can always be decomposed.
              cases h57
              case inl h58 =>
                -- Show the right disjunct based on <expert-advice>.
                apply Or.inr
                -- True on the right can always be proven directly.
                apply True.intro
              case inr h59 =>
                -- Show the right disjunct based on <expert-advice>.
                apply Or.inr
                -- True on the right can always be proven directly.
                apply True.intro
            case inr h60 =>
              -- Conjunctions on the left can always be decomposed.
              let h61 := h60.left
              let h62 := h60.right
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- True on the right can always be proven directly.
              apply True.intro
        case inr h63 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h64 =>
        -- Disjunctions on the left can always be decomposed.
        cases h1
        case inl h65 =>
          -- Disjunctions on the left can always be decomposed.
          cases h65
          case inl h66 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h67 =>
            -- Disjunctions on the left can always be decomposed.
            cases h67
            case inl h68 =>
              -- Disjunctions on the left can always be decomposed.
              cases h68
              case inl h69 =>
                -- Show the right disjunct based on <expert-advice>.
                apply Or.inr
                -- True on the right can always be proven directly.
                apply True.intro
              case inr h70 =>
                -- Show the right disjunct based on <expert-advice>.
                apply Or.inr
                -- True on the right can always be proven directly.
                apply True.intro
            case inr h71 =>
              -- Conjunctions on the left can always be decomposed.
              let h72 := h71.left
              let h73 := h71.right
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- True on the right can always be proven directly.
              apply True.intro
        case inr h74 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260293683349154840163787168277 : ((p2 → p4) → ((((p1 → p3) ∧ ((p3 → (p2 ∧ (False ∨ (True → (p3 ∨ (p5 → (p5 ∨ (p3 → p4)))))))) ∧ p5)) → p2) ∨ (p2 → p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : p2 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_803428300514495573377581839109 : (((p3 → ((p3 → (((p1 ∨ ((p2 → ((p3 ∧ (True ∨ p5)) ∧ True)) ∨ ((p5 ∨ p4) ∨ p5))) ∨ (True → p3)) → (p5 ∧ p2))) ∨ True)) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_204665149320507149079690222681 : (((p5 ∧ ((p2 → p2) → False)) ∨ p4) ∨ (((p3 ∨ True) → (((True ∧ (p2 → (p4 → (False ∧ (True ∨ (True → p5)))))) ∨ p4) ∨ p3)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260341700864059927420661504319 : ((p2 → p5) → (((p2 → (p3 ∧ (p4 ∨ (((((p5 ∨ p5) → True) → p1) → ((p1 ∨ True) ∧ (p4 ∧ (p3 ∨ False)))) ∧ p1)))) ∧ p2) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_262261761300304316138091951188 : (True ∧ (((((p3 ∧ ((p1 ∨ (p1 ∧ p4)) ∨ (True → (p5 ∧ (p5 ∨ True))))) ∧ ((p2 → True) → False)) → True) → ((True → False) ∧ False)) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112343239278293763973427839863 : (((p5 → ((p5 → (p5 → (p4 → ((True ∨ ((p5 → p5) ∧ p2)) ∨ p3)))) → ((p4 ∧ (p3 → (p5 → False))) ∨ p4))) ∨ True) ∨ (p5 ∨ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_241274205199819871760216994661 : ((False → True) ∧ ((((p1 ∨ (((p3 ∨ p3) ∨ (True ∧ (p2 ∧ (p2 ∨ ((p3 → p4) → True))))) → p1)) → False) ∨ (p2 → (p5 ∨ p5))) ∨ True)) := by
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
theorem thm_5_vars_183800410973967681860144291333 : ((((((p5 ∨ p2) ∨ p1) ∧ (p2 → (False ∧ True))) ∨ p3) ∧ p1) ∨ (((False → False) → False) ∨ ((True ∧ (p2 ∧ True)) → ((p3 ∧ True) → p2)))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h5 := h1.left
  let h6 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h6.left
  let h8 := h6.right
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_102710272146957490444662138010 : ((((((p2 ∧ ((p5 → (True ∧ (False ∨ p5))) ∨ p4)) ∧ True) → ((True ∨ p3) ∧ (False ∧ (False → (True → p2))))) ∨ p5) ∨ True) ∧ (True ∧ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53811129054922079759468218160 : ((((((p4 → True) → (p1 ∨ p4)) ∧ False) ∧ (p5 ∧ p5)) ∨ (((p3 ∧ p4) → False) ∨ ((p3 ∧ p5) → (p4 ∨ (p5 ∨ (False ∨ p5)))))) ∨ p1) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_678809929211867561379849250750 : ((((True ∧ (p3 → (p4 ∨ (((p3 → (p4 ∨ (p4 → (p1 ∧ (True → True))))) ∨ p2) ∧ (p1 → p5))))) ∨ (p3 → ((False ∧ False) ∨ True))) ∨ False) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_758650238467765289107964317396 : (((p2 ∧ ((((((p4 → p5) ∧ p2) → (p5 ∨ p5)) ∧ (p5 → (False → (p3 → p4)))) ∨ (((False ∧ p4) ∧ p1) ∧ (p5 ∨ p2))) ∨ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115267518025326642037422424741 : (((p1 ∧ (((p4 ∨ p5) ∧ (False ∧ (p4 ∧ p5))) ∨ p2)) ∨ (((p3 → False) ∨ ((p5 → p1) → (p5 ∨ True))) ∧ (False ∨ p5))) ∨ (True ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_96862198680041566123965952621 : ((p1 ∨ (((p1 ∨ (False → (True ∨ (p1 ∨ ((False → False) ∧ (p1 → p2)))))) → p1) ∧ (p5 → (p4 ∧ (True ∧ ((p1 → p3) → p1)))))) → p1) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h6 : (p1 ∨ (False → (True ∨ (p1 ∨ ((False → False) ∧ (p1 → p2)))))) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h7
      -- False on the left can always be used.
      apply False.elim h7
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h8 := h4 h6
    -- One of the premise coincides with the conclusion.
    exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_262354807591768456103232010722 : (True ∧ ((((True → p3) → p3) ∧ (((False ∨ ((((p5 ∧ (((False ∨ True) ∨ p4) ∨ (True ∨ False))) → p4) ∨ True) → False)) ∨ p2) ∨ True)) ∨ p5)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338159405463038242409677535744 : (p1 → (((((p3 ∨ False) ∧ p2) ∨ (p1 ∧ True)) → p2) → ((False ∨ (((True → ((p3 → False) ∨ p5)) ∨ (True ∧ (True → True))) ∨ p4)) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_81917097645894152754330375272 : ((((((((True ∧ (p1 ∨ (False ∧ p5))) → True) → ((False ∧ p2) ∨ p3)) → True) → p3) ∨ ((True → p2) ∨ True)) → ((p1 → p2) ∧ p2)) → p2) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((((((True ∧ (p1 ∨ (False ∧ p5))) → True) → ((False ∧ p2) ∨ p3)) → True) → p3) ∨ ((True → p2) ∨ True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341067699470795166756355555408 : (p2 → ((p4 ∨ (False ∨ (((p2 ∧ False) ∨ (p1 ∨ (p2 ∧ ((p1 ∨ ((False ∧ p4) ∧ p2)) ∧ ((p1 → p4) ∨ (p5 ∧ p1)))))) ∨ False))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_120690280852800894157480340769 : ((((((((False → ((p5 ∨ True) ∧ (p2 → False))) → p5) ∨ False) ∨ p4) ∧ (p1 ∨ (p2 → (p5 ∨ p1)))) ∧ (False → p3)) ∨ True) → (p3 ∨ True)) := by
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
    cases h5
    case inl h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Disjunctions on the left can always be decomposed.
        cases h6
        case inl h9 =>
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
        -- False on the left can always be used.
        apply False.elim h11
    case inr h12 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h13 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h14 =>
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
theorem thm_5_vars_64967802185193938762789395407 : ((p2 ∨ (((p5 ∧ p1) ∨ (p2 ∨ (p4 ∧ p2))) ∨ ((False ∨ p4) → ((p3 ∧ ((p3 → (True → p5)) ∨ (p5 ∨ (p3 ∨ p1)))) → p3)))) ∨ p5) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h6 =>
      -- False on the left can always be used.
      apply False.elim h6
    case inr h7 =>
      -- One of the premise coincides with the conclusion.
      exact h3
  case inr h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h10 =>
        -- False on the left can always be used.
        apply False.elim h10
      case inr h11 =>
        -- One of the premise coincides with the conclusion.
        exact h3
    case inr h12 =>
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- Disjunctions on the left can always be decomposed.
        cases h1
        case inl h14 =>
          -- False on the left can always be used.
          apply False.elim h14
        case inr h15 =>
          -- One of the premise coincides with the conclusion.
          exact h13
      case inr h16 =>
        -- Disjunctions on the left can always be decomposed.
        cases h1
        case inl h17 =>
          -- False on the left can always be used.
          apply False.elim h17
        case inr h18 =>
          -- One of the premise coincides with the conclusion.
          exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42610258045674036644323224789 : (((p3 ∨ ((p1 ∧ (p2 ∧ (((((True ∧ p4) ∨ ((False → (p5 ∧ p2)) → True)) ∧ (p1 → False)) ∨ (p2 → False)) ∧ p3))) ∨ True)) ∨ p3) ∨ p2) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197088723590551164547684806892 : (((p2 ∧ (((p4 ∧ p4) ∧ p4) ∨ False)) ∨ True) ∨ ((((p2 → (True → p2)) ∨ p2) ∨ ((p3 ∧ True) → p5)) ∧ (p3 ∧ (p1 → (p3 → True))))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_640859321657460463984691852741 : (((((p4 → True) ∧ ((((False ∧ p1) ∨ (p2 → ((((p2 ∧ p4) ∨ (False ∧ (True ∨ False))) ∨ p1) ∧ p3))) ∨ True) → (p3 ∧ p4))) → False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214618138733203007022861303963 : (((True → p3) ∧ (p1 → False)) ∨ (False ∨ (((p5 ∨ (p2 → (p5 ∧ p3))) ∨ (True → ((((p2 ∨ p2) → p1) ∧ p3) ∨ (True ∨ p3)))) ∨ p5))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351913435854020596513562079304 : (p4 → (((p2 ∧ p1) ∨ ((((p2 → False) ∨ p3) ∧ p2) ∧ p2)) ∨ (p4 → ((((((p4 ∨ p1) → p2) → p2) ∧ False) ∧ True) → (p3 ∨ p3))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_75733082838625463205287884045 : (((((p4 → ((p1 → ((((p2 ∨ (True → p3)) → False) → ((p3 → p1) → p2)) → p4)) ∨ (p1 → True))) → (p2 ∧ p5)) ∨ True) → False) → p4) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p4 → ((p1 → ((((p2 ∨ (True → p3)) → False) → ((p3 → p1) → p2)) → p4)) ∨ (p1 → True))) → (p2 ∧ p5)) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322386427277829065486386858618 : (p5 ∨ (((True → ((p5 → (p1 ∧ p1)) → (((p1 ∨ (p4 ∧ (p2 ∧ p3))) ∨ True) ∧ p3))) ∨ ((p1 ∨ (p1 ∨ (False → p4))) → p3)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134486804538687789088741486837 : (((((p4 ∧ (p1 → ((p3 → (((True ∧ ((p2 ∧ p1) ∨ (p1 → p5))) → True) → p4)) ∧ p2))) ∨ True) ∨ p1) → p2) ∨ (False → (False ∧ p1))) := by
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
theorem thm_5_vars_41147502724843853041185530055 : (((((p1 ∧ (p3 ∨ (False ∨ p5))) ∧ (p3 ∨ ((p1 ∨ ((p3 → p1) ∧ True)) ∧ (p2 ∧ (p5 → p4))))) ∨ (p5 ∧ (False ∨ True))) ∨ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187352127205631641785674634456 : ((p2 ∧ (p3 → ((((True ∧ p3) → False) ∨ p5) ∨ (p4 → p1)))) → (((p2 ∧ (p4 → False)) → (p3 ∨ p3)) ∨ (False → ((p1 ∧ p5) ∧ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h4
  -- False on the left can always be used.
  apply False.elim h4
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190372050507703952687201642446 : ((((p5 ∨ p1) ∨ (p2 ∧ (p4 ∧ (p5 ∨ p2)))) ∨ True) ∨ (True → (((((p4 ∧ True) → p5) ∧ ((False ∧ p3) ∨ p3)) ∨ p3) → (p1 ∨ p2)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_89192325184820477488515852726 : ((((p2 → p4) → False) ∧ (((p4 ∨ ((p1 ∨ ((p4 ∨ p4) ∨ True)) ∧ p4)) → (p2 ∧ True)) → ((True ∧ p4) ∧ ((True → p2) ∧ p2)))) → p2) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (p2 → p4) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h6 : ((p4 ∨ ((p1 ∨ ((p4 ∨ p4) ∨ True)) ∧ p4)) → (p2 ∧ True)) := by
      -- Implications on the right can always be decomposed.
      intro h7
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- One of the premise coincides with the conclusion.
        exact h5
      case inr h9 =>
        -- Conjunctions on the left can always be decomposed.
        let h10 := h9.left
        let h11 := h9.right
        -- Disjunctions on the left can always be decomposed.
        cases h10
        case inl h12 =>
          -- One of the premise coincides with the conclusion.
          exact h5
        case inr h13 =>
          -- Disjunctions on the left can always be decomposed.
          cases h13
          case inl h14 =>
            -- Disjunctions on the left can always be decomposed.
            cases h14
            case inl h15 =>
              -- One of the premise coincides with the conclusion.
              exact h5
            case inr h16 =>
              -- One of the premise coincides with the conclusion.
              exact h5
          case inr h17 =>
            -- One of the premise coincides with the conclusion.
            exact h5
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h18 := h3 h6
    -- We need to get the left conjuct of h18 based on <expert-advice>.
    let h19 := h18.left
    -- We need to get the right conjuct of h19 based on <expert-advice>.
    let h20 := h19.right
    -- One of the premise coincides with the conclusion.
    exact h20
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h21 := h2 h4
  -- False on the left can always be used.
  apply False.elim h21



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_252885437350296356223364301625 : ((True ∧ p1) → ((False ∧ (p3 ∨ ((((((False → (((False ∧ (p5 → p2)) ∧ p3) → p4)) ∨ p4) ∨ p2) ∨ p5) ∧ p2) → p4))) ∨ (False ∨ True))) := by
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
theorem thm_5_vars_638586323421098512970171852456 : (((((False ∨ (p3 ∨ (False ∨ (p4 ∨ p1)))) ∨ ((p4 → (p2 ∨ p3)) ∧ ((p2 → False) → (p3 ∨ (p3 ∧ ((p2 ∧ p2) ∨ True)))))) → False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_699365772219554250759062421342 : ((((((p2 → p5) → (((p1 ∨ p5) ∧ (False ∨ p5)) ∧ True)) ∧ p2) → (p2 → (((p3 ∧ (False → (p1 → p4))) → p1) → (p3 ∨ p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231489336248326151105231095910 : (((p3 → p3) ∨ False) → (p1 ∨ ((True → p3) ∨ ((((p1 ∨ (((p4 → True) ∧ (p4 ∧ p4)) ∨ (True ∨ p4))) ∨ (True ∨ False)) ∨ True) ∨ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
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
  case inr h3 =>
    -- False on the left can always be used.
    apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165264100759823181903915671859 : ((((((p5 ∧ ((True ∧ (p5 ∨ (p1 ∨ p3))) ∨ p1)) → p3) → p5) ∨ p5) → (False ∧ True)) ∨ (False ∨ (True ∨ ((p3 ∧ p3) → (p2 ∨ False))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199147882759501250468231270846 : ((((False ∨ p1) ∨ ((p1 → p4) → p1)) ∧ p3) → ((p5 ∨ p2) → ((((p2 ∨ (((p2 ∨ (p4 → p3)) ∨ p4) ∧ p5)) ∨ True) → p1) ∨ p3))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- False on the left can always be used.
        apply False.elim h7
      case inr h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h5
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5
  case inr h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h1.left
    let h12 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h13 =>
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h14 =>
        -- False on the left can always be used.
        apply False.elim h14
      case inr h15 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h12
    case inr h16 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_716797037121314368948789940229 : ((((False ∧ ((p2 ∨ p4) ∧ p5)) ∧ (p1 → ((p3 ∨ (p4 ∨ (p4 ∧ ((p2 ∧ (p5 ∧ False)) ∧ ((p2 ∨ p2) ∨ (p5 ∧ True)))))) → p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64820101809227714499342172709 : ((p2 ∨ (((p5 ∧ ((True ∨ p4) ∧ (((p2 ∧ (((p2 → p5) ∧ p2) ∧ p1)) ∨ (p1 ∨ False)) ∨ ((p5 ∨ False) ∧ p4)))) → p4) → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166984997625594687819175719045 : (((p1 ∨ ((((((True → p5) ∨ p4) → True) → ((p2 ∧ False) → p4)) ∨ True) → True)) ∧ p4) → (((p3 ∨ p2) ∧ (p5 ∨ p1)) ∨ (p3 → p4))) := by
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
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342453745780469365105172785851 : (p2 → ((((p1 ∧ False) ∧ (((p5 → p1) ∧ p4) ∨ False)) ∨ (p3 → (True ∧ p2))) ∧ ((((p2 → p4) → p3) → ((p2 → True) ∧ True)) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173292570508178152269113486448 : ((p1 → (((p2 ∨ p5) → (p3 → ((p4 → (False ∨ p1)) ∨ (p2 ∧ p3)))) → p2)) ∨ (p5 → ((p1 ∨ (p2 ∨ p5)) ∨ ((True ∧ p2) ∨ p4)))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62481729852806737075629264469 : ((p3 ∧ ((p2 ∨ True) → (p5 ∧ (False ∨ ((False ∧ ((p4 ∨ False) ∧ True)) ∨ (p2 ∧ ((True ∧ (p2 ∧ (False ∨ (p1 ∨ p3)))) ∧ p1))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38799663855436245124834644649 : ((((p2 → (p4 ∧ (True ∨ False))) ∨ (((p2 ∨ (p5 → p2)) → p1) → (((p4 → (((p5 → p3) ∨ p2) ∨ p3)) ∧ p3) → p3))) ∧ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148044745364470424496787194865 : (((p1 ∧ (((p5 ∧ p1) → (((((p1 ∧ p3) → (p3 → p4)) ∧ p3) → p1) ∧ p5)) → p1)) ∨ (p4 → p1)) ∨ ((p2 ∧ False) → (False ∨ p3))) := by
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
theorem thm_5_vars_40142268506325268279290705393 : (((((((p3 ∧ True) → ((True → (((p3 → False) → p4) → p3)) ∨ False)) ∧ False) ∧ ((True ∧ (p3 ∨ (p4 ∨ False))) ∨ p2)) ∧ p3) ∨ True) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51470223698789372627391158120 : ((((p1 ∨ (((True ∨ p3) ∨ True) ∧ (False ∧ False))) ∧ (p1 → ((p5 ∨ (p3 ∧ p1)) → p5))) → (p2 ∧ (p3 → (p3 → (p2 ∧ False))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184135601153273939400937915416 : (((p3 ∧ ((p5 ∧ p1) ∧ ((p2 → p2) → (p1 ∨ True)))) ∨ p1) ∨ ((p4 → (((p3 ∧ True) ∨ p4) ∨ (p1 → (p3 → p3)))) ∨ (True ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47067014701606987331715929504 : (((((True ∨ p1) ∧ ((((p3 ∨ ((p5 → p3) ∧ True)) ∨ ((p3 → p2) ∧ p5)) → p1) ∨ (p3 ∨ True))) ∨ (p2 ∧ p5)) ∨ (p5 → p3)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135372398095827178053842703186 : ((((True → (((p1 → (((p1 ∨ p1) → (p2 ∨ True)) ∨ p5)) ∨ True) ∨ (True → False))) ∧ p5) ∨ (p4 ∨ (p1 ∨ True))) ∨ ((p4 ∨ p2) → p4)) := by
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
theorem thm_5_vars_355840832686923050807104199544 : (p5 → ((((((p5 → (p4 ∧ False)) → ((p4 → (p4 ∨ ((p4 → p5) ∧ (p4 ∨ p4)))) ∧ p2)) ∨ p5) ∧ p2) → p3) ∨ (p3 → (p4 → p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_734661674856003687994228952736 : ((((p1 ∨ p4) ∧ ((((False → True) ∨ (False → (p2 ∨ True))) → p5) ∧ ((p2 ∨ ((((p3 ∧ p1) ∨ True) ∨ p4) ∧ p5)) ∧ (True → p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52196490082722099008018518107 : ((((False ∧ (p4 → p3)) ∨ (p4 ∨ (False ∨ (((False ∨ p2) ∨ p3) → (p5 ∨ p5))))) → (True → ((p4 → ((p2 → True) ∧ p4)) → p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134504006937281209529681943346 : ((((((p1 ∧ p3) → (p2 ∧ p4)) ∨ (p1 ∧ (p2 ∧ ((((p4 → p2) → True) ∨ True) ∧ (p1 → False))))) ∨ p1) → p3) ∨ (True ∨ (p4 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46939013048152743109323268326 : ((((p5 ∧ (((p4 ∧ (p2 ∧ ((p3 ∧ False) ∧ False))) ∧ p4) ∧ (p3 ∨ ((False ∨ (p1 ∧ (p2 ∧ p2))) ∨ p2)))) ∨ p2) ∨ (p5 → True)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_261470451017630805312890480778 : ((p5 → p2) → ((p5 ∨ p4) ∨ (((True → (((p5 ∧ (p3 → (p2 ∧ p5))) → (p2 → (p2 → True))) ∧ p1)) → (p3 ∧ (p1 ∨ p1))) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137672133893053088339493958501 : ((False ∨ (p1 → ((True ∧ False) ∧ ((False ∧ ((p4 ∨ p4) ∧ ((p5 ∧ (p2 → (p2 ∨ True))) ∧ (True → False)))) ∨ p3)))) ∨ ((False ∧ p2) → p4)) := by
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
theorem thm_5_vars_47514802946669028947768368871 : (((p2 ∨ (p3 ∨ (p4 ∧ (((p4 → (p2 → ((p4 ∨ True) ∧ p3))) → (p2 ∨ p2)) ∨ ((p4 ∧ p3) ∨ (False → p2)))))) ∨ (False ∧ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_763767763235504572538101653258 : (((p3 ∧ (p1 ∨ (p3 → ((p1 ∨ (((p5 ∨ (False → True)) ∨ ((p3 ∨ p2) ∨ (p2 → p1))) ∧ ((True ∨ (True → p4)) ∧ p5))) → False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112751003748926981614625810445 : ((((p3 ∧ ((p1 ∨ (p2 ∧ ((p4 → p1) ∧ (True → False)))) ∨ False)) → ((p1 ∨ (True ∧ (p2 ∧ (p3 ∧ p3)))) ∧ False)) → p2) ∨ (False ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199386726287911062730631268675 : ((((p1 ∧ (p3 → False)) → (p4 ∨ False)) ∨ False) → ((p3 ∧ (p5 → (False ∨ (p3 ∨ ((False → True) → (False ∨ (True ∧ False))))))) ∨ (False → p4))) := by
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
    -- False on the left can always be used.
    apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303062971057167290024659776238 : (False ∨ (p2 → (((p5 → (((p4 ∨ p3) ∧ True) ∨ (p4 → ((True ∨ p3) ∨ (p1 → p3))))) → p4) ∨ (p2 ∨ (p4 ∨ (p3 ∨ (p3 → p2))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_196575356513693570955341192940 : ((p4 → ((((p1 ∨ p3) ∨ True) ∨ p1) ∨ p5)) ∧ (((p3 ∨ (((p4 ∧ (p4 ∨ p5)) ∨ (p2 ∨ (p3 ∨ True))) ∨ False)) → (p2 ∧ False)) → False)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (p3 ∨ (((p4 ∧ (p4 ∨ p5)) ∨ (p2 ∨ (p3 ∨ True))) ∨ False)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
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
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68809923163526341226895808014 : ((p4 → (((p5 → False) ∧ (False → p4)) → (p1 ∧ (p2 ∧ (p2 ∨ (p4 ∨ ((p4 ∧ (p1 ∨ (p4 ∨ (True → (p4 → p3))))) → p5))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_693189492964535630238834175909 : ((((False ∨ (((p1 → p1) ∧ ((p3 → ((False → p3) ∨ True)) ∧ True)) ∨ True)) ∧ (((p1 → ((p5 ∧ p2) ∨ (p5 → p1))) → p1) ∨ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117201552079173136657597310455 : ((True ∧ (((p1 ∨ p3) ∨ (p2 ∨ ((p4 ∧ p3) ∨ (p2 ∧ p5)))) ∧ (p5 ∧ ((p2 → ((p4 → False) ∧ p1)) ∧ (False ∧ p2))))) ∨ (p1 → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257366489268722754203481400901 : ((p2 ∨ p5) → (((p5 → ((((p3 ∨ ((p4 ∨ (p2 → p5)) ∧ ((p4 → p1) → (p1 → p2)))) ∨ False) → True) → (p5 ∧ p3))) ∨ True) ∨ p5)) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_723239876747591150303615020391 : (((((p2 → p4) ∨ True) ∧ (((p5 → p2) ∧ (True ∧ (((p4 ∧ p5) ∨ p1) → (True → False)))) → (False ∧ ((p4 → False) ∧ (p4 → p2))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43785925638326965241374278367 : ((((p2 ∨ (((False → p2) → p5) → (p5 ∧ (((((p3 → False) ∨ (p5 ∨ (p2 ∧ (p3 → False)))) ∧ False) → True) ∨ p1)))) → p5) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



