variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_83258881381888240319595862146 : ((((p3 → ((((p4 → ((((p2 → p2) ∧ p5) → False) ∨ True)) → p5) ∧ p4) → p5)) → False) ∧ ((p2 ∨ ((p1 ∨ p5) → p3)) → p5)) → False) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (p3 → ((((p4 → ((((p2 → p2) ∧ p5) → False) ∨ True)) → p5) ∧ p4) → p5)) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- Implications on the right can always be decomposed.
    intro h6
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h9 : (p4 → ((((p2 → p2) ∧ p5) → False) ∨ True)) := by
      -- Implications on the right can always be decomposed.
      intro h10
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h11 := h7 h9
    -- One of the premise coincides with the conclusion.
    exact h11
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h12 := h2 h4
  -- False on the left can always be used.
  apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257913345525492487914282454400 : ((p4 ∨ False) → (((((p1 ∧ True) → (p2 ∨ (p4 ∧ p5))) ∨ (((p1 ∨ (p5 ∨ p1)) → p4) → (p1 → ((p1 ∧ False) ∨ p3)))) → False) ∨ p4)) := by
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
    -- False on the left can always be used.
    apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184484231373639155985960905594 : (((((p3 ∨ p1) → ((p4 ∧ True) ∧ False)) → False) ∨ (p5 → True)) ∨ (((((True ∧ (p3 ∧ (True ∨ p5))) ∧ (p5 ∧ p1)) ∧ p2) ∧ p1) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172670968124829811388737472988 : (((p3 → p2) ∧ ((((p4 ∨ p4) ∧ False) → True) → ((p5 ∨ (False ∨ p3)) → p1))) ∨ (((p3 ∧ (p1 ∧ p3)) ∧ (p4 ∧ (True ∨ True))) → p3)) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h8 := h3.left
  let h9 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h9
  case inl h10 =>
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h11 =>
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231334282338102777218466580995 : (((True → p3) ∨ p3) → (False ∨ (((((False → (p3 ∨ p4)) ∨ False) ∨ False) ∧ ((p1 ∧ (p1 → (True ∧ ((p2 → p4) ∧ p3)))) ∨ True)) ∨ p5))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- False on the left can always be used.
    apply False.elim h5
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346330053337001092912642645087 : (p3 → (((p4 ∨ (((p5 ∧ ((((p5 ∧ p2) ∧ True) → p1) → (p2 ∧ True))) → p4) → p1)) ∨ (((p2 ∨ p3) ∨ p4) → p3)) ∨ (True ∧ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_684708268672644132975722277460 : (((((p2 ∧ p1) ∧ (((p3 → False) → True) → (((((True ∨ p5) ∧ p5) ∧ p5) ∨ p4) → True))) ∨ ((p3 → (p2 ∧ (False ∨ p4))) ∨ True)) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_258507249475041904005395803433 : ((p5 ∨ p2) → (p4 ∨ (p5 → (((p1 ∨ ((p1 ∧ (True ∧ p2)) ∧ ((True → p5) ∧ p1))) ∨ (((p1 ∨ True) ∧ p2) → (p4 ∨ False))) ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208078804696102320694617956758 : (((p1 → (p4 → p1)) ∨ (p1 ∧ p4)) → (p2 → (((False ∨ p2) → p2) → (p2 ∧ (((p2 ∧ p5) ∨ (False ∨ ((p5 ∧ p5) ∨ True))) ∨ p5))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h4 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- One of the premise coincides with the conclusion.
    exact h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h8 =>
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
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
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
theorem thm_5_vars_4026346328356790217906178052 : (p2 ∨ ((False ∧ (((((((False ∨ True) → p1) ∨ p5) ∨ True) ∧ p3) → (p3 ∨ True)) → ((True ∧ p5) ∨ (p4 ∧ (p5 ∨ p2))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198291116106093017011318775563 : ((p1 ∧ (((p1 ∨ (p1 → p4)) → p1) ∧ p3)) ∨ ((False ∧ False) → (((p2 ∨ (p4 ∧ p2)) ∧ True) ∨ ((False ∧ p4) ∨ (True → (False ∨ p3)))))) := by
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
theorem thm_5_vars_339970272172955148487508319434 : (p1 → (p1 → ((p2 ∨ (p5 ∨ (((p5 ∨ p4) ∨ (p5 ∧ (p1 → (p3 → (False → ((p2 ∧ False) ∧ p4)))))) → ((p2 ∨ p3) → p4)))) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65947063162767402861881252225 : ((p4 ∨ (p2 ∨ ((((p1 ∨ False) ∧ (p3 ∨ ((False ∧ (False → p2)) ∨ p1))) → (p2 ∧ False)) ∨ (((p2 → p1) ∧ p4) ∧ (True ∨ p5))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164517694793899122729361547336 : (((((p3 ∧ (p1 ∨ False)) ∧ (p2 ∧ (p3 ∧ ((True → True) ∨ p2)))) ∨ (p5 ∨ False)) ∧ p5) ∨ (p5 → ((p4 ∨ (p2 → p3)) → (p4 → p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h5 =>
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_343427713293672613767494496201 : (p2 → ((p1 ∨ p1) ∨ ((p3 → (p1 ∧ p5)) → ((p2 ∧ (((p5 ∨ False) ∨ p1) ∨ p4)) → ((p3 ∨ (p1 ∧ False)) ∨ (True ∧ (False ∨ p2))))))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- True on the right can always be proven directly.
        apply True.intro
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h4
      case inr h9 =>
        -- False on the left can always be used.
        apply False.elim h9
    case inr h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
  case inr h11 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322239045852372033466732562086 : (p5 ∨ ((((True → (((((p5 ∨ (p2 → (((p4 ∨ p2) → p5) ∧ p5))) ∧ (p1 → (p5 → p3))) → p4) → p4) ∨ p5)) ∧ p2) ∨ p1) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117364442742147946492271864943 : ((False ∧ (p3 ∨ (((((True ∧ ((p3 → p1) → p1)) ∧ (p2 ∧ p5)) ∨ p2) ∨ False) ∧ (((p2 ∨ (p3 ∧ p2)) ∧ True) → p5)))) ∨ (p3 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186274711587800411194763723835 : ((((p4 ∧ ((False → (p1 ∨ False)) ∧ (p3 ∧ p3))) ∨ False) → False) → (((((p4 → p3) ∧ (False ∧ p5)) ∨ p2) ∧ ((True → p3) ∨ p3)) → p3)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- False on the left can always be used.
    apply False.elim h8
  case inr h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h11 =>
      -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
      have h12 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h11, we can now drive its conclusion.
      let h13 := h11 h12
      -- One of the premise coincides with the conclusion.
      exact h13
    case inr h14 =>
      -- One of the premise coincides with the conclusion.
      exact h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257610719050198916618860440306 : ((p3 ∨ p2) → (((((p3 ∧ p4) → (((p5 → (p5 ∨ (p3 ∨ p3))) → p5) ∨ p3)) ∨ (p2 ∨ p4)) ∨ (p1 ∧ ((p2 → True) → p2))) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h6 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184879242011307962322673317289 : (((p4 ∧ (p3 ∧ p5)) ∧ (False → (((p3 ∧ False) ∧ p3) ∧ p1))) ∨ (((p1 ∧ ((((p5 ∧ False) → p3) ∨ False) ∨ p1)) ∧ p2) → (p4 ∨ True))) := by
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
  cases h5
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h8 =>
      -- False on the left can always be used.
      apply False.elim h8
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_325659695541704777710589104315 : (p5 ∨ (False ∨ (p5 ∨ (True ∧ (True → ((p2 ∨ ((p3 → p1) → (False ∨ ((((False ∨ (False ∨ p2)) → p3) → False) ∧ p4)))) ∨ (True ∧ True))))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_196850887974211160336492134547 : (((False ∨ ((p5 ∧ p5) ∨ (False ∧ False))) ∧ p4) ∨ ((False ∧ (False ∧ True)) → (((((p2 → (p5 ∧ p3)) ∨ p2) → (True ∧ True)) ∧ False) ∨ p5))) := by
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
theorem thm_5_vars_765640318971017601472624805983 : (((p4 ∧ (((p2 ∧ False) ∨ (((p3 ∧ True) ∧ (p2 ∨ (p4 → p2))) ∧ True)) ∧ (((((p4 → p1) → p1) → (p5 ∧ p5)) ∧ False) ∨ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347329469408027081129328920557 : (p3 → ((False → ((p5 → p1) → (((False ∧ p5) ∨ False) ∨ False))) → (((p4 ∧ ((p2 ∨ p4) ∨ p1)) ∧ (True → p4)) → (p4 → (p1 ∨ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h12 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178585636781952041653881621424 : ((((((p3 ∧ p1) ∧ False) ∧ False) ∨ p5) ∨ (True → ((False → p5) ∨ False))) ∨ ((p1 ∨ (p4 ∧ ((p4 ∧ p4) ∧ True))) → ((p3 ∨ True) ∧ False))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197734381346248013897039972508 : ((((p4 → p4) ∨ p4) ∧ (p2 ∨ (p1 ∨ p3))) ∨ ((p3 ∨ ((True ∨ (p4 ∨ p2)) → p4)) → (p1 → ((((p4 ∧ p4) ∨ p4) ∨ p2) ∨ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_255278563290163707784439927950 : ((p4 ∧ p5) → (True ∧ ((((p2 → p3) → p3) ∨ (False ∨ (p1 ∧ p3))) ∨ (((p2 ∧ p2) ∨ ((p5 ∧ ((p4 ∧ p1) ∨ True)) ∨ p1)) ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
theorem thm_5_vars_201304324071630939308055962216 : ((p4 → (False ∧ (((p3 ∨ p1) → p4) ∧ p2))) → ((((p1 → p3) ∨ ((p3 → False) ∧ (((p5 ∨ p1) → p2) ∧ p3))) ∧ (p1 ∨ p3)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_709589945682359593812404046379 : ((((p1 ∨ ((p4 ∨ (False ∨ False)) ∨ (p4 ∨ p3))) → ((((False ∨ (p5 → ((((p2 ∨ False) ∧ p2) ∨ True) → p1))) ∨ True) ∨ True) → p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299270649746943571059358490438 : (False ∨ (((p2 ∧ (p5 ∨ ((p4 → ((p2 ∨ (True ∨ (p4 ∨ p2))) ∨ (True → p4))) → p5))) ∨ (p4 → ((True ∧ (p5 → True)) → p4))) ∨ p5)) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115878268807585173429261949220 : ((((False ∨ (p1 ∧ False)) ∧ p4) ∨ ((p1 ∨ (((False ∨ p1) → (True → (p5 ∧ ((False → p2) ∧ p5)))) ∨ p3)) ∨ (p4 ∨ p1))) ∨ (p2 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304080128808571597626645702873 : (p1 ∨ ((p4 ∨ ((p4 ∧ (p1 ∨ (((p1 → p3) ∨ p5) ∨ ((((((True ∧ p1) ∧ p4) → True) → (p2 → p4)) ∨ False) ∧ p1)))) → False)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323243807644550373432987865632 : (p5 ∨ (((p1 ∧ p2) ∨ ((p5 ∧ (((p3 → p1) ∨ (p1 ∧ (p1 → p4))) ∨ (((p5 ∧ p5) ∨ True) → (p2 → False)))) ∨ True)) ∨ (p5 → True))) := by
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
theorem thm_5_vars_60201848815439898629584158056 : (((p5 ∨ p5) → ((((p3 ∧ (p4 → p4)) → p1) ∧ p4) ∧ ((((p5 ∨ True) ∨ p5) ∨ (False ∧ (p2 → False))) ∧ (p3 → (p3 → False))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199545145793607649829354661470 : ((((p4 ∧ (p4 → (p3 ∧ False))) ∧ p4) → p2) → (((((False ∨ ((True ∧ (p2 → p2)) ∨ True)) → False) ∨ p4) ∨ p2) ∨ (p2 ∨ (True ∨ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_607873665567542064497809910600 : (((((True → ((p3 → (p2 → (((True ∧ p5) → ((p4 → p4) ∧ p4)) ∨ ((p4 ∧ p5) ∨ p5)))) ∧ (p3 → (p5 ∨ p5)))) ∧ p4) ∨ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_619358316891831186167929003825 : ((((((p1 ∨ p1) → p1) → (False ∨ (p4 ∧ ((p1 ∨ ((False ∧ (((p5 → (p2 ∨ p3)) → True) ∨ p4)) ∧ (p4 ∧ p1))) ∨ True)))) ∨ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232019236924551549818070590509 : (((p3 ∨ True) → p2) → ((False ∧ (p5 ∨ ((False ∧ (p3 ∨ p4)) ∧ (p2 ∨ p4)))) ∨ (((((False ∨ p5) ∧ p3) ∧ (True → p5)) → p2) ∨ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h7 =>
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h9 : (p3 ∨ True) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h6
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h10 := h1 h9
    -- One of the premise coincides with the conclusion.
    exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171678851040792601585925132791 : (((p1 ∨ (p1 ∨ (p3 → ((p3 ∨ False) ∧ (p5 → ((p1 → p4) → p1)))))) ∨ False) ∨ ((True ∧ (((p3 ∧ (p1 ∧ p4)) ∨ p1) ∨ True)) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_804327396397576513344829238803 : (((p3 → ((p2 ∧ (((p2 ∨ (p5 ∨ (p4 ∨ p1))) ∧ (p3 → True)) → False)) ∧ ((False ∧ p2) ∨ ((p5 ∧ ((False → True) → p4)) ∨ p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_806186363613282113617310257438 : (((p4 → (((p3 ∨ ((p5 → ((((p1 ∧ ((p3 ∨ p5) ∧ p1)) ∧ (p4 → p5)) ∧ (p5 ∧ p1)) ∨ p1)) ∨ (True ∨ p4))) ∨ p1) ∨ p3)) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118088202550757346737470553048 : ((False ∨ ((((((p1 ∧ True) ∧ ((((((True ∨ (p5 ∨ p2)) → p2) → False) ∧ p1) → True) ∨ True)) ∧ p4) → p5) ∧ p5) ∧ True)) ∨ (True ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113844268492215221237533096911 : (((p4 ∨ (p1 ∧ (((False ∨ (p4 ∨ p4)) ∨ (p3 ∧ (p3 → (p5 → (p1 → ((p3 ∧ True) ∨ p2)))))) ∨ p2))) → (p2 ∧ p1)) ∨ (True → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_326890028636033532818734524309 : (True → (((p4 ∧ (((p2 → (False → p5)) ∧ p1) → (True → (False ∧ (False ∨ ((((p3 ∨ p4) ∧ p3) ∧ (p1 ∨ p4)) ∧ p3)))))) ∨ p1) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112899175948943192757162595549 : ((((p4 → p3) ∧ (((((p5 ∨ p3) ∧ True) ∨ (p1 → (p1 ∧ True))) ∨ False) → (((p5 → (False → True)) ∧ p5) ∨ p2))) → False) ∨ (p1 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191933824778236102514638742990 : ((True → ((p1 ∨ ((True ∨ p1) → False)) ∨ (p2 ∧ p2))) ∨ ((((p5 → False) ∨ ((p3 → p4) → p1)) → (p1 → True)) ∨ (True ∧ (True ∨ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45362682990283737141388040765 : (((p4 ∧ ((((True ∧ ((p5 ∧ (p3 ∨ p3)) ∧ p4)) ∧ True) → p5) ∧ ((((p1 → p1) → False) ∨ p2) → (False → (p4 → p3))))) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_325151514867489245113858501759 : (p5 ∨ (True ∧ ((p4 → (((p2 ∧ False) → False) ∧ (p2 ∧ p2))) ∨ (((p1 ∧ (True ∧ p3)) ∧ p1) → ((p4 ∧ p1) → ((p5 ∧ p5) ∨ True)))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h1.left
  let h6 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- Conjunctions on the left can always be decomposed.
  let h9 := h8.left
  let h10 := h8.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_757461185400777048413015130057 : (((p1 ∧ (True ∧ (p1 → (True ∧ (((((p5 ∧ (False → (p3 ∧ (p4 ∧ p5)))) ∨ (p1 → (p4 ∨ p3))) ∧ (p4 → p3)) ∨ False) → p4))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350351813704065880106745468341 : (p4 → ((p4 → (((True ∨ False) ∨ (p4 ∨ p3)) → (((p4 → p3) ∨ (((p2 ∨ True) ∨ p1) ∧ p5)) ∨ (((p5 ∧ False) → p4) ∧ True)))) ∨ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
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
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- False on the left can always be used.
      apply False.elim h8
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h9 =>
      -- False on the left can always be used.
      apply False.elim h9
  case inr h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h12
      -- Conjunctions on the left can always be decomposed.
      let h13 := h12.left
      let h14 := h12.right
      -- False on the left can always be used.
      apply False.elim h14
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h15 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h16
      -- One of the premise coincides with the conclusion.
      exact h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48869954165965354213711261125 : (((p5 ∨ ((p4 ∨ (False ∨ p1)) → ((((True ∧ (((True ∧ p3) → p4) → p3)) → (True ∧ p1)) ∨ p2) ∨ False))) ∧ (p1 ∧ (p5 ∨ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321291993991673133915377358643 : (p4 ∨ (p5 ∨ (((p1 ∨ ((p2 → (p3 ∧ ((((p3 ∨ ((False ∧ p4) ∧ ((p3 ∨ p5) ∧ False))) ∧ p3) ∨ True) ∧ p1))) ∧ p1)) ∨ True) ∨ False))) := by
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
theorem thm_5_vars_726581763039204333258084130834 : (((((True ∧ p3) → p4) ∨ (((((p3 → (((p1 ∧ (p5 → ((p3 ∨ p5) ∧ p1))) ∨ p4) → False)) ∨ p5) ∧ (p5 ∧ p4)) ∧ p4) ∨ True)) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_891956734779913577384253283493 : (((((p3 → ((True ∧ (p1 ∨ (p2 ∧ ((((p3 ∧ True) ∧ (p5 ∨ p2)) ∧ p2) ∧ (p1 ∧ p2))))) ∧ False)) ∧ p2) ∧ ((p5 ∧ p4) ∧ p3)) → False) ∧ True) := by
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
  let h8 := h6.left
  let h9 := h6.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h10 : p3 := by
    -- One of the premise coincides with the conclusion.
    exact h7
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h11 := h4 h10
  -- We need to get the right conjuct of h11 based on <expert-advice>.
  let h12 := h11.right
  -- False on the left can always be used.
  apply False.elim h12
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_194040320460167811980550391645 : ((p5 ∨ ((p3 ∧ (((p1 → p1) ∧ p1) → True)) → p5)) → (p1 → (((p4 ∧ (False ∧ p3)) ∨ (p3 → (((p3 ∨ p1) → p4) ∨ True))) ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65606379617850820580129066559 : ((p4 ∨ (((p3 ∨ (p4 → True)) → ((p4 → (((p2 ∨ (True ∨ p1)) ∨ False) ∨ ((((p3 ∧ p3) ∧ False) ∨ p4) ∨ p4))) ∧ p2)) ∧ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_216141412707928301657627428032 : ((True → (p5 → (p4 ∧ p1))) ∨ (((p5 ∧ p2) ∨ p3) → (((True → ((((True ∧ p3) ∧ False) ∨ True) → p5)) → (p5 ∧ (False ∨ p5))) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h6 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h7 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h8 := h2 h7
    -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
    have h9 : (((True ∧ p3) ∧ False) ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h8, we can now drive its conclusion.
    let h10 := h8 h9
    -- One of the premise coincides with the conclusion.
    exact h10
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h12
  case inr h14 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h15 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h16 := h2 h15
    -- We want to use the implication h16 based on <expert-advice>. So we show its premise.
    have h17 : (((True ∧ p3) ∧ False) ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h16, we can now drive its conclusion.
    let h18 := h16 h17
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h18
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191246748362742725871410943639 : (((p1 ∧ True) ∧ (p5 ∨ (False → (False → (p1 ∧ p4))))) ∨ ((p1 → (p2 ∨ (((((p3 → (p1 → p2)) ∨ p2) ∧ True) ∧ p1) ∨ p1))) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180061584802606808498465032889 : (((True → ((((False ∧ (p2 → True)) → (False ∨ p3)) ∨ False) → False)) ∨ False) → ((((False → (((p3 → p4) → p3) ∨ True)) → p4) ∨ p2) ∨ p4)) := by
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
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h5 : (((False ∧ (p2 → True)) → (False ∨ p3)) ∨ False) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h6
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- False on the left can always be used.
      apply False.elim h7
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h9 := h4 h5
    -- False on the left can always be used.
    apply False.elim h9
  case inr h10 =>
    -- False on the left can always be used.
    apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_619020291008148187501157760372 : ((((((p1 → p4) ∨ p3) ∨ (False ∧ (p2 ∧ (p1 → ((p2 ∨ (((False → (p5 → p3)) → (False ∨ (p4 ∨ p4))) ∨ p1)) ∧ p3))))) ∨ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_786272007030958533439148407179 : (((p4 ∨ (((False ∧ p1) ∧ ((p4 ∨ ((p5 → False) ∧ False)) → (p3 ∨ (((True ∨ p2) ∨ True) ∨ True)))) ∨ ((p2 ∨ (False → p1)) ∨ False))) ∨ p4) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184024737514588056379350079718 : (((((p1 → (p5 ∧ ((False → p3) → p5))) ∧ True) → False) ∨ p1) ∨ ((p3 → (p1 → (p2 ∨ True))) ∨ (p4 → ((p2 ∨ (p1 → p2)) ∨ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133072641010946051259818117592 : ((True → ((((p5 ∨ (p3 → (True ∨ True))) → False) ∨ (p2 ∨ (p1 ∨ ((p2 → p4) ∨ True)))) ∨ (p2 → (p3 ∧ p4)))) ∧ ((True ∧ p4) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191285590322282278649820876234 : (((p4 ∨ p5) ∧ (((p3 → (True ∨ p5)) ∨ p4) → p5)) ∨ (p3 ∨ ((True ∨ (False ∧ ((p5 ∧ False) → ((p1 → (True ∨ p1)) → p5)))) ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181477268893110795511578891417 : ((p4 ∨ (True ∧ (((p1 ∨ (p3 → False)) ∧ p4) ∨ (p4 ∨ (True ∨ p5))))) → ((p4 ∨ p3) → ((False ∨ (p3 → True)) ∨ ((False → True) ∧ p1)))) := by
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h5
      -- True on the right can always be proven directly.
      apply True.intro
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
        -- Disjunctions on the left can always be decomposed.
        cases h10
        case inl h12 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h13
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h14 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h15
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h16 =>
        -- Disjunctions on the left can always be decomposed.
        cases h16
        case inl h17 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h18
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h19 =>
          -- Disjunctions on the left can always be decomposed.
          cases h19
          case inl h20 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h21
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h22 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h23
            -- True on the right can always be proven directly.
            apply True.intro
  case inr h24 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h25 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h26
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h27 =>
      -- Conjunctions on the left can always be decomposed.
      let h28 := h27.left
      let h29 := h27.right
      -- Disjunctions on the left can always be decomposed.
      cases h29
      case inl h30 =>
        -- Conjunctions on the left can always be decomposed.
        let h31 := h30.left
        let h32 := h30.right
        -- Disjunctions on the left can always be decomposed.
        cases h31
        case inl h33 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h34
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h35 =>
          -- We want to use the implication h35 based on <expert-advice>. So we show its premise.
          have h36 : p3 := by
            -- One of the premise coincides with the conclusion.
            exact h24
          -- We have shown the premise of h35, we can now drive its conclusion.
          let h37 := h35 h36
          -- False on the left can always be used.
          apply False.elim h37
      case inr h38 =>
        -- Disjunctions on the left can always be decomposed.
        cases h38
        case inl h39 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h40
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h41 =>
          -- Disjunctions on the left can always be decomposed.
          cases h41
          case inl h42 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h43
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h44 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h45
            -- True on the right can always be proven directly.
            apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245089013906004496583077321962 : ((p1 ∧ p5) ∨ (p1 → (p1 ∧ (((p4 ∧ (p5 ∨ p5)) ∨ (False ∨ True)) ∨ (p2 → (((p3 → True) ∧ p1) ∨ (p4 ∨ (p3 ∨ (False ∨ p5))))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62600830100624703948032597317 : ((p3 ∧ (p5 → ((p2 ∧ (((p3 ∧ (((False → (True ∨ (p2 ∨ False))) → p1) → p3)) ∨ p1) ∧ (p1 → ((True ∧ True) ∨ p3)))) ∨ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_666316215749493068731094863992 : ((((((True → ((p3 ∨ p2) → (p4 ∧ ((p5 ∧ ((True → False) ∨ p4)) ∨ p1)))) ∧ True) ∧ (False ∨ (p2 ∨ p4))) ∧ ((False ∨ p3) → p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_783644282994635574856323369803 : (((p3 ∨ (((p2 ∨ p4) → (((p4 ∨ p1) ∨ False) ∧ p3)) ∨ (((p5 ∨ (False ∧ (((p1 ∨ p4) → p4) ∧ p5))) ∧ (p1 ∨ p5)) → p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321082979781402360782698117939 : (p4 ∨ (p1 ∨ ((p3 → True) ∧ (((False → False) → p2) → (((p5 ∨ p1) ∧ False) ∨ ((p1 → (p3 ∨ (((True → p2) ∨ p3) → p2))) ∧ True)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h6 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h7 := h5 h6
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h8 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h9 : (False → False) := by
      -- Implications on the right can always be decomposed.
      intro h10
      -- False on the left can always be used.
      apply False.elim h10
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h11 := h2 h9
    -- One of the premise coincides with the conclusion.
    exact h11
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197589654340322208507867906568 : (((p4 ∧ (p4 ∨ (False ∨ p5))) ∨ (p2 → p4)) ∨ ((False ∧ p2) ∨ (((p5 ∨ (((p5 → p5) ∨ p1) ∧ (p4 → p1))) ∧ (p4 ∧ False)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179048953371877946410308948789 : (((p2 → p5) → (p3 ∨ (((((False → False) → p1) ∧ True) → p5) ∧ p1))) ∨ ((True ∨ (((p3 ∨ p3) ∧ ((p1 ∧ False) ∨ p4)) ∨ False)) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_754524614010610263606921845094 : (((False ∧ (False ∧ (p1 → ((((((p4 ∨ p5) ∧ p1) → (p4 ∨ p2)) ∨ ((p1 ∧ False) ∨ (p5 → p2))) ∧ p1) ∨ (p2 ∨ (p5 ∨ False)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351753033287303759942994597782 : (p4 → (((p2 → (p4 → ((((False ∧ True) ∨ True) → True) ∧ (p5 ∧ p1)))) ∨ p5) → (p2 ∨ (p1 → ((p5 → (p2 ∨ (p4 → p3))) ∨ p4))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173245588864842343373234423067 : ((True → (True ∧ (((((p3 → (p2 ∨ p5)) → (p3 ∨ p5)) → True) → p5) ∨ p1))) ∨ (((p2 ∨ (True → p4)) → (True ∨ True)) ∨ (p4 ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49018023005694844166354229143 : (((((((True ∧ False) ∧ (p5 → (((p5 ∧ True) ∨ (False ∨ True)) → (p4 ∨ p2)))) ∧ True) → (p5 ∧ True)) → p4) ∨ (p4 → (False ∧ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351895533113133606905801644928 : (p4 → ((((p1 ∧ (p5 → (p2 → (p3 ∨ p2)))) ∨ True) ∧ False) ∨ (p4 ∧ (p4 → (False ∨ ((p4 → p5) → (((p5 ∨ p1) ∧ p3) ∨ True))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_182514687998989142674217436267 : (((((False → p3) ∨ p5) ∧ (p1 ∨ (p1 ∧ p5))) → (True ∧ True)) ∧ ((p3 → ((((p4 → (True ∧ p1)) → (True → p4)) ∧ p5) ∨ p3)) ∨ p2)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65981650653241603452232005785 : ((p4 ∨ (p1 → (((p3 → p4) ∨ p1) ∧ (((p2 ∧ p1) ∧ ((p5 → p3) ∨ (False ∨ p1))) ∨ ((p2 → (p3 ∧ p4)) ∨ (p2 → p4)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190886597735533693659626626484 : ((((p1 → True) → ((p5 ∧ p4) → p2)) → (False ∧ p3)) ∨ (((p4 ∨ p2) ∧ (p1 ∨ (((p3 ∧ p3) ∨ p5) ∧ (p3 → p1)))) → (p5 ∨ True))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h9 =>
        -- Conjunctions on the left can always be decomposed.
        let h10 := h9.left
        let h11 := h9.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h12 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h12
  case inr h13 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h14 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h15 =>
      -- Conjunctions on the left can always be decomposed.
      let h16 := h15.left
      let h17 := h15.right
      -- Disjunctions on the left can always be decomposed.
      cases h16
      case inl h18 =>
        -- Conjunctions on the left can always be decomposed.
        let h19 := h18.left
        let h20 := h18.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h21 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h21



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_326282343485789176954245773975 : (p5 ∨ (p4 → (((p4 → p2) ∨ ((((p1 ∨ (((False → p3) ∧ p3) ∨ p3)) → p2) ∨ True) ∧ (p5 → (False ∨ (True → (p3 ∨ p1)))))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_339800809932674635998580229540 : (p1 → (p5 ∨ ((False ∨ (((((p3 → p5) ∧ (p2 ∧ False)) → (p5 ∨ ((p4 ∧ p5) ∧ p4))) → (p2 ∨ p4)) ∧ p3)) ∨ ((p4 → p4) ∨ p3)))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_21796076290278591109891068721 : (((p3 → (p4 → (p2 ∨ (False → ((p5 ∨ False) ∧ p4))))) → ((p1 ∨ (p5 ∧ (p1 ∧ (p5 ∧ False)))) ∨ (p4 ∨ (p4 ∨ (False → True))))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149149619845393346060542837895 : (((False ∨ p3) ∧ (((False ∨ p5) ∨ p3) ∧ ((p3 ∨ ((p2 → (p1 → p2)) ∨ p4)) → (p5 ∨ (True ∨ p1))))) ∨ (True ∨ (p4 ∧ (p4 ∧ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186412254005621520980887279325 : (((p2 ∨ (((p2 → p5) ∧ p2) ∨ (p5 ∨ (False → p2)))) → False) → (p4 ∧ (True ∧ ((p1 → p2) ∨ (False ∨ ((p5 → (p5 ∧ p5)) ∧ p3)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p2 ∨ (((p2 → p5) ∧ p2) ∨ (p5 ∨ (False → p2)))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- False on the left can always be used.
  apply False.elim h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h5 : (p2 ∨ (((p2 → p5) ∧ p2) ∨ (p5 ∨ (False → p2)))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- False on the left can always be used.
    apply False.elim h6
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h7 := h1 h5
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181211734018327363309945175657 : ((p2 ∧ ((p2 → p4) ∧ ((((p4 ∨ False) ∧ (p2 → False)) ∨ p3) ∨ p2))) → ((True → (((p4 ∨ True) → (p3 ∧ True)) ∨ (True ∨ p2))) ∨ p5)) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h10 =>
        -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
        have h11 : p2 := by
          -- One of the premise coincides with the conclusion.
          exact h2
        -- We have shown the premise of h9, we can now drive its conclusion.
        let h12 := h9 h11
        -- False on the left can always be used.
        apply False.elim h12
      case inr h13 =>
        -- False on the left can always be used.
        apply False.elim h13
    case inr h14 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h15
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h16 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h17
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48569641963181741613857045183 : (((((p4 ∨ p1) ∨ ((p1 ∨ (((p2 ∨ (p2 ∨ (p3 → (False ∧ p2)))) → p3) ∧ p1)) ∨ (p5 ∨ p3))) → p4) ∧ (p5 ∧ (p3 ∨ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_398268223705682260968639816207 : ((((p5 ∨ ((((((p1 ∨ ((p4 ∨ ((True ∨ p4) → p2)) → ((p3 ∨ p5) → (p5 ∧ p3)))) ∧ p3) ∨ p4) ∧ False) → p3) → p4)) ∨ True) ∧ True) ∧ True) := by
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
theorem thm_5_vars_315706997373839276054606266321 : (p3 ∨ ((p4 ∨ p2) ∨ (((p4 → p2) ∨ (False ∧ (p5 ∧ ((p4 → False) ∨ p3)))) → (p4 ∨ ((((p3 ∧ False) ∧ p2) ∨ p3) ∨ (True ∧ True)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
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
  case inr h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- False on the left can always be used.
    apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213432576231383498886763747470 : (((p4 ∨ (p1 ∧ p1)) ∧ p2) ∨ ((((False ∨ p3) ∧ ((((((p3 ∧ p1) ∨ p2) → p2) ∨ False) ∧ p2) ∧ (p1 ∨ False))) ∧ p3) ∨ (False → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47409092456863917337353837085 : (((False ∧ (((p2 ∧ ((p1 ∧ p2) ∧ (((True ∨ p3) ∨ p3) → ((p2 ∨ False) ∧ (False ∨ p4))))) ∧ p2) ∧ (True ∨ p2))) ∨ (True ∨ p5)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_902820381663922785517170181962 : (((((p1 ∨ (False → False)) → (p2 ∧ (p5 ∨ (((p1 ∨ ((p1 ∧ p2) ∨ True)) ∨ p2) ∨ (True → p2))))) ∧ (p2 ∧ ((p1 → p4) → p4))) → p2) ∧ True) := by
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
  -- One of the premise coincides with the conclusion.
  exact h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_88706929649387036265654825117 : (((((False ∨ p3) → p3) ∨ True) → ((p2 ∧ ((p1 ∨ p5) ∧ (p2 ∧ p3))) ∧ ((p3 ∧ (p1 → p5)) → (p3 ∧ (True ∨ (p1 ∧ p1)))))) → p3) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((False ∨ p3) → p3) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the left conjuct of h3 based on <expert-advice>.
  let h4 := h3.left
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319532537757065372595443790419 : (p4 ∨ ((p3 → ((False → True) → (p2 → (p5 → (p1 ∨ True))))) ∧ ((((p2 ∧ p2) ∨ p3) ∧ True) ∨ ((True ∨ ((p1 ∨ p5) → p3)) ∨ True)))) := by
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
theorem thm_5_vars_619607034070348897195064721496 : (((((p1 ∧ p3) ∧ ((p1 ∧ (p3 → (((p1 ∧ (False ∨ p1)) ∨ (p1 ∧ p5)) ∨ True))) → ((False ∨ (p2 ∨ (False ∨ p2))) ∨ p5))) ∨ True) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_206245401084029356927162275043 : ((False ∨ ((p5 ∧ (p2 ∧ p2)) ∧ p1)) ∨ ((p3 ∨ (p4 → ((p2 ∧ False) → ((p5 ∧ False) → (((p5 ∧ p1) ∧ True) → (True ∧ p4)))))) ∨ p3)) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- Conjunctions on the left can always be decomposed.
  let h9 := h3.left
  let h10 := h3.right
  -- False on the left can always be used.
  apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112476982516544756224186363077 : (((((p1 → p5) ∧ (((p1 ∨ ((p3 ∧ (p3 ∧ p2)) ∨ p4)) → (p4 ∧ p3)) ∧ (p4 ∨ ((p2 → p4) ∨ p2)))) ∨ p3) → p3) ∨ (p2 → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232442256630736292566117389663 : ((True ∧ (p4 ∧ p4)) → (((((p3 ∧ ((((p2 → p4) ∧ ((p3 → (p2 → False)) ∨ p1)) ∨ (True ∧ p3)) ∧ p2)) ∨ True) ∧ p1) ∨ p1) ∨ True)) := by
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
theorem thm_5_vars_809376952242832337878759933485 : (((p5 → ((p2 → (((p2 ∧ (False ∧ p2)) ∧ p2) ∨ ((p2 ∧ ((False ∨ (p4 → (p2 ∨ (p4 → (p4 → p3))))) ∧ p2)) → p4))) ∨ p5)) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257532663409701770484980757240 : ((p3 ∨ False) → (p1 ∨ (((((True ∨ p1) → False) ∧ ((((False → p5) → False) ∧ p4) ∨ (p2 ∨ p4))) → (p4 → False)) ∧ (p2 ∨ (p3 ∨ p5))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the left can always be decomposed.
    let h5 := h3.left
    let h6 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h10 : (True ∨ p1) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h11 := h5 h10
      -- False on the left can always be used.
      apply False.elim h11
    case inr h12 =>
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
        have h14 : (True ∨ p1) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h5, we can now drive its conclusion.
        let h15 := h5 h14
        -- False on the left can always be used.
        apply False.elim h15
      case inr h16 =>
        -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
        have h17 : (True ∨ p1) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h5, we can now drive its conclusion.
        let h18 := h5 h17
        -- False on the left can always be used.
        apply False.elim h18
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h19 =>
    -- False on the left can always be used.
    apply False.elim h19



