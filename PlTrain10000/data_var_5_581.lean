variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258957926409159734964707282496 : ((True → p3) → (((((True ∨ ((False → True) ∨ (False ∧ p3))) → p4) → ((p2 → p1) ∨ True)) → (p4 ∨ (False → (p4 ∧ p1)))) ∨ (p2 → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134239528279228917269694213874 : ((((p2 ∨ ((p5 ∧ p1) ∨ p4)) ∨ (p2 ∧ ((((p3 ∧ p5) → ((p1 ∨ (p2 ∧ False)) → p3)) → p1) → p2))) ∨ p5) ∨ ((True ∧ True) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315924223458107962904788531529 : (p3 ∨ (True ∧ (p1 ∨ (((p4 → p2) → (p5 ∨ ((False ∧ (((True → True) → p1) ∧ (p5 → p4))) ∨ ((True ∨ False) ∨ p3)))) ∨ (p5 ∨ p5))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
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
theorem thm_5_vars_193723553279225217747155627247 : ((p2 ∧ ((True → (False ∨ p4)) → (p5 → (p3 → p1)))) → ((((p5 ∧ p4) → ((True ∧ (p2 → True)) ∨ (False → (p4 → p1)))) → p3) → p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h5 : ((p5 ∧ p4) → ((True ∧ (p2 → True)) ∨ (False → (p4 → p1)))) := by
    -- Implications on the right can always be decomposed.
    intro h6
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Implications on the right can always be decomposed.
    intro h9
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h10 := h2 h5
  -- One of the premise coincides with the conclusion.
  exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66220204182303558645859848212 : ((p5 ∨ (((p5 ∨ (p4 → (True ∧ (True → p2)))) → (p1 ∨ p3)) ∧ (p1 → ((((False ∨ p4) → (p2 ∨ False)) ∨ p3) ∧ (p1 ∨ p3))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165623923618698645680188747061 : ((((p4 ∨ ((p4 ∨ p5) ∨ p3)) ∨ p5) ∧ (p4 → (p5 ∧ (((True ∨ p3) ∧ p4) ∨ p5)))) ∨ ((p4 ∨ p5) ∨ ((p4 ∨ (p5 ∨ p2)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158966144867410019064255637793 : ((p3 ∨ (((p4 ∨ ((p4 ∧ ((p5 ∧ (False → p5)) → (p2 ∨ True))) → p2)) ∨ (True ∨ p2)) ∧ False)) ∨ (p3 → (p3 ∨ ((p2 ∨ p5) → p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234405915843606773223335780871 : ((p1 → (p3 → p5)) → ((p4 → (p3 → (p4 → p2))) ∨ (((p3 ∨ (True → p1)) ∨ (((p3 ∧ (p2 ∨ False)) ∨ (p2 ∧ p1)) ∨ True)) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_188696367036230006571287072185 : (((p5 → (p1 → ((False ∨ p1) ∧ p5))) ∨ (p3 → p2)) ∧ ((p4 ∧ (p4 → False)) ∨ ((p5 ∧ (p1 ∨ p2)) ∨ ((True ∨ False) ∧ (False → p5))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_699563240201583156585462033219 : (((((((False ∧ (p1 ∧ ((p1 ∧ False) ∨ True))) ∨ True) ∧ False) → True) → (((False ∨ (p1 ∧ ((p2 → p3) ∨ (p3 → False)))) ∨ False) ∨ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323249122995415558366403418843 : (p5 ∨ (((p2 → p1) → (((((p1 ∧ (True ∧ ((p2 ∨ (p5 → (p1 ∧ False))) ∨ p2))) ∨ p4) → p3) ∨ (False ∧ True)) ∧ p5)) ∨ (True ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308451555667491822656638480640 : (p2 ∨ (((((p1 ∨ (p3 → p2)) ∧ False) ∨ (((p2 ∨ (((p1 ∧ False) ∧ False) → ((p1 ∧ p3) ∧ p2))) → p2) ∨ p5)) ∧ (p3 → p3)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173529623067920780789793383797 : (((((p3 ∨ ((p2 → False) ∨ p1)) ∧ p2) ∧ (p1 ∨ ((p2 → True) ∨ False))) ∧ p4) → ((p5 ∧ p3) ∨ (p5 → ((p4 ∧ p2) ∨ (p5 → False))))) := by
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
  cases h6
  case inl h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h3
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h13
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h3
        -- One of the premise coincides with the conclusion.
        exact h7
      case inr h14 =>
        -- False on the left can always be used.
        apply False.elim h14
  case inr h15 =>
    -- Disjunctions on the left can always be decomposed.
    cases h15
    case inl h16 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h17 =>
        -- We want to use the implication h16 based on <expert-advice>. So we show its premise.
        have h18 : p2 := by
          -- One of the premise coincides with the conclusion.
          exact h7
        -- We have shown the premise of h16, we can now drive its conclusion.
        let h19 := h16 h18
        -- False on the left can always be used.
        apply False.elim h19
      case inr h20 =>
        -- Disjunctions on the left can always be decomposed.
        cases h20
        case inl h21 =>
          -- We want to use the implication h16 based on <expert-advice>. So we show its premise.
          have h22 : p2 := by
            -- One of the premise coincides with the conclusion.
            exact h7
          -- We have shown the premise of h16, we can now drive its conclusion.
          let h23 := h16 h22
          -- False on the left can always be used.
          apply False.elim h23
        case inr h24 =>
          -- False on the left can always be used.
          apply False.elim h24
    case inr h25 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h26 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h27
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h3
        -- One of the premise coincides with the conclusion.
        exact h7
      case inr h28 =>
        -- Disjunctions on the left can always be decomposed.
        cases h28
        case inl h29 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h30
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- One of the premise coincides with the conclusion.
          exact h3
          -- One of the premise coincides with the conclusion.
          exact h7
        case inr h31 =>
          -- False on the left can always be used.
          apply False.elim h31



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313150413640695889240335221246 : (p3 ∨ (((p1 → (((p5 ∧ ((False ∧ p3) ∨ (p4 ∧ p4))) ∨ False) ∧ (p1 ∨ p5))) ∨ ((((p1 → p1) → p1) ∧ True) ∨ (p1 ∧ p1))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60484625727344559041137635330 : ((True ∧ ((((p4 ∧ ((((p4 ∧ p3) ∧ p1) → (True ∧ ((True ∧ (p5 ∧ (p2 ∨ (p3 ∨ False)))) ∨ p1))) ∧ True)) → False) ∨ p3) ∧ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_732196931309369312266688218164 : ((((True ∧ p4) ∧ (p5 ∨ (((((True ∧ ((p3 → True) ∧ False)) → (p2 → False)) → p4) → (p3 ∨ (p5 → ((p5 ∧ False) ∧ p5)))) → p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46231608047782429031370260262 : (((((((True → (p1 ∧ ((p4 ∨ True) ∧ p1))) ∨ p4) → ((p2 ∧ ((False → p3) ∧ p1)) ∧ False)) → False) ∨ (p5 ∨ True)) ∧ (True ∨ p5)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_166078716897426224012574940034 : (((p2 ∨ True) → (((((p3 ∨ p5) ∨ (p2 → False)) ∨ p3) ∧ (p4 → (p5 → p5))) ∨ False)) ∨ (True ∨ ((((p3 ∧ True) ∧ False) ∨ True) ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_94341137886547780930182370678 : ((p2 ∧ ((p1 → ((p5 ∧ (True ∧ (p5 ∧ p1))) ∨ p5)) ∧ (p3 ∧ (p2 ∧ (((True ∨ p4) → ((p5 → p4) ∧ (p5 ∧ p4))) ∧ p1))))) → p4) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h7.left
  let h9 := h7.right
  -- Conjunctions on the left can always be decomposed.
  let h10 := h9.left
  let h11 := h9.right
  -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
  have h12 : (True ∨ p4) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h10, we can now drive its conclusion.
  let h13 := h10 h12
  -- We need to get the right conjuct of h13 based on <expert-advice>.
  let h14 := h13.right
  -- We need to get the right conjuct of h14 based on <expert-advice>.
  let h15 := h14.right
  -- One of the premise coincides with the conclusion.
  exact h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314620203570184161628145336578 : (p3 ∨ ((((((p5 → False) ∨ p4) ∨ p5) ∧ (False ∧ p3)) ∨ (p3 → (p4 → (p2 → True)))) ∧ (((p2 ∨ p2) ∨ True) ∧ (False → (p1 ∨ p2))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h4
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52300290278976714307359986582 : ((((((p3 → p1) → (True → p1)) → (False ∧ ((True ∨ p5) → True))) ∧ False) ∧ (True ∧ ((((p5 ∨ p2) → p5) ∨ p2) → (p4 ∧ p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_748896406208528732835336251736 : ((((p4 → p2) → ((((False → p5) → p5) → ((((((p3 ∧ p4) ∨ (p4 ∧ (p5 ∨ p5))) ∧ p5) → p2) ∧ (p4 ∧ p1)) ∧ p4)) ∨ True)) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_41160488328917785686250674724 : ((((p2 ∨ (((p4 ∧ ((p2 ∨ ((True ∧ p1) → p2)) ∧ (p3 ∨ True))) ∧ ((False ∨ True) → True)) ∨ False)) ∨ (p1 ∨ (False ∨ True))) ∨ p2) ∨ False) := by
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
theorem thm_5_vars_340836461333384408174852283620 : (p2 → ((((p5 ∨ True) → ((((p3 → ((p1 → p4) ∧ (False ∨ (p5 ∧ p5)))) ∨ (False ∧ p5)) ∨ (True ∧ p4)) ∧ p1)) → (p5 ∧ p3)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231170474891469950358680517722 : (((p2 ∨ p2) ∨ p2) → (True → ((p4 ∨ (True → (((False ∧ (p1 → p3)) → p5) ∧ (((p3 → p4) → (p2 → p1)) ∧ p3)))) ∨ (True ∨ p5)))) := by
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
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42716603733149630411733686327 : (((p5 ∨ (p2 ∨ (True → ((True ∨ ((p5 ∧ (p5 ∧ p4)) ∧ ((p4 → p5) ∨ True))) → ((p5 → ((p5 ∧ p2) → p3)) ∨ False))))) ∨ True) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135422828041754058334511104875 : (((p2 ∧ (p1 ∧ ((p3 → (p2 ∧ p1)) ∧ ((False ∨ (((p1 ∨ True) → True) → p2)) ∧ p5)))) ∨ (True → (p1 → p1))) ∨ ((p2 ∨ p2) ∧ p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_261023114821197345716276037953 : ((p4 → p2) → (((p3 ∨ p5) ∨ (((p4 ∧ (p5 ∨ p4)) → ((False ∨ (False ∧ (p3 ∧ p3))) ∨ p4)) ∨ ((True ∧ False) → p5))) ∨ (p2 ∧ False))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149977532875263849527609527904 : ((p4 ∨ ((p2 ∨ (False → (p2 ∧ (True ∨ p4)))) → (False ∧ (((p2 → False) ∧ (p2 ∨ (p1 ∨ p4))) ∨ p3)))) ∨ ((p1 → p3) ∨ (p3 → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_691382554859454462489745434503 : (((((True ∧ p4) ∧ ((p2 → p5) ∧ (((p1 ∧ p4) ∨ (p5 → (True → True))) → True))) → (((p2 ∨ (p1 ∨ p5)) → (p3 ∧ p3)) ∨ True)) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h3.left
  let h7 := h3.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_647218712630913502797622932076 : ((((p3 → (p4 → (((True ∨ ((False ∨ False) ∨ (p1 ∨ (False ∧ (p5 ∨ ((p5 → p5) ∧ p2)))))) ∨ p4) ∧ (p4 → (p4 ∧ False))))) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60920016441562265305248646051 : ((False ∧ ((((((p1 ∧ (((True ∧ p4) → p2) ∨ ((p1 ∧ p2) → p4))) ∨ p3) ∨ p3) ∨ (True ∧ False)) ∨ (p1 → (True ∧ False))) ∧ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208745978580459426445074963164 : ((p1 ∧ (p2 ∨ (p2 → (p4 ∨ p1)))) → ((((False ∧ p1) ∧ (p3 ∨ (p4 ∨ (p4 → ((p2 ∧ (p2 ∨ p1)) ∧ p3))))) ∨ p2) ∨ (p2 ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_790987572119678899550833438946 : (((True → ((((((((False → True) → p3) ∧ (p5 → True)) → p5) ∧ (p4 ∨ (p1 ∧ (p2 → (p2 → (False → p2)))))) ∨ p5) ∧ p5) ∧ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60686547191399245164534578161 : ((True ∧ (((((((p3 ∧ p2) ∧ p3) → (False ∧ p3)) ∨ True) ∧ p5) ∧ p3) ∨ ((True → p2) ∨ ((p1 ∨ (p5 ∨ False)) ∨ (True ∨ p1))))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
theorem thm_5_vars_323823553448980394558956083217 : (p5 ∨ ((((False → (p2 ∧ p2)) → (p4 ∨ ((p1 ∨ ((p1 ∧ p4) ∧ (p1 → False))) ∧ True))) → p1) → ((p5 → (p5 → (p2 ∨ True))) ∨ p4))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135042667000044093556573123927 : ((((((False → (True ∨ p2)) → ((p1 ∨ p1) ∨ ((p1 → (p1 → (p4 → p2))) ∨ p1))) ∧ p4) ∨ p1) ∨ (True ∧ False)) ∨ ((True ∨ True) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_653376613720258559737659809854 : ((((p3 → (((p3 → p5) → False) ∧ ((p5 ∨ (p5 → (((p3 ∨ (p1 → True)) ∧ p5) → (True ∧ p4)))) ∨ (p3 ∧ p1)))) ∧ (True → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166425391585911219345826202100 : ((p1 ∨ (((p2 ∨ p1) ∨ False) → ((p3 ∨ (p3 → (p2 ∨ ((p2 ∨ True) ∨ p3)))) ∨ p5))) ∨ ((((p2 → p4) ∨ p3) ∨ (p4 ∧ p2)) ∧ True)) := by
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h4
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h5 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h6
  case inr h7 =>
    -- False on the left can always be used.
    apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_358190439751791768285953957400 : (p5 → (p3 ∨ ((p3 → p4) ∨ (((((((((p3 ∨ p1) ∨ (p1 → True)) → p5) → p1) → False) ∨ p5) ∨ p1) ∨ (p3 → (p4 → True))) ∨ False)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111073016836496745091395128377 : ((((((p4 ∧ (((False → (p1 ∧ p3)) → False) ∨ False)) → (p5 → p3)) ∨ p1) → (((p3 ∨ (True ∧ p1)) → False) ∧ p1)) ∧ p1) ∨ (p1 → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347819807763129605173432005652 : (p3 → (((p3 ∨ p1) ∧ p5) → ((p3 → (p4 ∨ ((((p3 ∧ True) → ((((p1 ∨ (False ∨ p1)) ∨ p1) ∨ p5) ∨ True)) ∨ p2) ∧ p4))) ∨ p3))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_726239546828657111658990661205 : (((((False ∨ p1) ∨ p3) ∨ (((((p3 ∨ ((p1 → (p1 → p4)) ∧ True)) ∧ False) ∨ (p5 → (p2 ∧ True))) → ((p2 → p3) ∨ p3)) ∧ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112609115485163664959488491495 : (((((p4 → (p5 ∨ ((((p2 ∧ True) → (p1 → p5)) → p3) → (True → (p2 ∨ True))))) ∧ (p2 → p5)) ∨ (p3 ∨ p1)) → p3) ∨ (False → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313978624470196266812076318348 : (p3 ∨ ((((p5 → False) ∧ ((False ∨ ((p4 ∧ p1) ∧ p1)) → p5)) → ((p2 ∨ (p1 ∧ (True → p4))) ∧ (p2 ∨ (p1 ∨ False)))) ∨ (True ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_809530530947074540586621103829 : (((p5 → (((p5 → (((p4 ∨ ((p4 ∨ p4) ∨ p2)) → p2) ∨ True)) → (((p4 ∧ ((p5 ∨ (False → True)) ∧ p4)) → p3) → False)) → p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66589633537442424068833075916 : ((True → ((((p2 ∨ (p1 ∧ (p5 ∨ (((p5 ∨ p4) ∧ ((False ∨ p5) ∨ (p4 → p5))) → False)))) → p5) ∨ True) ∨ ((p3 ∧ p2) → True))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_238142148583054310053725966835 : ((True ∨ p3) ∧ (((False ∨ ((p4 ∧ p5) ∨ p2)) ∨ p3) ∨ (((((True ∧ False) ∧ p5) ∧ p1) ∨ ((False → p3) ∧ (p1 → p3))) ∨ (True ∨ p1)))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134020119800106953548000615372 : (((((p4 ∨ ((p2 ∨ ((p5 ∧ (((p4 ∧ ((p1 → p4) → p5)) → True) → p2)) ∧ p2)) → p1)) ∧ False) ∨ p3) ∨ p3) ∨ ((p4 → p1) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159063677511417506207867272917 : ((p5 ∨ ((p5 ∨ False) ∧ ((((p1 → ((((p4 → p5) → p5) → p3) ∧ p5)) → p4) ∧ p4) ∧ p4))) ∨ ((p1 ∧ False) → ((True ∧ p5) ∨ p4))) := by
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
theorem thm_5_vars_53765457378900494593809459793 : ((((p4 → ((p1 ∧ (p2 ∧ (p5 ∨ p5))) → p4)) ∧ p2) ∨ (((p5 ∧ ((p5 → (p2 ∨ (p3 ∨ True))) → (p5 ∨ True))) ∨ p5) ∨ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_743766936136110818805177214463 : ((((True ∧ p4) → (False ∨ ((False → False) → (p5 ∧ (((((((True ∨ p1) → (p2 → True)) ∨ p5) ∨ (p3 → p1)) ∧ p1) ∨ True) ∧ True))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166089849826296421743033561077 : (((p5 ∨ p2) → ((False → p1) ∧ (p5 → ((((p4 ∨ p2) ∨ p1) ∧ (p2 ∧ p4)) ∨ False)))) ∨ (((False ∧ False) → True) ∨ ((False → False) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_901359630136619958800510119392 : ((((p5 → (((((p4 ∨ (p4 → False)) ∧ (p4 ∨ (False ∧ p4))) ∧ p1) ∨ p5) ∨ (p5 ∨ ((p3 ∨ p5) ∨ p3)))) → ((False ∧ p2) ∧ p2)) → p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p5 → (((((p4 ∨ (p4 → False)) ∧ (p4 ∨ (False ∧ p4))) ∧ p1) ∨ p5) ∨ (p5 ∨ ((p3 ∨ p5) ∨ p3)))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- False on the left can always be used.
  apply False.elim h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66601976801805459641757545618 : ((True → ((((((True ∧ (p1 ∧ p1)) ∧ p5) ∧ p3) ∨ (False ∨ (p1 → (p2 ∧ (p5 → True))))) ∨ True) ∧ (p4 ∧ (p4 ∨ (p5 → p1))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_803758726724965203174192646044 : (((p3 → ((((False → p4) → (p1 ∧ p3)) → ((((p2 → ((p5 → ((True ∨ p3) ∨ p1)) ∨ p2)) ∧ p5) ∧ p2) ∧ True)) ∧ (True ∧ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300385720370053847552808724971 : (False ∨ ((((False ∨ p3) ∨ (((p5 ∧ p4) ∨ False) ∨ True)) ∨ (p3 → (((p3 ∧ True) ∨ (p1 ∧ (False ∧ False))) ∧ True))) ∨ (True → (p3 ∨ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_134215980959832893526735798823 : ((((p2 ∨ (p2 ∨ (p5 → (p5 ∧ (p5 ∨ p4))))) → (((p5 → p2) ∧ (p1 ∨ ((p4 ∨ p4) → p3))) → p5)) ∨ False) ∨ (p3 → (True ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54247065139031209969253951256 : ((((p4 ∨ ((p4 → p4) ∧ p5)) ∧ (p3 ∨ p1)) ∧ (((p4 ∨ (((False ∧ (True → (p5 ∧ p5))) ∧ False) → p4)) ∨ (p1 ∧ p5)) ∨ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299408898806607419722320853516 : (False ∨ ((p2 ∧ ((p4 → p5) ∨ ((True ∨ (p5 ∨ (((True ∧ False) → (p3 → p3)) ∧ p4))) → ((((False ∨ p3) ∧ p3) → p3) → False)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113250676980138856736974700710 : (((((p1 ∨ ((False ∧ p1) → p4)) ∧ ((False ∧ (False ∧ ((True → (p1 ∨ p3)) → False))) ∨ p1)) ∨ (False → p5)) ∧ (True ∧ p3)) ∨ (True ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152303767325202470162486023229 : (((((p3 → p5) → p5) ∧ p3) ∧ (p3 → (((p5 ∧ p1) → (True ∨ ((p2 ∧ (p4 → p4)) → True))) ∧ False))) → (True ∧ ((p5 ∧ p3) ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h6 : p3 := by
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h7 := h3 h6
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_649557881965502434081318936509 : (((((((p5 ∨ True) ∧ (((p5 ∨ ((p1 ∨ p5) ∨ True)) → p5) ∨ (p3 → ((False ∨ False) → p2)))) ∧ True) ∨ (p4 ∧ True)) ∧ (p4 ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_349111493136775479556894100534 : (p3 → (True → ((p2 ∧ ((p1 ∧ p4) ∨ (((p5 ∧ (p3 → (p3 ∨ True))) → (p3 → False)) ∧ p3))) ∨ ((p1 ∧ (p4 ∨ False)) → (p1 → True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50184519855395647231706321564 : (((((True ∧ (((True ∧ p2) ∧ p2) ∨ p3)) ∧ (((p2 ∧ (p1 ∧ p2)) → p5) → (p5 ∨ p3))) ∧ True) ∨ ((p3 ∨ p3) ∨ (False → p1))) ∨ p4) := by
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
theorem thm_5_vars_185605601383646622351464285953 : ((True → (((((p2 ∨ (p2 ∧ True)) ∧ p5) ∧ False) ∧ p4) ∧ p1)) ∨ (True → ((p2 → True) → (((p4 ∧ (False ∧ True)) ∧ (p2 → p3)) ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119258511139773163329516699084 : ((p2 → (True → ((False ∨ (True ∧ (p4 ∧ (p4 ∧ (p1 ∨ ((p5 ∨ (p2 ∧ p4)) ∧ False)))))) ∨ (False → (p2 ∧ (p5 → p4)))))) ∨ (False ∨ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317776486417239610325564504694 : (p4 ∨ (((p4 ∨ (p3 ∨ (p3 → (((False → p3) → (p3 ∧ (True ∧ p2))) ∧ False)))) → ((p3 ∨ (p4 ∨ p3)) ∨ ((p3 → p1) ∨ p5))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_216698924731784453855680982127 : ((((False ∧ p2) → True) ∧ p1) → ((((p4 → False) ∧ False) ∧ ((p2 → p4) ∨ (True ∨ True))) ∨ ((((p3 ∨ False) → True) ∧ p3) ∨ (p5 → p5)))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340703785142387354514374367155 : (p2 → ((((p3 ∨ (((p2 → p1) ∧ False) ∨ (p5 ∨ (((False ∧ (p2 ∧ (p3 ∧ p2))) ∧ p4) ∧ p2)))) ∨ ((p5 → p4) ∨ p3)) ∧ p1) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_141041486538652814162340338225 : (((p3 ∨ ((True ∧ (p2 ∧ True)) ∧ (True ∨ False))) ∧ ((p2 ∨ ((p3 ∧ (p5 ∧ p5)) ∨ (p4 ∨ (p3 → p5)))) ∧ p3)) → ((False ∧ p4) ∨ p3)) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Conjunctions on the left can always be decomposed.
        let h10 := h9.left
        let h11 := h9.right
        -- Conjunctions on the left can always be decomposed.
        let h12 := h11.left
        let h13 := h11.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h6
      case inr h14 =>
        -- Disjunctions on the left can always be decomposed.
        cases h14
        case inl h15 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h6
        case inr h16 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h6
  case inr h17 =>
    -- Conjunctions on the left can always be decomposed.
    let h18 := h17.left
    let h19 := h17.right
    -- Conjunctions on the left can always be decomposed.
    let h20 := h18.left
    let h21 := h18.right
    -- Conjunctions on the left can always be decomposed.
    let h22 := h21.left
    let h23 := h21.right
    -- Disjunctions on the left can always be decomposed.
    cases h19
    case inl h24 =>
      -- Conjunctions on the left can always be decomposed.
      let h25 := h3.left
      let h26 := h3.right
      -- Disjunctions on the left can always be decomposed.
      cases h25
      case inl h27 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h26
      case inr h28 =>
        -- Disjunctions on the left can always be decomposed.
        cases h28
        case inl h29 =>
          -- Conjunctions on the left can always be decomposed.
          let h30 := h29.left
          let h31 := h29.right
          -- Conjunctions on the left can always be decomposed.
          let h32 := h31.left
          let h33 := h31.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h26
        case inr h34 =>
          -- Disjunctions on the left can always be decomposed.
          cases h34
          case inl h35 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h26
          case inr h36 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h26
    case inr h37 =>
      -- False on the left can always be used.
      apply False.elim h37



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_265767394167238748325176215532 : (True ∧ (p4 ∨ (((p2 ∨ ((p5 ∧ (p4 ∨ p3)) ∧ p2)) ∧ (((True ∨ ((p1 ∧ p1) ∨ p5)) → p3) → (p4 ∨ (True ∨ p5)))) ∨ (False → False)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113714926994123215530863876801 : ((((p2 ∧ (p4 ∧ ((p3 → (p3 ∧ p2)) → ((((False ∧ (p2 ∧ p2)) → p4) ∧ False) ∨ p2)))) ∨ (True ∨ False)) → (p3 ∨ p1)) ∨ (p3 → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_658861331192068295891608899555 : ((((True → ((p5 → p2) ∨ ((((((p1 ∨ False) ∧ True) → (p4 ∨ (p3 ∧ p5))) ∧ ((p2 ∨ True) ∧ p2)) ∧ p2) → p5))) ∨ (p1 ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_683137765601614205987429783633 : ((((p3 ∧ ((p1 ∨ (((p1 ∧ p5) ∧ p5) ∧ True)) ∧ (False → (((p3 → p5) ∨ p5) ∧ p1)))) ∧ (((False → p5) → p1) ∧ (p4 ∨ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_77965377754454342098203608801 : (((p3 ∨ ((p2 ∨ (p3 ∧ p1)) ∨ (((True ∨ (p3 ∧ p1)) → (True → ((False → (False → (p3 → p2))) ∨ (True → p5)))) ∨ p4))) → False) → p1) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p3 ∨ ((p2 ∨ (p3 ∧ p1)) ∨ (((True ∨ (p3 ∧ p1)) → (True → ((False → (False → (p3 → p2))) ∨ (True → p5)))) ∨ p4))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h5 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h6
      -- Implications on the right can always be decomposed.
      intro h7
      -- Implications on the right can always be decomposed.
      intro h8
      -- False on the left can always be used.
      apply False.elim h7
    case inr h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h12
      -- Implications on the right can always be decomposed.
      intro h13
      -- Implications on the right can always be decomposed.
      intro h14
      -- False on the left can always be used.
      apply False.elim h13
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h15 := h1 h2
  -- False on the left can always be used.
  apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_327186324471594944500617749724 : (True → ((p2 ∨ ((p1 ∨ p4) ∧ (p1 ∨ ((p5 → (((p3 ∨ p1) ∨ (((p4 → p4) ∨ p5) ∨ False)) ∨ True)) ∧ (True ∧ (p3 ∨ True)))))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114439857250728953505251240747 : (((p5 ∨ ((p2 ∧ True) ∨ (((p4 → (p2 ∧ p2)) ∨ p5) ∧ ((True ∧ p1) → (False ∧ p5))))) ∨ (p5 ∧ ((p5 ∨ p5) ∧ p3))) ∨ (p5 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51563599989932098844266255918 : (((False ∨ (p3 ∧ ((True ∧ ((p4 ∧ (False ∨ p2)) → p2)) → (p4 ∧ (False → (p4 ∧ p4)))))) → ((p1 ∨ p5) ∨ ((p4 → p2) → p4))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h7 : (True ∧ ((p4 ∧ (False ∨ p2)) → p2)) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- Implications on the right can always be decomposed.
      intro h8
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- False on the left can always be used.
        apply False.elim h11
      case inr h12 =>
        -- One of the premise coincides with the conclusion.
        exact h12
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h13 := h5 h7
    -- We need to get the left conjuct of h13 based on <expert-advice>.
    let h14 := h13.left
    -- One of the premise coincides with the conclusion.
    exact h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_320105980056733403214796713699 : (p4 ∨ (((p1 → True) → True) → ((((((p3 ∧ p1) ∧ True) ∧ (p5 → False)) ∧ True) ∨ p1) ∨ ((True ∧ (False ∧ False)) → (p3 ∧ (True ∧ p1)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- False on the left can always be used.
  apply False.elim h5
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h7 := h2.left
  let h8 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h9 := h8.left
  let h10 := h8.right
  -- False on the left can always be used.
  apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340780393107915889292893398236 : (p2 → ((((((((p1 → (p2 ∧ (p4 ∧ ((p5 ∨ p4) ∨ p2)))) ∨ (p1 ∧ p3)) → False) ∨ (p5 ∧ p3)) ∧ p1) → (p4 → False)) → p4) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_785397299742162633705185002304 : (((p4 ∨ ((((p2 ∨ p2) ∨ ((p5 ∧ p5) → (False ∧ (p4 ∨ ((p4 ∨ (p3 → True)) ∧ (True ∧ (p5 ∨ p4))))))) ∨ (p4 → p1)) ∨ True)) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_39766001887016239498272230104 : (((True → (((p2 ∧ ((p2 → p2) → ((p2 → True) ∨ False))) ∧ p4) → (((((p5 → (p3 → p5)) → p2) → p3) ∧ p4) ∨ p3))) ∧ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115633749422344416352488531776 : ((((((False ∧ p2) ∧ False) ∧ p3) ∨ p4) ∨ (((p2 ∨ p3) ∨ ((p5 ∨ p2) ∨ (((p3 ∧ p5) → (p1 ∨ p4)) → False))) ∨ p4)) ∨ (True ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324071857755042337265317737679 : (p5 ∨ (((((((p3 → p4) ∨ (p4 ∨ True)) → p2) → True) → p2) ∨ True) ∨ (p1 → (((p4 ∧ p2) → (p3 ∧ (p4 → (p3 ∨ p2)))) ∨ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156719564703829077099422353624 : (((((p4 → ((p3 → (p3 → p5)) → p1)) ∧ True) → ((p3 ∨ p1) → (p2 ∧ (p5 ∧ p3)))) ∧ p2) ∨ ((p1 ∨ ((p4 ∨ False) → True)) ∨ p4)) := by
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
theorem thm_5_vars_71178341273465153558355074570 : (((((False ∨ False) ∨ (True ∨ p4)) → ((((p5 → p5) ∨ p4) ∧ False) ∧ (((p2 ∧ False) ∧ (p2 → False)) ∨ (True ∧ (True → p2))))) ∧ p4) → p5) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : ((False ∨ False) ∨ (True ∨ p4)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314475875873407471531300181626 : (p3 ∨ (((p2 ∨ (False → False)) → (((((p1 ∨ (p1 ∧ False)) → False) ∧ True) ∨ (p4 ∨ (p1 → p1))) → p4)) → (p4 ∧ (False → (p1 ∨ p2))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p2 ∨ (False → False)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h5 : ((((p1 ∨ (p1 ∧ False)) → False) ∧ True) ∨ (p4 ∨ (p1 → p1))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- One of the premise coincides with the conclusion.
    exact h6
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h7 := h4 h5
  -- One of the premise coincides with the conclusion.
  exact h7
  -- Implications on the right can always be decomposed.
  intro h8
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157077171407266122414938429326 : (((p2 ∨ (((p5 ∧ p5) ∧ p5) ∨ ((((False ∨ (True → (p3 ∨ p4))) → p1) ∧ p4) → p1))) ∨ p2) ∨ (((p2 ∨ True) → (True → p3)) ∧ p5)) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (False ∨ (True → (p3 ∨ p4))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h4
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_665030232309374251418928624403 : ((((p4 → ((p2 ∨ p4) ∧ (((False ∧ ((True ∧ ((p3 ∨ p4) ∨ p3)) ∨ (False → p1))) ∨ p1) ∨ (p2 ∨ (False → p5))))) → (p4 ∧ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64100787434991323944680337571 : ((False ∨ ((((p3 ∨ False) ∧ (p4 ∨ p3)) ∨ (p4 → (False ∨ p2))) → (((True ∧ False) ∧ (False ∧ p2)) ∨ ((True ∨ p4) ∨ (False ∨ p1))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256544108114995791436634365558 : ((False ∨ p5) → ((True → ((False ∨ p2) ∧ (p4 ∨ p1))) → ((p4 ∨ (p5 → p4)) → ((True ∧ p1) → ((p2 ∧ p5) ∨ (p4 ∨ (p2 ∨ p4))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h8 =>
      -- False on the left can always be used.
      apply False.elim h8
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h7
  case inr h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h11 =>
      -- False on the left can always be used.
      apply False.elim h11
    case inr h12 =>
      -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
      have h13 : p5 := by
        -- One of the premise coincides with the conclusion.
        exact h12
      -- We have shown the premise of h10, we can now drive its conclusion.
      let h14 := h10 h13
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_312998764290070060225853786842 : (p3 ∨ (((((p1 ∨ (p3 → ((False ∨ (p4 ∧ p5)) ∧ (False ∨ p5)))) ∨ (((p1 → (p4 ∨ (p3 ∨ False))) → False) ∨ True)) → p3) ∨ True) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50182359153913535517239222093 : (((((p2 → (True ∨ (p2 ∧ ((True ∧ p2) ∨ (True ∨ p5))))) ∧ (p1 ∨ ((False ∧ p5) ∧ p5))) ∧ False) ∨ ((p1 ∧ (p3 ∨ p2)) → True)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_189804451838060530404654161406 : ((True → (False ∨ ((p3 ∧ (p1 ∨ p2)) → (False → p1)))) ∧ (((False ∧ True) ∧ p1) ∨ (p3 ∨ (p2 ∨ (((p3 ∨ p1) → (p3 ∨ p2)) → True))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47300251254702795772920025095 : ((((p5 ∧ (p5 ∧ p3)) ∧ (((p1 ∨ ((p4 → False) ∨ False)) ∧ ((((p4 ∨ (True ∨ False)) ∨ p3) → p3) ∧ p4)) ∧ p5)) ∨ (False ∧ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_684126114593022421520802332724 : (((((p5 ∧ (p3 ∧ (((((False → False) → False) ∨ False) ∧ p2) ∧ (p2 → False)))) ∧ (True → True)) ∨ (False → ((False ∨ (False → True)) ∨ p4))) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_705903173188404563788183290873 : ((((((False → True) → p4) ∨ ((p1 → False) ∨ p1)) ∧ ((((p4 ∧ p5) ∨ ((False → (True ∧ p1)) → (p4 → p3))) ∧ p2) ∧ (p4 ∨ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232841015042636165412830939156 : ((p2 ∧ (p5 ∨ p3)) → (((p5 ∧ p5) ∨ (((p1 ∧ p4) ∧ (False ∧ True)) ∨ p3)) ∨ (False ∧ (True ∨ (p1 → (((p2 → p1) ∨ p5) ∨ p2)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h4
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_151935156293296514757058336782 : (((((p5 → p2) → p1) → (p4 → (((p4 ∧ False) ∧ True) ∨ False))) ∧ (p2 → (p3 ∨ (True ∧ (p5 ∨ False))))) → (p4 → (p2 → (p5 ∨ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h6 : p2 := by
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h7 := h5 h6
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h12
    case inr h13 =>
      -- False on the left can always be used.
      apply False.elim h13



