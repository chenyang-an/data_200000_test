variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_799876463594512618572026784946 : (((p1 → (p5 → ((((p4 → p5) ∧ ((p2 ∧ p3) ∨ (((False ∨ p1) ∨ ((p5 ∧ (p5 ∧ (p4 ∧ p1))) → False)) → p2))) → p4) ∨ p5))) ∨ p1) ∧ True) := by
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
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232353810477940764228115926965 : (((p4 → p2) → p5) → (p5 → (p1 → ((((((p3 ∨ p4) → p5) ∧ (((p2 ∨ p1) → p5) ∧ (p1 → True))) ∧ p5) ∧ (p3 ∧ p2)) ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_733880453277415222163135898357 : ((((p5 ∧ p5) ∧ ((p5 → p3) ∧ (p2 ∨ (((p5 ∨ ((p4 → (p3 → (((False ∨ p3) ∧ (p5 → p1)) ∨ p2))) → p5)) ∨ True) → p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308380378685991133803283017582 : (p2 ∨ (((((p3 → p5) ∨ (((False → p3) → True) ∨ (((p5 ∨ (True ∨ False)) ∧ p5) ∧ ((True ∨ p5) → p2)))) → (p2 ∨ p3)) ∨ p2) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59957235821457075661394634030 : (((True ∨ p4) → (((p4 ∧ (((True ∧ (p5 ∨ p2)) ∨ p3) ∨ (((p3 → p4) → True) ∧ (p1 ∧ p3)))) ∧ (p5 ∨ (False ∨ p5))) ∧ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138066974037867776983164027299 : ((True → (True → (((((p4 → ((p3 → p5) ∨ p3)) ∨ p1) ∧ p4) → False) ∨ (((True ∧ p5) → p5) ∨ (False → p3))))) ∨ ((p5 → p2) ∨ p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_722102824315033098362116862597 : ((((p2 → (p2 ∨ (p5 → p4))) → (((((True ∧ p1) → (p5 ∧ True)) → (((p2 → p1) ∧ (p1 → (p3 ∧ True))) → p1)) ∨ p4) ∨ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48365653612456774952085753158 : (((p5 ∨ ((True ∨ (((((True ∨ False) ∨ True) → (((p3 ∧ p5) → (True ∨ p1)) ∨ (False ∧ False))) ∧ p2) → p5)) ∧ p5)) → (True → p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_730242093963615133107031000939 : (((((p2 → True) → True) → (((p4 ∧ p4) → (False ∨ (p2 ∨ (p4 → (p3 ∨ p5))))) ∨ (p1 ∧ ((False → (p4 ∨ (p5 ∧ p5))) ∧ p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308665798342301147444315172806 : (p2 ∨ ((p4 ∧ (((p3 ∧ p4) ∨ p5) ∨ ((True ∧ ((p4 ∧ (p5 ∨ (p4 ∨ False))) ∧ p4)) ∨ (p3 ∧ (((False ∧ p2) ∨ p4) ∧ False))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58230429023385513520657232313 : (((p4 ∧ p4) ∧ (p1 → (False ∨ (False ∨ (((((p2 ∨ False) ∧ (p1 → p1)) → p4) ∨ (p2 ∨ ((p2 → False) → True))) → (p1 → p3)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40533105999525736334943944984 : ((((p2 ∨ (((((p5 ∨ p4) ∧ ((p3 → p2) → p1)) → ((p4 → (((False ∧ p3) → p5) ∧ p3)) ∨ p4)) → p3) → p4)) ∨ True) ∨ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_722901322407478402204516707886 : (((((p3 ∧ p2) ∨ p5) ∧ (((p1 ∧ p3) ∧ (p5 ∧ (((p1 → True) ∧ False) → ((p1 ∧ p5) → (True ∨ p2))))) ∨ ((False ∨ p5) ∨ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41142845591361531726128125454 : ((((((p2 → ((p5 ∧ p4) ∧ p5)) ∨ (p1 ∨ (p2 ∧ (p5 → p5)))) → ((p1 ∨ (p3 → False)) → p3)) ∨ (p5 ∧ (True ∧ False))) ∨ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345366993671181109706381855875 : (p3 → ((((((((p3 → ((p5 → p5) ∧ (p1 ∨ p2))) ∨ p4) → p4) → p4) ∧ (p4 ∧ p5)) ∧ (False ∧ ((p5 ∧ False) → False))) ∨ True) ∨ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134367878360943034996749439370 : (((p2 ∨ (((p1 → (((p2 ∧ False) → p3) → (((p5 ∧ p1) → (False ∨ False)) ∧ (False ∧ False)))) ∧ False) ∨ False)) ∨ p2) ∨ ((p3 ∨ True) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_124778605916131443978907389176 : (((p2 ∨ (p1 ∨ (True ∨ p1))) ∧ ((((p2 → p2) ∧ ((p3 ∧ (p4 → False)) ∧ ((p5 ∧ (p2 ∧ True)) → False))) ∨ True) → False)) → (p2 ∨ p5)) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h7 : (((p2 → p2) ∧ ((p3 ∧ (p4 → False)) ∧ ((p5 ∧ (p2 ∧ True)) → False))) ∨ True) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h8 := h3 h7
      -- False on the left can always be used.
      apply False.elim h8
    case inr h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
        have h11 : (((p2 → p2) ∧ ((p3 ∧ (p4 → False)) ∧ ((p5 ∧ (p2 ∧ True)) → False))) ∨ True) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h3, we can now drive its conclusion.
        let h12 := h3 h11
        -- False on the left can always be used.
        apply False.elim h12
      case inr h13 =>
        -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
        have h14 : (((p2 → p2) ∧ ((p3 ∧ (p4 → False)) ∧ ((p5 ∧ (p2 ∧ True)) → False))) ∨ True) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h3, we can now drive its conclusion.
        let h15 := h3 h14
        -- False on the left can always be used.
        apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_597946475130735846122695769949 : (((((True ∧ (False ∧ p5)) ∧ (p4 ∨ (((p5 → False) ∨ p1) ∨ (p4 → (((p5 ∧ (False ∧ (p2 → (p3 ∨ p1)))) ∧ p3) → p5))))) ∧ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149024874418046246825182311538 : ((((p1 ∨ True) → p5) ∨ (p5 ∨ (((True ∧ p1) ∨ ((True ∧ p4) ∧ p5)) ∨ (p2 ∧ (p5 ∧ (p2 ∧ True)))))) ∨ (p3 ∨ ((p3 ∨ True) ∨ False))) := by
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
theorem thm_5_vars_149837196228754641689844626889 : ((p1 ∨ ((((p2 ∨ p1) → p1) → (True → p1)) → (p2 → ((p4 ∧ p2) → ((p2 → False) ∨ (p3 ∨ p2)))))) ∨ (False → (p2 ∧ (True → p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59796372193355182342774449898 : (((p2 ∧ p3) → (((((p1 ∨ (p1 ∨ p3)) ∨ ((p2 ∧ (p2 ∨ (p4 → p1))) ∨ p1)) → p4) ∨ True) → (((p3 ∧ p2) → False) → False))) ∨ p5) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h1.left
    let h6 := h1.right
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h7 : (p3 ∧ p2) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h6
      -- One of the premise coincides with the conclusion.
      exact h5
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h8 := h3 h7
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h1.left
    let h11 := h1.right
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h12 : (p3 ∧ p2) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h11
      -- One of the premise coincides with the conclusion.
      exact h10
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h13 := h3 h12
    -- False on the left can always be used.
    apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322133571818036528121595949100 : (p5 ∨ ((p1 ∨ (False ∨ ((p3 ∧ p3) ∨ (((((True ∧ p4) ∧ (p2 → p2)) ∧ p1) → True) ∨ (p2 ∨ (p5 → ((p1 → p4) ∧ p1))))))) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_749628474197414025524633008644 : (((True ∧ ((((((True → p1) ∨ (False ∨ p3)) → (p1 → ((True ∨ (p1 ∧ (((True → p2) ∧ p2) → p3))) ∧ False))) ∨ True) ∨ True) ∨ p2)) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304780550793717075822249154895 : (p1 ∨ ((True → ((p2 ∨ p3) ∧ (((p2 ∨ p5) → (p3 ∧ p2)) ∨ ((False ∧ False) ∨ ((((p5 ∨ False) → p1) ∧ False) ∨ True))))) ∨ (p1 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_242792984842986473421680535217 : ((p3 → p3) ∧ (((((True ∨ (p2 ∧ (((p4 ∨ p5) ∨ p1) ∨ p2))) ∨ True) → p4) ∨ (((p3 → p4) ∨ ((p2 → p2) ∨ p2)) ∧ True)) ∨ p3)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_626552160573524184963990729570 : ((((p4 → ((True → ((p1 → p3) ∨ p2)) ∧ (((p2 → (False ∧ p1)) ∧ ((p3 ∨ (p3 ∧ False)) ∧ (True ∨ (p1 ∧ p3)))) ∧ False))) ∨ True) ∨ False) ∧ True) := by
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
theorem thm_5_vars_225871632122810274295629088060 : (((False ∧ p5) ∨ False) ∨ (((p4 → p3) ∧ (False → True)) → (p4 → (p4 → ((((p2 ∨ (p3 → (p1 ∨ (p1 ∧ True)))) ∧ p1) ∧ p3) → p3))))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h1.left
    let h11 := h1.right
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h12 =>
    -- Conjunctions on the left can always be decomposed.
    let h13 := h1.left
    let h14 := h1.right
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172427042863611837074063533355 : (((p2 ∧ ((False → p4) ∨ p2)) ∧ (p3 ∧ (p4 → ((p4 ∨ (p3 → p3)) ∧ p3)))) ∨ (((True ∧ p4) → ((p4 → p2) ∧ False)) → (p5 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_339492594718590668219752222624 : (p1 → (False ∨ ((((p2 ∨ (p2 → ((p3 → p4) → (((False → p4) ∧ p1) → (p3 ∧ p1))))) ∧ (True → (p2 ∧ p5))) ∨ p3) ∨ (p5 ∨ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113600360648526720540513597746 : (((False ∨ (p1 ∧ ((((p5 → (p3 ∧ p4)) ∨ (True ∨ ((p1 ∧ p4) → (p2 ∧ (p5 ∧ p5))))) → p2) ∨ p2))) ∨ (p4 → True)) ∨ (p4 → p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_120348642977856939774404105797 : (((p3 ∨ (False ∨ ((p4 ∨ ((((False → (p1 ∧ ((p3 ∨ (True → p4)) ∧ True))) → p1) ∧ False) ∧ False)) → (True → p2)))) ∧ p1) → (p2 ∨ p1)) := by
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
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- False on the left can always be used.
      apply False.elim h6
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_649750183239707404396126081133 : (((((((p1 → (p5 ∨ (((p5 → True) ∨ (p3 ∧ ((p1 ∨ p4) ∨ False))) → p1))) → p3) ∨ (p4 ∨ True)) → (p4 ∨ p3)) ∧ (p1 ∧ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323248546073724241076815898742 : (p5 ∨ (((p5 ∨ p1) → (p5 ∧ (((((False → p4) ∧ p3) → False) ∧ p3) ∨ ((p1 ∨ p4) ∧ (((False ∨ False) ∧ p1) → False))))) ∨ (p5 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_221131279800984960764426783364 : (((True ∨ p2) ∨ False) ∧ ((p2 → (((False → True) → (p1 ∧ p5)) ∧ (p3 ∧ p5))) → (((p1 → p2) ∨ False) ∨ ((p2 ∧ (True → p2)) → True)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156681676953114369050004602018 : ((((p2 → (((p3 ∨ p1) ∨ ((p5 ∧ p2) ∨ p2)) ∧ (p5 ∨ (False ∧ p5)))) ∨ (True ∨ p2)) ∧ p5) ∨ ((p3 → (p2 → p2)) ∧ (p2 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52778760079434834488654991478 : ((((p4 → (False → ((p4 ∧ ((p3 ∧ False) → p2)) ∨ p3))) ∧ (p1 ∧ p4)) → ((p2 ∧ (p5 ∧ ((True ∨ False) ∨ p2))) ∧ (p3 ∧ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58694590603854390934513836477 : (((p2 → p3) ∧ (((p2 ∧ ((p3 ∨ (p4 ∨ False)) → (p5 → True))) ∨ p2) ∧ (p4 ∨ (((False ∨ True) ∧ False) ∧ ((p4 ∨ p2) → p1))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_708985411744029959670273618980 : ((((((p5 → p2) → (p4 → p3)) → (p3 ∨ p5)) → (True ∧ (((p4 ∧ (p4 ∧ p3)) ∧ p3) ∨ (False → ((p2 ∨ (False ∧ p1)) ∨ True))))) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39368658546798503257130871845 : (((p3 ∧ (((p5 → (p2 ∨ ((p5 → False) ∧ True))) ∨ (((False ∧ p1) ∧ (p2 ∧ p1)) ∨ p1)) ∧ ((p5 ∧ (p5 ∧ True)) ∧ p3))) ∧ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_520397155715184805119337404626 : ((((p4 ∨ p1) → ((((p4 → ((((p2 ∨ p5) ∨ p1) ∧ (((p4 ∨ p2) → (p4 → False)) ∨ p2)) ∧ p5)) ∨ (False → False)) ∨ False) ∨ p4)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- False on the left can always be used.
    apply False.elim h4
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156666319583078472270895406361 : ((((p3 → (((p1 ∧ (p4 ∧ p2)) → (p5 ∨ False)) → ((True ∨ p4) ∧ (True ∨ p1)))) → p5) ∧ True) ∨ (False → ((p4 ∧ (p5 → p3)) ∧ p4))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37158961341423441813465577685 : (((((((p4 ∨ p3) ∨ (p2 ∨ p5)) ∨ (p4 ∨ ((p1 ∨ (p5 → (p1 ∧ p3))) ∨ p3))) ∧ (p2 → (p3 → (p4 ∨ p3)))) ∧ p3) ∧ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_659305361936813864203618234933 : ((((p5 → (((True ∨ ((False → p2) ∨ (False → ((True ∧ p1) ∨ p3)))) ∧ p3) ∧ (((False ∨ p3) → p5) → (p5 → False)))) ∨ (False ∨ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346366560348057036113856526607 : (p3 → ((False ∧ ((((((p3 ∨ p1) ∨ False) → False) ∧ p2) ∧ (((p3 → False) ∨ ((p2 → True) ∨ (p1 ∨ False))) ∧ p2)) ∧ p4)) ∨ (p3 ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_681210901397760417707564695280 : ((((p3 ∧ (((p1 ∨ True) → (True ∧ p5)) ∨ (p3 ∧ ((p2 ∨ (((False ∧ p1) → False) ∧ p4)) → p1)))) → (p5 ∨ ((p4 ∧ False) ∨ True))) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_312126932311544799523210285870 : (p2 ∨ (True → ((((p3 ∧ (((p5 → (p5 → p1)) ∧ False) ∨ p2)) ∧ p4) ∨ ((p1 ∨ False) ∨ p1)) ∨ (p5 → ((p4 ∧ (False → p2)) ∨ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147915319076233396676473233581 : ((((((((p4 → (p2 ∧ False)) ∧ (True ∨ False)) → True) ∨ p4) → (p1 ∧ p2)) → (False ∧ False)) ∧ (p1 ∨ p5)) ∨ (((p3 ∨ p5) ∨ p1) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_789136591492075454067747532862 : (((p5 ∨ (((True → (p4 ∨ p2)) ∨ ((p1 ∧ p5) ∧ (p1 → ((p2 ∨ p2) → (False ∨ (p3 ∧ (p3 ∨ p4))))))) ∨ (p5 → (p3 ∨ p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112107717470456015192771556693 : ((((p3 ∨ p2) → ((p1 ∧ ((((p5 ∨ p4) ∧ True) ∧ (((p4 → p5) ∧ p5) → p3)) ∧ False)) ∨ (True ∨ (p4 ∨ p1)))) ∨ False) ∨ (p3 → p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_778803518644764074873026624141 : (((p1 ∨ (p5 ∨ (p2 → ((((((p5 ∨ ((False ∨ p1) ∧ p2)) ∨ (p3 ∧ p4)) ∨ p1) ∧ (p4 → p3)) → p1) ∨ ((p5 ∧ False) ∨ True))))) ∨ p1) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199737607033716197754889207320 : (((p2 ∨ ((False → True) ∧ (p5 ∨ p3))) → p2) → ((p1 → p1) ∧ ((((p2 ∧ p4) ∨ ((p1 ∧ (p2 → p3)) ∧ p4)) ∨ True) ∨ (False ∧ False)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150661164221350299152756975127 : (((p4 ∨ ((((p5 → ((p1 ∧ p1) ∧ p4)) ∨ (False ∨ True)) ∧ ((False ∨ p5) ∨ False)) → (p1 ∨ p3))) ∧ p2) → ((p1 → p4) ∨ (False ∨ True))) := by
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
theorem thm_5_vars_178719222710503726122348215843 : ((((p1 → (True ∧ p4)) ∧ p1) → (((p4 ∨ True) ∧ p5) ∧ (False ∧ p3))) ∨ (((p2 ∧ ((p5 → (True → True)) → False)) ∧ (p4 → p2)) → p5)) := by
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
  have h6 : (p5 → (True → True)) := by
    -- Implications on the right can always be decomposed.
    intro h7
    -- Implications on the right can always be decomposed.
    intro h8
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h9 := h5 h6
  -- False on the left can always be used.
  apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_783683077953599082620994159506 : (((p3 ∨ (((True → (p4 ∨ (True → p2))) → p4) ∧ ((p5 ∧ (((p2 → (p2 ∨ p2)) ∧ (p2 ∨ p1)) ∧ False)) ∧ (p1 ∧ (p5 ∨ True))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111089236654671605062262862585 : (((((((True ∧ p2) ∨ False) ∧ False) ∧ ((p5 ∧ (p4 ∨ p3)) → p3)) ∨ (((p4 ∧ (p2 ∧ p1)) ∧ p1) ∨ (p1 → True))) ∧ True) ∨ (p3 ∧ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184088496325354367783788584665 : (((((p5 ∧ p4) ∧ p5) ∨ (((p4 → p4) → p2) ∨ p3)) ∨ True) ∨ (p2 ∧ (p1 ∧ (p1 ∨ ((((True ∧ True) ∨ p5) → (p3 ∨ p4)) ∨ True))))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198675507052264903438179164540 : ((p4 ∨ ((True ∨ (p5 → (p5 ∨ p3))) → p3)) ∨ ((True ∨ p4) ∨ ((((False ∨ True) → p5) ∧ ((p5 → p5) → p5)) ∨ (True → (False → False))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230417613317157895552435699160 : (((p4 ∨ p1) ∧ p3) → ((True ∨ p3) → (True → ((False ∧ ((p4 → False) → True)) ∨ ((p5 ∨ False) ∨ ((((False ∧ p3) → p2) ∧ False) → False)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h1.left
    let h6 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- False on the left can always be used.
      apply False.elim h10
    case inr h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h12
      -- Conjunctions on the left can always be decomposed.
      let h13 := h12.left
      let h14 := h12.right
      -- False on the left can always be used.
      apply False.elim h14
  case inr h15 =>
    -- Conjunctions on the left can always be decomposed.
    let h16 := h1.left
    let h17 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h16
    case inl h18 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
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
theorem thm_5_vars_56637553489229382644879013466 : ((((True ∨ True) ∧ p3) ∧ ((p4 ∧ ((True ∧ (p4 ∨ (p3 → ((p2 ∧ (p3 ∨ (p4 ∨ p3))) → p4)))) ∧ False)) ∨ ((p1 ∨ p1) ∨ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_774820327474984814993310238450 : (((False ∨ ((False → (((p1 ∨ p2) ∨ p4) ∧ p3)) → ((False ∨ p2) ∧ (((p3 ∨ ((p1 ∧ p5) → p3)) ∨ (p1 ∧ p2)) ∨ (p3 ∧ p1))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115576348185467310470612581487 : (((((p3 ∨ True) ∧ p2) ∧ (p5 ∨ p3)) ∧ (((p3 ∧ (p1 ∧ ((False ∨ p4) ∨ False))) ∨ (p2 ∨ p3)) ∧ ((p1 → p2) ∨ p2))) ∨ (p4 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53134969679546580330688634415 : (((((True ∧ (p5 ∧ p3)) ∧ (p3 → (p1 ∧ (True ∧ p5)))) ∧ p5) ∨ ((p5 ∨ (p2 ∨ ((p1 → (True → p3)) → p4))) ∨ (True → True))) ∨ p5) := by
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
theorem thm_5_vars_185261737634029783350855582425 : ((p1 ∧ ((p1 ∧ (p5 ∨ p1)) ∨ ((True ∨ (p3 ∨ True)) → False))) ∨ (((False ∧ p4) → ((((p5 → p2) ∧ p5) → p3) ∧ False)) ∧ (p3 → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h1.left
  let h6 := h1.right
  -- False on the left can always be used.
  apply False.elim h5
  -- Conjunctions on the left can always be decomposed.
  let h7 := h1.left
  let h8 := h1.right
  -- False on the left can always be used.
  apply False.elim h7
  -- Implications on the right can always be decomposed.
  intro h9
  -- One of the premise coincides with the conclusion.
  exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48029048967454119839769134164 : ((((p3 ∨ (((p2 ∨ p1) ∨ (p5 → (p3 ∧ True))) → (p1 → p3))) → (((p1 → True) ∨ (p1 ∨ (p2 → True))) → p2)) → (p3 ∨ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_262298488476755510576601714336 : (True ∧ ((((((p2 ∨ ((p3 ∨ p1) ∧ p2)) ∨ p2) ∨ p2) → ((True ∧ p1) ∧ True)) → (((True ∧ False) ∨ True) → (p2 ∧ (p4 ∧ True)))) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_598133870246705107505644645436 : ((((((True → p3) ∧ p2) ∨ (((p4 ∨ (((p1 → True) → p4) → False)) → (True ∨ (((True ∨ (True ∨ False)) → p5) ∨ True))) → p4)) ∧ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337571172804527795749280577374 : (p1 → ((((((p5 → (((p3 → (p2 ∧ ((p2 ∧ p3) ∧ p2))) → p5) ∧ p1)) → p2) ∨ p4) ∨ p2) → p1) → ((p2 ∨ (p5 → p4)) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_464362464247819288597532120272 : ((((((p5 ∨ (False ∧ p4)) ∧ (((False ∨ p5) ∧ (False → p3)) → p5)) ∧ (True → p1)) → ((((p5 → False) ∨ (False → p4)) ∨ p1) ∨ p1)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- False on the left can always be used.
    apply False.elim h9
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354606165235339118769800501167 : (p5 → ((((((p4 ∨ ((((p2 ∨ p1) ∧ p2) → True) → False)) ∧ p5) ∨ ((p3 ∨ (((p1 ∨ p5) → p2) ∧ p4)) ∨ p1)) → False) ∨ True) ∨ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246629314067151169318074397862 : ((p5 ∧ p3) ∨ (((((((p4 ∨ p2) ∨ ((p4 ∨ True) ∧ (p4 ∧ p4))) ∨ (p1 → p4)) ∨ True) ∧ (p2 ∧ (p2 ∨ p5))) ∨ True) ∨ (p5 ∧ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49231790263220207090556105062 : ((((True → p4) ∨ (((p4 ∧ ((p5 ∧ (p5 ∧ (p2 ∧ (False → p3)))) ∨ p1)) ∨ (p4 → False)) ∧ (p5 ∧ p3))) ∨ ((p4 → True) ∨ p3)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171305672270133674769158062411 : (((((p5 ∧ p3) ∨ ((p1 → (p3 ∧ (False → (p5 ∧ True)))) ∨ False)) ∧ p2) ∧ p3) ∨ ((True ∨ p1) ∨ (False ∧ ((p3 ∧ (p1 ∧ True)) → p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_638190051426661745754151033317 : (((((((p3 ∧ p3) ∨ p4) ∨ ((p5 ∧ p5) ∨ True)) → ((((p5 ∧ (p1 ∨ (True ∧ p1))) → p2) → p4) ∧ ((False ∧ p5) ∧ True))) → False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113092295088757329763509015090 : (((p5 ∨ ((((p4 ∧ p2) ∨ ((True ∧ p4) ∨ (True ∧ p1))) ∧ ((p4 ∧ False) → False)) → (False → ((p2 ∨ p5) → p3)))) → p2) ∨ (False → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161871274306198434701735157033 : ((False → (((p1 ∨ p1) → (p3 ∧ (p3 → (((p3 ∨ True) ∨ (p4 ∧ (False → False))) ∨ True)))) → False)) → ((p5 ∧ (False ∨ True)) → (p3 ∨ p5))) := by
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
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40727142184876151502906948533 : (((((p3 ∧ ((True → (True → False)) ∨ True)) → (False ∨ (False ∨ (((((p2 ∨ True) ∨ p1) → False) → False) → (p3 ∧ False))))) → p5) ∨ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_105078822812013792813705447503 : (((((True → (((True → (p1 ∧ p1)) ∨ p4) ∨ ((p5 ∨ p4) ∨ p2))) → (p1 ∨ (p2 → False))) ∧ p1) ∨ (p4 ∨ (p4 → True))) ∧ (False → p3)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_810162048075670489744689882010 : (((p5 → (((p3 ∨ p2) ∧ (p1 ∨ ((p4 ∧ (((True ∧ False) → (True ∧ p5)) ∧ False)) ∨ False))) ∨ (False ∨ (p4 → ((p4 ∧ p2) ∧ False))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199051854852853819398254259132 : ((((p2 ∧ (p5 → (True → p4))) ∨ p2) ∧ p2) → (((True ∨ ((p2 → p1) ∨ ((p5 ∨ False) ∨ False))) → p1) → (((p1 ∧ p3) ∨ p1) ∨ True))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114661203773195333948381259662 : (((((p2 ∧ p1) ∧ p2) ∧ ((p3 ∧ ((p3 → True) ∨ p4)) ∧ ((True ∨ False) ∧ p2))) ∨ (p3 ∨ ((False ∨ (p3 ∨ p5)) ∧ False))) ∨ (True ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134361235947517217126134777582 : (((p1 ∨ (((((p4 → False) ∧ ((p3 ∨ p1) ∨ ((True → p5) ∧ p4))) ∨ p1) ∨ ((False ∧ p5) ∧ False)) ∧ p1)) ∨ True) ∨ ((p3 ∨ True) ∨ p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_650426855043417448816513858129 : (((((((p4 ∨ p2) ∧ ((p4 ∧ ((p1 ∧ False) → p3)) ∨ p2)) ∨ (p2 ∨ p3)) → ((False ∨ (False ∨ p4)) ∨ (p2 ∨ p3))) ∧ (p3 → True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319054220704431054272324133009 : (p4 ∨ (((False ∨ p5) ∨ ((p2 → (p5 ∨ (p5 ∨ ((p2 ∧ (p5 → p4)) ∧ (p5 ∧ (p2 ∧ p3)))))) ∨ True)) ∨ ((p5 ∧ p5) ∨ (False ∧ False)))) := by
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
theorem thm_5_vars_149929084233306487018148308526 : ((p3 ∨ ((((True ∨ (p4 ∧ p5)) ∧ (p2 ∨ False)) → p5) → ((((False → False) → p4) ∨ False) ∨ (p2 → p2)))) ∨ (p1 ∧ ((p1 → False) ∧ p1))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_746485133690989539222996049059 : ((((p2 ∨ p3) → (p4 ∨ (p3 → ((((True ∧ ((p1 ∨ (p1 ∨ True)) ∧ (True → (True → (False ∨ (p4 ∧ p5)))))) ∨ p1) → p2) ∨ False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185898306515227579259069091192 : (((((((p3 ∧ False) ∧ p1) ∨ p5) ∨ p2) → (p4 ∧ p2)) ∧ p1) → (((p1 ∨ (p2 ∧ (p3 ∨ (p1 ∨ (p4 ∧ p2))))) → False) ∨ (False → p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_751177466455422476159183199167 : (((True ∧ ((False ∧ (True → p3)) ∨ (((p1 ∨ ((False ∨ p1) ∨ p5)) → p1) → (p3 ∨ ((p5 → ((True → (p4 ∨ False)) → p5)) ∨ p5))))) ∨ p5) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_800595716202659411638959804491 : (((p2 → (((((p3 ∨ p1) ∧ (p1 ∨ False)) ∨ (p4 → ((p5 ∨ p4) → p3))) → (((p1 ∧ p2) ∧ (p4 ∨ (p4 ∧ p2))) ∨ p5)) → p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177434027544902912653995226066 : ((True → ((p1 ∨ ((p1 ∨ True) ∨ p3)) ∧ ((p5 → (p1 ∨ p4)) ∨ True))) ∧ ((((p5 ∨ (p2 ∨ (p1 → (p2 → True)))) ∨ False) ∨ p2) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114997861107819127309801560057 : (((((p2 → (p2 → (True → p2))) → p1) ∨ ((p1 ∨ p3) ∨ p5)) ∧ ((True → (((True ∨ p5) ∧ (p1 ∨ False)) ∨ p3)) → p5)) ∨ (p2 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328299617135093639767992990170 : (True → (((p3 → p2) ∧ (((p3 ∧ False) ∧ (p5 ∨ p3)) ∧ ((False → (False → (True ∧ p4))) ∨ (p1 ∨ p4)))) ∨ (p4 → ((p1 ∧ p1) ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60037463551841983348886503178 : (((p1 ∨ p4) → ((p2 ∨ ((p1 → (((p2 ∨ ((False → (p1 ∧ p4)) ∧ (p4 ∧ False))) ∨ p2) → (p1 ∧ p4))) → p1)) ∧ (p3 ∨ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58904071849448292908947253062 : (((False ∧ p5) ∨ (False ∧ (p1 ∧ (((p3 ∧ p4) → (p4 → (p5 ∧ (False ∨ ((True → (False ∨ (p1 ∨ (p5 ∨ True)))) → p1))))) ∧ p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_209108585718227480057308417825 : ((p2 ∨ ((p3 ∨ False) → (p4 → p2))) → ((False → (False → ((True → p4) ∧ p1))) → ((p1 → (((p2 → p4) → p3) → p5)) ∨ (False → p5)))) := by
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
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- False on the left can always be used.
    apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_343596245187012067749756527101 : (p2 → ((p3 → p1) → ((((p5 ∨ False) → (p4 → ((p4 → p3) → ((p5 ∨ True) ∧ p3)))) ∨ p1) ∧ (((True → False) ∨ p5) → (p4 ∨ p5))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h6 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- False on the left can always be used.
    apply False.elim h7
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h8 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h9 : p4 := by
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h10 := h5 h9
    -- One of the premise coincides with the conclusion.
    exact h10
  case inr h11 =>
    -- False on the left can always be used.
    apply False.elim h11
  -- Implications on the right can always be decomposed.
  intro h12
  -- Disjunctions on the left can always be decomposed.
  cases h12
  case inl h13 =>
    -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
    have h14 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h13, we can now drive its conclusion.
    let h15 := h13 h14
    -- False on the left can always be used.
    apply False.elim h15
  case inr h16 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65544808061696511386339504779 : ((p3 ∨ (True → ((((((False ∨ False) ∧ False) ∧ p3) ∧ p5) → p3) ∧ (((((p2 ∨ p5) → (p3 ∧ p5)) ∨ True) ∨ p3) ∧ (p1 ∨ True))))) ∨ p5) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h9 =>
    -- False on the left can always be used.
    apply False.elim h9
  case inr h10 =>
    -- False on the left can always be used.
    apply False.elim h10
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_599461079567661159969841115255 : (((((False ∨ False) ∨ (p1 ∧ (((((True → (p3 ∧ False)) ∨ (p5 → ((False ∨ p1) ∧ p3))) → ((p2 → True) → p5)) → False) ∧ p3))) ∧ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_844498436903884646470609091209 : (((((p5 → (p1 → (False → (p3 → False)))) → ((((p5 ∨ (p4 ∧ ((p4 ∨ p1) ∧ (p4 ∧ True)))) ∧ p4) ∧ True) ∧ (p5 ∧ p5))) ∨ p5) → p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h3 : (p5 → (p1 → (False → (p3 → False)))) := by
      -- Implications on the right can always be decomposed.
      intro h4
      -- Implications on the right can always be decomposed.
      intro h5
      -- Implications on the right can always be decomposed.
      intro h6
      -- Implications on the right can always be decomposed.
      intro h7
      -- False on the left can always be used.
      apply False.elim h6
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h8 := h2 h3
    -- We need to get the right conjuct of h8 based on <expert-advice>.
    let h9 := h8.right
    -- We need to get the left conjuct of h9 based on <expert-advice>.
    let h10 := h9.left
    -- One of the premise coincides with the conclusion.
    exact h10
  case inr h11 =>
    -- One of the premise coincides with the conclusion.
    exact h11
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_226045865878043669695094131318 : (((p5 ∧ p1) ∨ False) ∨ ((p5 ∧ (((False ∨ (p1 → p4)) ∨ p2) ∨ (p5 ∧ (True → False)))) → ((p4 → ((p1 ∧ p3) → (p2 ∨ p5))) ∨ p1))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- False on the left can always be used.
        apply False.elim h6
      case inr h7 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h8
        -- Implications on the right can always be decomposed.
        intro h9
        -- Conjunctions on the left can always be decomposed.
        let h10 := h9.left
        let h11 := h9.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h2
    case inr h12 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h13
      -- Implications on the right can always be decomposed.
      intro h14
      -- Conjunctions on the left can always be decomposed.
      let h15 := h14.left
      let h16 := h14.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h12
  case inr h17 =>
    -- Conjunctions on the left can always be decomposed.
    let h18 := h17.left
    let h19 := h17.right
    -- We want to use the implication h19 based on <expert-advice>. So we show its premise.
    have h20 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h19, we can now drive its conclusion.
    let h21 := h19 h20
    -- False on the left can always be used.
    apply False.elim h21



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345494439391092217042579009520 : (p3 → (((False → (((True → False) ∧ (False → p1)) → (p2 → ((p3 ∨ ((p3 ∧ True) ∧ True)) → p4)))) → (p2 ∧ ((p2 → p3) ∧ False))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



