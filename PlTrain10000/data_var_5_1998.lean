variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263751700941061881234353092053 : (True ∧ ((p5 → ((p3 → p3) ∧ (p2 ∧ ((False ∨ p3) → (p4 ∧ (p1 ∧ (p1 → (p3 → p4)))))))) → (((p4 ∨ (p4 ∨ True)) ∨ True) ∨ p4))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340977877546794829182440635878 : (p2 → (((False ∨ p1) ∨ (((p4 → (p3 → (True ∧ (((p5 ∨ False) ∧ ((p3 ∨ p4) → p3)) ∧ True)))) ∧ (p2 → (p1 → p4))) ∨ True)) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317606705271586114608651726796 : (p4 ∨ (((p1 ∨ ((p4 ∧ p3) ∧ (p2 → (((((p4 → p2) ∧ (p4 ∧ True)) ∨ (((p1 ∨ p2) → p5) → True)) → False) → p4)))) ∧ p5) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52434326198280585795239807839 : ((((True → p1) → (True ∧ (((p2 → p3) → (True → False)) ∨ (p3 → False)))) ∧ (((p2 ∧ p3) → (((p3 ∨ p1) ∨ p1) → False)) ∧ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54317887185705316628574613242 : (((True ∧ (p3 ∧ (((p5 → p5) ∨ False) → p3))) ∧ ((False ∧ (((p2 ∧ (True ∨ (((p2 → False) → True) ∨ p3))) → p5) → p5)) ∨ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116037757398158729048117073878 : (((p2 ∨ ((False → p5) → p1)) → ((p5 → p3) → (p4 ∨ ((True → (p3 ∨ ((p2 → (p3 → (True → p3))) ∨ False))) → p3)))) ∨ (True ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_611252690383104861311288495980 : ((((((p3 → True) ∧ (p5 → ((((p2 ∧ p5) ∧ ((True → (p3 ∨ True)) → (p1 ∨ p5))) → True) → ((p1 ∧ False) ∨ p3)))) → p2) ∨ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328433410637843685348157771662 : (True → ((p5 ∨ ((p5 → p1) → ((((p3 ∨ True) ∨ p4) ∨ (True ∧ p2)) ∧ (p2 → (False ∨ p5))))) ∨ ((p3 ∧ p2) → (p2 ∨ (p1 ∧ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_229055557129343133680003237851 : ((p5 ∨ (p4 ∨ p2)) ∨ ((((p4 ∧ ((p2 ∧ (p4 ∧ ((False → p5) → True))) ∨ p3)) ∧ (p3 ∧ p5)) ∨ (((False ∧ p5) ∨ True) ∨ p1)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_693621477603672930118377236036 : ((((((((p3 ∧ (p5 ∧ ((p5 ∧ p2) ∧ p4))) ∨ p4) ∧ True) ∨ True) ∨ True) ∨ (p3 ∧ (((p1 → True) ∧ p1) ∨ ((p3 ∧ p2) → p4)))) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_84018057247217847525427278306 : (((((((((False ∧ p4) ∧ (False ∧ p5)) ∧ (p5 → False)) ∧ p1) ∧ p2) → p4) → False) ∧ (((False ∨ ((p4 ∨ p5) ∧ p2)) → True) ∧ True)) → p4) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h6 : ((((((False ∧ p4) ∧ (False ∧ p5)) ∧ (p5 → False)) ∧ p1) ∧ p2) → p4) := by
    -- Implications on the right can always be decomposed.
    intro h7
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h8.left
    let h11 := h8.right
    -- Conjunctions on the left can always be decomposed.
    let h12 := h10.left
    let h13 := h10.right
    -- Conjunctions on the left can always be decomposed.
    let h14 := h12.left
    let h15 := h12.right
    -- Conjunctions on the left can always be decomposed.
    let h16 := h14.left
    let h17 := h14.right
    -- False on the left can always be used.
    apply False.elim h16
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h18 := h2 h6
  -- False on the left can always be used.
  apply False.elim h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_98987593786437282380216687769 : ((True → ((((((p4 ∨ (True → p5)) → False) ∨ (p1 ∧ p5)) → (p4 ∨ p1)) → p3) ∧ (p4 ∧ (p2 ∨ (True ∨ (p5 ∨ (p5 ∨ p4))))))) → p4) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_591928195335341795120927938432 : ((((((True ∨ (p1 → (True ∨ p2))) → ((p1 ∧ p1) ∨ (((((p2 → p5) ∧ p4) → (True → p2)) ∧ p5) ∧ p2))) ∨ (p4 ∨ p5)) ∧ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172823459125050398139600967513 : ((True ∧ ((p2 → True) ∧ ((((p3 ∨ True) ∨ ((p5 ∨ False) ∧ True)) → p5) ∧ p3))) ∨ ((((p5 ∨ False) ∨ (p1 ∨ p4)) → (p1 ∧ p3)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217510464726810475472335653689 : ((((p4 ∨ p1) ∧ p1) → p2) → ((((p4 → True) ∨ p4) ∨ p3) ∧ ((p5 → ((True → p3) ∨ (p1 → p5))) ∨ ((True ∨ p5) ∧ (p5 ∨ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_591823482469026160186161628678 : ((((((True → ((p2 ∨ p2) → ((p1 ∧ ((p4 → ((p1 ∧ True) ∧ False)) → p5)) ∧ p5))) ∨ ((p3 ∨ True) ∨ p3)) ∨ (p3 ∧ False)) ∧ True) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_388380988699075233995354375224 : ((((((p2 ∧ ((True → p1) → (p2 → ((p1 ∨ (p5 ∧ (p3 → False))) → (p5 ∧ True))))) ∨ False) → (p3 → (p5 ∧ (p3 ∧ p1)))) ∨ True) ∧ True) ∧ True) := by
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
theorem thm_5_vars_234949725197156391808569733855 : ((True ∧ True) ∧ (p4 → (p2 → ((p5 ∧ ((p5 → (p5 ∧ False)) ∧ (p4 ∨ ((True ∨ True) ∨ (((p4 ∧ p4) ∧ False) → False))))) → (p3 ∨ p3))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h9 : p5 := by
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h10 := h6 h9
    -- We need to get the right conjuct of h10 based on <expert-advice>.
    let h11 := h10.right
    -- False on the left can always be used.
    apply False.elim h11
  case inr h12 =>
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h13 =>
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h14 =>
        -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
        have h15 : p5 := by
          -- One of the premise coincides with the conclusion.
          exact h4
        -- We have shown the premise of h6, we can now drive its conclusion.
        let h16 := h6 h15
        -- We need to get the right conjuct of h16 based on <expert-advice>.
        let h17 := h16.right
        -- False on the left can always be used.
        apply False.elim h17
      case inr h18 =>
        -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
        have h19 : p5 := by
          -- One of the premise coincides with the conclusion.
          exact h4
        -- We have shown the premise of h6, we can now drive its conclusion.
        let h20 := h6 h19
        -- We need to get the right conjuct of h20 based on <expert-advice>.
        let h21 := h20.right
        -- False on the left can always be used.
        apply False.elim h21
    case inr h22 =>
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h23 : p5 := by
        -- One of the premise coincides with the conclusion.
        exact h4
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h24 := h6 h23
      -- We need to get the right conjuct of h24 based on <expert-advice>.
      let h25 := h24.right
      -- False on the left can always be used.
      apply False.elim h25



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_645159285171012786733974374841 : ((((p3 ∨ ((p5 → (True ∧ ((((p2 ∨ True) ∧ p4) ∧ p4) ∨ p5))) ∨ ((False ∧ (((False ∧ p1) ∨ True) ∨ p2)) ∧ (p2 → p5)))) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135028633596264796622964048973 : (((p5 → ((True ∧ (((p2 ∧ False) ∧ False) → p2)) → (((((p5 ∨ False) ∧ p3) ∨ p3) ∨ p1) ∧ p3))) ∧ (False ∨ p3)) ∨ ((False → p5) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307169666882307676174372894405 : (p1 ∨ (False ∨ (p1 → ((((True ∧ False) ∧ p4) ∧ ((p5 ∧ p2) ∧ (((p3 ∨ False) → True) ∧ (False ∨ True)))) ∨ ((p3 → p5) → (p4 → p1)))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_731618449602798579148711430144 : ((((p1 → (p2 ∨ p3)) → (p5 → (((p4 ∨ True) ∧ p1) → (((False ∧ (True ∧ p4)) ∨ ((p4 → p3) → p2)) → (p3 ∨ (p2 ∨ p4)))))) ∨ False) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- False on the left can always be used.
    apply False.elim h6
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h3.left
    let h10 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h11
    case inr h12 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h13 : p1 := by
        -- One of the premise coincides with the conclusion.
        exact h10
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h14 := h1 h13
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h15 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h15
      case inr h16 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h16
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_475837630386256854215443481167 : ((((((((p2 → p2) ∨ p3) ∧ (p5 ∨ p3)) → p3) ∨ p1) ∨ (((((p2 ∧ (((p2 ∨ False) ∧ False) ∧ p4)) ∧ p1) ∧ p2) ∨ True) ∨ p1)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180632960493521119635942319483 : ((((False → ((p5 → p1) → p4)) ∧ p4) ∨ (((p3 → p3) ∨ False) ∧ p5)) → (((p5 ∧ p5) ∧ (p1 ∨ p3)) ∨ ((p3 → p1) ∨ (p4 → p4)))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- One of the premise coincides with the conclusion.
      exact h10
    case inr h11 =>
      -- False on the left can always be used.
      apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_758067831548831900491546833955 : (((p1 ∧ (p1 → ((p1 ∨ ((p1 ∧ (((True ∧ p4) → p3) ∧ ((p1 ∨ (p3 → True)) → p2))) → ((p2 ∨ True) ∨ False))) → (p2 → False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_787925059393561009024561095870 : (((p4 ∨ (p3 → (p4 ∨ (((p1 ∧ (p4 ∧ False)) ∨ p4) ∧ (((p3 → (p2 ∨ (True → p3))) ∧ False) ∧ ((p5 ∨ p2) → (p5 → p2))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59769149574778263980675187061 : (((p1 ∧ p5) → ((((p1 ∨ p4) ∧ p1) ∨ p1) → ((p4 ∧ ((((p2 ∨ p3) ∧ True) ∨ (p2 ∨ p2)) ∧ p2)) ∨ (True → (False ∨ p3))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246497762998146358144098759148 : ((p5 ∧ p1) ∨ ((((p4 ∨ ((p5 → (p3 ∨ False)) ∧ True)) ∨ p1) ∨ (((True ∧ (p1 → (p2 ∧ p3))) → ((p2 ∧ p5) ∨ p5)) → p5)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61420632421636315314671560880 : ((p1 ∧ ((((p5 → True) ∧ ((((False ∧ (p3 ∧ (False ∧ p1))) ∨ p2) ∧ False) ∨ (True ∧ (p5 → (p3 → False))))) ∧ (p4 ∧ True)) → p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328710070900456309008862709502 : (True → (((p3 ∨ p5) ∨ (((p3 ∨ p4) ∧ (p5 ∧ (False → True))) → False)) ∨ ((p4 ∨ ((False ∨ (p2 → (True ∨ True))) ∧ p2)) → (True ∨ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- False on the left can always be used.
      apply False.elim h7
    case inr h8 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159583174267754272890971124341 : (((p1 → (((True ∧ (True → True)) → ((True ∧ p1) ∧ ((p4 ∧ (p2 ∧ p2)) → p3))) → p5)) ∧ p5) → (((p4 ∨ p5) → p3) → (True ∧ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h5 : (p4 ∨ p5) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h5
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147351017372995584739217248844 : (((((True ∧ ((False → (False → p5)) ∧ True)) → ((p1 ∨ p3) ∧ (p5 ∧ p4))) ∧ (p2 ∧ (p2 ∨ p2))) ∨ p5) ∨ ((False ∨ (p4 ∨ p4)) → p4)) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h5 =>
      -- One of the premise coincides with the conclusion.
      exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_750235295470051670848655758455 : (((True ∧ (((((p1 ∧ (True ∨ (p4 ∧ ((p3 ∧ p3) → (True ∧ (((False ∧ p2) ∨ True) ∨ p4)))))) → False) ∨ True) ∨ p1) ∨ (p4 ∧ p2))) ∨ p2) ∧ True) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_266062493763764571397333543650 : (True ∧ (p2 → ((True → (((((p5 ∧ False) ∨ (p1 ∨ (p2 → (p1 ∧ False)))) → (((p1 ∨ False) ∧ (p1 ∨ True)) → p5)) ∨ p3) → p3)) ∨ True))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55579713795342943179246902741 : (((p1 ∨ (True ∧ (p4 ∨ (p4 ∨ p3)))) → (((p1 ∨ (p5 ∨ p2)) ∨ (((p4 ∨ (True → p5)) ∨ False) ∨ False)) ∧ (p4 ∧ (False ∧ p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230926437337940924482880820679 : (((p3 ∧ p1) ∨ False) → (((p1 ∨ ((p4 → ((p5 ∧ p3) ∨ True)) → (((((True ∨ True) ∧ (p2 ∧ False)) ∨ p1) ∧ p5) ∨ p5))) → p4) ∨ p3)) := by
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
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52462150721895426691585141540 : (((False ∨ ((True ∧ p2) ∧ (((p5 ∨ (p2 ∧ (p3 ∧ False))) ∨ p1) ∨ p3))) ∧ ((True ∨ (p3 ∨ (True → p5))) → (p5 ∧ (p2 ∧ p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322400957460283938814312365330 : (p5 ∨ ((((((True ∨ (p3 ∨ p2)) ∧ p3) ∧ (True ∨ p5)) ∨ (p4 → p3)) ∧ (((False ∧ (p5 → (p1 ∨ (p4 → p5)))) ∨ p3) ∨ p2)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_658115875015608875508615464184 : ((((p4 ∧ (((((False ∨ (p2 ∧ ((((True → p1) → p1) ∧ p5) ∧ p1))) ∧ (p5 → p3)) ∨ True) ∧ (p1 ∧ p4)) ∧ True)) ∨ (p1 ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_704378443818595818758255002877 : ((((((p2 ∨ p5) ∧ p5) ∧ (p5 ∧ ((True → False) ∨ False))) → ((((p4 ∧ (p5 ∧ p4)) ∧ (False ∧ p1)) ∧ p4) ∨ (p4 ∧ (p2 → p3)))) ∨ p3) ∧ True) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h3.left
    let h8 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
      have h10 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h9, we can now drive its conclusion.
      let h11 := h9 h10
      -- False on the left can always be used.
      apply False.elim h11
    case inr h12 =>
      -- False on the left can always be used.
      apply False.elim h12
  case inr h13 =>
    -- Conjunctions on the left can always be decomposed.
    let h14 := h3.left
    let h15 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h15
    case inl h16 =>
      -- We want to use the implication h16 based on <expert-advice>. So we show its premise.
      have h17 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h16, we can now drive its conclusion.
      let h18 := h16 h17
      -- False on the left can always be used.
      apply False.elim h18
    case inr h19 =>
      -- False on the left can always be used.
      apply False.elim h19
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150054372796363020284056749112 : ((True → ((p5 → (((p2 ∧ ((p4 ∧ (((False ∨ p4) ∧ p3) ∧ p2)) ∨ (False ∨ True))) ∧ p5) ∨ p5)) ∨ p2)) ∨ ((p4 ∨ False) ∧ (False ∧ p1))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133536951988618625027754812285 : ((((((p5 ∧ p1) ∨ p2) → (p5 → (p3 ∨ (((False ∧ ((True ∨ p4) ∨ p5)) ∧ (True ∨ False)) → True)))) ∧ p3) ∧ p5) ∨ (False ∨ (True ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_658357857518658465500312401589 : ((((False ∨ ((False ∧ (p5 ∧ (True → (p5 ∧ ((False ∨ ((True ∨ (p1 → ((p2 ∨ True) ∧ p5))) ∧ p1)) ∧ p3))))) ∨ False)) ∨ (p3 → p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346605314856403395146105601220 : (p3 → ((((((p4 ∧ p4) → False) → (p2 ∨ (p5 ∧ p3))) → ((p3 ∧ ((p3 ∨ p4) → p3)) → p1)) → (p5 ∧ p4)) ∨ (p2 ∨ (p1 ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117281597804310852573800090791 : ((False ∧ ((False ∨ ((((p1 ∨ p5) → p1) ∧ p1) ∨ (((p1 → p3) ∧ True) ∨ ((True → ((p1 → p3) ∨ p1)) → p3)))) ∨ True)) ∨ (False → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149887959054273617189067292704 : ((p2 ∨ ((p2 ∨ (p3 ∧ p5)) → (p2 → (((False ∨ p5) → ((p3 ∧ (True ∧ p4)) ∧ p4)) ∧ (p5 ∧ p5))))) ∨ (((p5 ∨ p4) ∨ True) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323253987653946910044718881744 : (p5 ∨ ((p1 ∧ (False ∧ ((True ∨ p2) → (p5 → (((False ∨ ((p4 ∧ p2) → ((p5 ∧ p5) ∨ p3))) ∧ p4) ∨ (True ∨ p5)))))) ∨ (p5 → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134571530375637292334804082581 : ((((((True ∨ ((p1 ∧ (p5 → (p5 ∨ p2))) ∧ True)) ∨ (p5 ∧ p5)) ∨ (p4 ∧ (p2 → p5))) ∧ (p2 → p2)) → p1) ∨ (p2 ∨ (True ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133519058790242896804903668686 : ((((((p3 → ((p1 ∨ (p5 → p1)) → (p3 ∨ (p5 ∧ (((p1 ∧ p3) ∧ p2) ∨ True))))) ∨ p4) → p5) ∧ p3) ∧ False) ∨ ((True ∨ True) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_789671900853618050741043004539 : (((p5 ∨ ((p2 ∨ ((p3 ∧ p4) ∨ (p2 ∨ p5))) ∨ ((((p2 → p2) ∨ (True → (p3 ∧ p5))) ∧ (p3 ∨ p3)) ∨ (p3 → (p2 ∧ p4))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230245452538720322875230959376 : (((False ∨ True) ∧ True) → ((p2 ∨ ((p3 ∧ (p1 ∨ (p1 ∧ p5))) ∨ (p3 → ((p2 → (p4 ∨ p4)) ∨ (True ∧ True))))) ∨ (p4 ∧ (False ∧ False)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137794488168960933165108551865 : ((p2 ∨ (p4 ∧ ((((p1 ∧ (p2 → p3)) → (p4 → p4)) ∧ p3) → (p4 ∨ (p5 ∧ (p1 ∧ (p4 ∨ (p3 → True)))))))) ∨ ((p2 → True) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_255667606058377461142286828502 : ((p5 ∧ p5) → ((((p5 ∧ False) → (True → (p5 ∧ ((p3 ∨ p5) → ((False ∧ p1) ∨ True))))) → (((p5 → True) → p2) ∨ (True ∨ p2))) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_739085397761583813445568850465 : ((((p3 ∧ p4) ∨ (p5 ∨ ((((p3 ∨ ((p1 ∨ p2) ∧ p2)) ∨ p4) → p2) ∨ ((((p3 → p4) ∧ False) ∨ p2) ∨ (False ∨ (p4 → True)))))) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_115813501233156250714487511309 : ((((p5 → (p1 → False)) → False) ∧ ((p3 → (p4 ∨ ((False ∧ (((p5 → ((p2 → True) ∧ p4)) ∧ p5) ∧ p2)) ∨ p2))) ∨ p5)) ∨ (True ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117294375204615961615298871034 : ((False ∧ ((p5 → ((p5 ∨ ((p1 → (p2 ∧ p4)) ∧ (((p2 ∧ p3) ∧ (False ∨ p5)) ∨ False))) ∨ ((p1 ∨ p5) ∨ p4))) → False)) ∨ (False → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112685872079268097720337482486 : (((((p1 → ((p2 ∨ (p4 ∨ (True ∨ p5))) ∨ (((p3 ∨ True) ∨ True) ∧ p5))) → False) ∧ (((p4 → p2) → p3) ∧ p3)) → p5) ∨ (p5 ∧ True)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h6 : (p1 → ((p2 ∨ (p4 ∨ (True ∨ p5))) ∨ (((p3 ∨ True) ∨ True) ∧ p5))) := by
    -- Implications on the right can always be decomposed.
    intro h7
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
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h8 := h2 h6
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_745512020954197226670457263873 : ((((True ∨ False) → ((False ∨ ((p3 → (p3 → ((False ∧ ((p1 → ((p2 → p4) ∧ p4)) ∧ p2)) ∨ (False ∧ (p3 ∨ False))))) ∨ True)) ∨ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136671151295920333231339700098 : (((p3 ∨ (p5 ∧ p1)) → ((((True ∨ (p4 ∧ (p4 → (((p2 ∧ (p2 → p3)) → p2) → p4)))) → p2) ∧ p5) ∨ True)) ∨ ((p1 ∧ True) ∧ p3)) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136800213852841067513886502664 : (((p2 → p5) ∧ ((p1 ∨ (p4 ∨ p5)) → ((p2 ∨ (p2 ∨ p5)) ∧ ((p2 ∧ ((p2 ∨ (p4 → True)) ∨ False)) ∨ False)))) ∨ ((p2 ∨ True) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38505544775691777832316239244 : (((((p2 → p4) ∨ (p3 ∧ (((p5 ∧ p3) ∨ (p5 ∧ p3)) ∧ p5))) ∨ (p3 → ((p3 ∧ ((p5 → p1) ∨ p2)) ∧ (p3 → p1)))) ∧ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64755811425605268917888044063 : ((p2 ∨ ((((p1 ∧ p4) ∨ p4) → ((p1 ∧ True) ∨ (((p2 ∧ p4) ∧ (((p2 → p3) ∨ p3) ∧ (p2 ∨ p3))) ∧ (p2 ∧ p1)))) ∧ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_765696797120733944956360258101 : (((p4 ∧ ((((p3 ∧ ((p5 ∧ p1) ∧ p5)) ∧ True) ∧ (p2 ∧ p5)) ∧ (((True ∧ p1) → (p1 ∧ (p3 ∨ (p5 → (p2 → p2))))) → p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260531910410725091837552345062 : ((p3 → p1) → ((((p4 → (p3 ∨ p2)) ∧ (p1 ∧ (True → p3))) ∧ (p2 ∨ ((p2 → p5) → ((p1 ∨ (False → (p2 → p2))) → True)))) → p3)) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h7 := h6.left
  let h8 := h6.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h9 =>
    -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
    have h10 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h8, we can now drive its conclusion.
    let h11 := h8 h10
    -- One of the premise coincides with the conclusion.
    exact h11
  case inr h12 =>
    -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
    have h13 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h8, we can now drive its conclusion.
    let h14 := h8 h13
    -- One of the premise coincides with the conclusion.
    exact h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_302752463009240772516846211508 : (False ∨ (p4 ∨ ((p4 → (((p3 → (p5 ∨ ((p2 ∨ ((p1 ∨ p2) ∨ p3)) ∧ ((p3 → (p3 ∨ p3)) ∧ False)))) ∨ p3) ∧ p1)) ∨ (p2 ∨ True)))) := by
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
theorem thm_5_vars_608406470943106605968218587994 : (((((((((p5 ∧ ((p3 → p3) → False)) ∧ (p2 ∨ ((p3 ∧ p2) → (p2 → ((p4 ∧ p3) → True))))) ∨ p5) ∧ p2) → p4) ∨ p2) ∨ True) ∨ False) ∧ True) := by
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
theorem thm_5_vars_57242346333332688989357423912 : ((((p2 ∧ p3) → p5) ∨ (p5 → ((p4 ∨ ((p3 → False) ∧ ((p1 ∨ p4) ∨ False))) ∧ ((((p1 → p5) → True) ∧ p3) ∧ (p5 ∨ p2))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_788702588178872205847909065795 : (((p5 ∨ (((((p4 ∨ (p4 ∧ (False ∨ p2))) → True) ∧ p5) ∨ ((p4 → p2) ∧ (((p1 ∧ p5) ∨ True) → (p3 → (True → False))))) → p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48430007697551169691755767680 : (((p3 → (True → (True ∧ (p4 ∨ (p1 ∧ ((p5 ∨ ((((p3 ∨ True) → p2) ∧ (p4 → (True ∨ True))) ∨ p1)) ∧ p2)))))) → (p2 ∨ True)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55916629393637906549143640327 : (((True → ((False → True) → True)) ∧ (((((p4 → (p2 → p2)) → p1) ∨ (p5 → False)) ∨ p5) → ((p4 ∧ p2) ∨ ((p3 ∨ p1) ∨ p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117538392028445401455384033945 : ((p2 ∧ ((((p2 ∧ (p3 ∧ False)) → ((p2 → p5) ∨ True)) ∧ (p2 → (p2 ∨ ((p1 ∨ (p5 → False)) ∨ p2)))) → (p1 → p4))) ∨ (False ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51866680544432784994801183044 : (((((p1 ∧ (((False ∨ False) ∨ p4) ∨ (True ∨ True))) ∨ ((p5 ∨ True) ∧ p2)) ∨ False) ∨ ((p1 → (p1 ∨ p3)) ∨ (p2 ∨ (True ∧ p1)))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_696053052876922164546569410103 : ((((p3 ∧ ((True → ((p5 → p5) ∧ p2)) ∨ (True ∨ (p1 ∨ (p3 ∨ p2))))) → (p4 ∨ ((p2 ∨ (p1 ∧ p4)) ∨ (True ∧ (False → p2))))) ∨ False) ∧ True) := by
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
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Implications on the right can always be decomposed.
    intro h5
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- Implications on the right can always be decomposed.
      intro h8
      -- False on the left can always be used.
      apply False.elim h8
    case inr h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- True on the right can always be proven directly.
        apply True.intro
        -- Implications on the right can always be decomposed.
        intro h11
        -- False on the left can always be used.
        apply False.elim h11
      case inr h12 =>
        -- Disjunctions on the left can always be decomposed.
        cases h12
        case inl h13 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- True on the right can always be proven directly.
          apply True.intro
          -- Implications on the right can always be decomposed.
          intro h14
          -- False on the left can always be used.
          apply False.elim h14
        case inr h15 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h15
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305580769962271496849713227636 : (p1 ∨ ((((p3 → True) ∧ (p5 ∧ (((False ∧ True) → False) → p3))) ∨ p3) ∨ ((((p3 ∧ (False ∧ p2)) ∧ p1) ∨ (True ∨ (p4 ∧ p5))) ∧ True))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62512347732097407368168426391 : ((p3 ∧ (p3 ∧ (((p3 ∧ (p5 ∧ ((p5 ∨ ((p5 → p1) ∨ (False ∨ (True → p4)))) ∧ p2))) → p4) → (p2 → ((p3 ∨ p3) ∧ p4))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_141387690197117453292871225346 : ((((True ∧ (False ∧ True)) → False) → (p2 ∧ (p1 ∧ ((((p4 ∨ p4) → ((p2 → p1) ∨ True)) ∨ p1) → (False ∧ False))))) → ((p2 ∧ p4) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((True ∧ (False ∧ True)) → False) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- False on the left can always be used.
    apply False.elim h6
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h8 := h1 h2
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- We need to get the right conjuct of h9 based on <expert-advice>.
  let h10 := h9.right
  -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
  have h11 : (((p4 ∨ p4) → ((p2 → p1) ∨ True)) ∨ p1) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h12
    -- Disjunctions on the left can always be decomposed.
    cases h12
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
  -- We have shown the premise of h10, we can now drive its conclusion.
  let h15 := h10 h11
  -- We need to get the left conjuct of h15 based on <expert-advice>.
  let h16 := h15.left
  -- False on the left can always be used.
  apply False.elim h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199432006109562813480861761546 : (((True ∧ ((p2 ∨ p4) → (True ∧ False))) ∨ p2) → (((p1 → False) ∨ ((True ∧ False) → p3)) ∧ ((False ∨ True) ∨ ((p1 ∨ (p2 → False)) ∨ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- False on the left can always be used.
    apply False.elim h11
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h12 =>
    -- Conjunctions on the left can always be decomposed.
    let h13 := h12.left
    let h14 := h12.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h15 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213808725629974142071438825946 : (((p3 ∧ (p4 ∧ True)) ∨ p2) ∨ ((p2 ∨ ((((((p3 ∧ True) ∧ p5) → p2) ∧ p1) ∨ p5) ∨ ((p1 → (False → True)) ∨ p2))) ∨ (True ∧ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263916319550109329268175772655 : (True ∧ (((((p4 ∧ (((p1 ∨ True) → p4) ∧ p1)) → p2) ∨ (p3 ∧ p3)) → p5) → (((True ∧ p5) → False) ∨ (False → (p5 ∨ (p3 → p4)))))) := by
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
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184398592234396081859119270347 : (((((p5 ∧ (p4 → (False → p1))) ∧ p2) ∧ p2) ∧ (p1 ∧ True)) ∨ ((p4 → True) ∧ ((p4 ∧ p3) ∨ (p4 → (p5 ∨ (p2 ∨ (False → p4))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_232052956955150409863166273486 : (((p3 ∨ p5) → p2) → ((p4 ∧ (p5 ∧ (p3 ∨ (p5 → (((True ∨ p2) ∧ p1) ∨ p3))))) ∨ (((p1 ∨ (p2 → p1)) ∨ p3) ∨ (True → True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64985852646343179446255551312 : ((p2 ∨ ((False → ((False → p1) ∨ False)) → ((p1 ∧ (p3 → p1)) ∨ (True → (p1 ∨ ((p3 ∧ ((p2 ∧ p2) ∨ (p4 ∧ p1))) → True)))))) ∨ p1) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39444881147638397745482890253 : (((p5 ∧ (((p5 → ((((p3 → True) ∨ p5) ∧ p4) ∨ False)) → (p5 ∧ ((p3 ∨ (True → (p5 ∧ True))) ∨ p1))) → (p1 → p3))) ∧ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_255600778748147308270472085000 : ((p5 ∧ p4) → ((((p2 ∧ (((False → (p5 ∨ (p5 ∧ (False ∨ (p2 → p2))))) ∨ (p5 ∨ True)) ∧ p3)) ∨ p2) ∨ ((p3 ∧ p1) ∨ p5)) ∧ p4)) := by
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
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259018390100142728723406218036 : ((True → p4) → (((p2 ∨ ((False → ((((True ∧ True) ∧ False) ∨ p3) → (False ∨ p1))) ∨ ((p2 ∧ (False ∨ p4)) → False))) → p1) ∨ (False → p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234255480147910340981659702376 : ((False → (p5 ∨ False)) → ((((p3 → p3) ∧ (((False ∨ p3) ∨ ((p1 → ((p1 → p5) ∧ (False ∧ p1))) ∨ True)) → False)) → p4) ∨ (p1 → p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h5 : ((False ∨ p3) ∨ ((p1 → ((p1 → p5) ∧ (False ∧ p1))) ∨ True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h6 := h4 h5
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199426489071524694786690351705 : ((((False → p5) → (False ∨ (True ∧ p4))) ∨ p5) → ((False ∨ (p5 ∨ (p5 ∨ ((p5 ∨ (p1 → (True ∧ (p4 ∨ p2)))) → p4)))) ∨ (p4 ∧ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h3 : (False → p5) := by
      -- Implications on the right can always be decomposed.
      intro h4
      -- False on the left can always be used.
      apply False.elim h4
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h5 := h2 h3
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- False on the left can always be used.
      apply False.elim h6
    case inr h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- One of the premise coincides with the conclusion.
        exact h9
      case inr h12 =>
        -- One of the premise coincides with the conclusion.
        exact h9
  case inr h13 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137965613711218115598237267752 : ((p5 ∨ (((((((((p3 → p4) ∨ p1) ∨ p1) → True) → (p2 ∨ False)) → p4) → p5) ∧ p4) ∨ (p3 → (True ∨ False)))) ∨ ((False ∨ p5) ∧ p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51111977465040379533756243491 : (((((False → (p2 ∨ ((((p2 ∧ True) ∨ p4) → (p2 ∨ (False ∧ p3))) → p1))) ∧ p4) ∨ p4) ∨ (((True ∧ (p3 ∨ p3)) ∨ p2) ∨ True)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39071435082495246575374057051 : ((((False ∨ p1) ∨ (((((((p3 → p2) ∨ p1) ∧ ((p4 ∨ p4) ∨ p3)) ∨ p4) ∧ p3) ∨ False) ∧ (False ∧ ((p1 ∧ False) → False)))) ∧ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_712088769897889462275191282967 : (((((p5 ∧ ((p5 ∨ p2) → p3)) ∨ p3) ∨ ((True → (False ∧ p5)) → ((p5 ∧ ((((True ∨ False) → p2) ∧ p3) ∧ (False → p4))) ∨ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58826003364472302622880659975 : (((p5 → p5) ∧ (p2 ∨ (((p2 ∧ (((p5 ∨ (p3 ∧ p4)) ∨ p2) ∧ p1)) ∨ p3) ∨ ((((p5 ∨ (p1 → True)) → p2) ∨ p4) ∨ p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_786493825230187486154841113211 : (((p4 ∨ ((p2 ∧ ((p2 → (((p1 ∧ (False ∧ p3)) ∨ True) ∨ False)) ∧ p2)) ∨ ((p2 → (False ∨ ((p1 ∧ False) ∧ False))) ∨ (p4 ∧ p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309822385430117810898465636235 : (p2 ∨ ((p4 → ((((((p4 ∨ p4) ∧ p3) ∨ (False ∧ False)) → True) ∨ (True → ((p3 ∨ p1) → p1))) → p1)) ∨ (p5 ∨ ((p5 → p5) ∨ p3)))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_123174131631793504796674967700 : (((p4 ∨ ((((p3 ∧ p4) ∨ p2) → (((False ∧ (p1 ∧ (True ∧ (p3 ∨ p2)))) ∨ True) ∨ True)) → p2)) → ((p3 → p5) ∧ True)) → (p5 → p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150742803589383191544901344679 : (((((True ∧ ((p4 → ((True → (p5 ∧ p2)) → (True → p1))) ∨ p2)) ∧ ((p3 ∧ p3) → False)) ∨ p2) ∨ True) → (p2 → (p2 ∨ (p3 → p2)))) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- Conjunctions on the left can always be decomposed.
      let h7 := h5.left
      let h8 := h5.right
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h2
      case inr h10 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h10
    case inr h11 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h11
  case inr h12 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_705971681341061166577429683254 : (((((p5 ∨ (True ∧ p2)) → ((p4 ∧ p4) → p5)) ∧ (p4 → (p1 → ((p2 ∨ p3) → (True ∧ ((True ∧ (p5 ∧ (p1 ∧ p3))) ∨ p3)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244684735967189556995748498938 : ((p1 ∧ True) ∨ (((((True ∨ (((p4 ∧ False) → p5) ∧ p2)) → False) ∧ (((p1 ∨ p5) → (True → p5)) ∧ p5)) → (True → p3)) ∧ (p5 ∨ True))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h7 : (True ∨ (((p4 ∧ False) → p5) ∧ p2)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h8 := h3 h7
  -- False on the left can always be used.
  apply False.elim h8
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160905526604803182170183555904 : (((p4 → ((p1 ∨ True) ∨ p2)) ∨ ((p1 → False) → (((True ∧ p3) ∧ (False → (True → p4))) ∧ p5))) → (p3 → ((p2 ∨ (p3 ∨ p4)) ∨ p3))) := by
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
theorem thm_5_vars_303784168216728077312866931072 : (p1 ∨ ((((((False ∨ (((p3 ∨ p3) ∨ (p4 ∧ p4)) → p3)) ∧ ((p4 ∨ (p5 ∨ p2)) → (p1 ∨ p2))) → (p5 ∧ False)) ∧ p3) → p1) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



