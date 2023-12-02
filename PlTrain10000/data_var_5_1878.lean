variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_352841073042119003786581935028 : (p4 → ((p3 → True) → (p2 ∨ ((p4 → (True ∨ p5)) → (((p2 ∨ (p2 → p3)) → False) ∨ (p1 → ((p1 ∧ (True ∨ (True → p3))) → True))))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305194098167177372899192454866 : (p1 ∨ ((p2 ∨ (p5 → ((((p3 ∨ p2) → p1) ∧ False) ∧ (False ∨ (p4 ∨ ((p1 ∧ p4) ∨ (p5 → p3))))))) ∨ ((p5 ∧ (p4 ∨ False)) → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_931397644218927452143574468723 : ((((p2 ∨ (((p5 → (p4 ∨ (p4 ∨ p3))) ∨ p2) ∨ True)) → (p5 ∧ (((False → p3) ∧ p1) ∧ (((True → (p5 ∧ p2)) ∨ False) → True)))) → p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p2 ∨ (((p5 → (p4 ∨ (p4 ∨ p3))) ∨ p2) ∨ True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the left conjuct of h3 based on <expert-advice>.
  let h4 := h3.left
  -- One of the premise coincides with the conclusion.
  exact h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_16742335303864993194537084038 : ((((True ∧ (p3 ∧ (p1 ∧ ((True ∧ p2) → (False ∧ ((p4 ∨ p2) ∨ (p1 ∨ p5))))))) → ((p4 ∧ p1) ∧ p1)) ∨ ((p1 → p1) ∨ p3)) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_649765516386625907702765412102 : (((((((((((p3 → p3) → p1) → p5) ∧ p4) → p3) → (p4 → p3)) ∧ (p5 → ((p1 ∨ p1) ∨ True))) → (p5 ∧ p4)) ∧ (p1 ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116704178377558086055321364334 : (((p1 ∧ False) ∨ ((p2 → ((p3 ∨ False) ∧ ((((p3 ∧ (True → True)) → (p5 ∧ (True ∧ p5))) → p5) ∧ (p2 ∧ p4)))) ∧ p4)) ∨ (False → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63897834773521824627713538349 : ((False ∨ (((((True → False) ∧ (p3 ∨ (False ∧ False))) ∧ (p1 → (((p1 ∧ True) ∨ p5) ∧ True))) → (True ∧ (p2 ∨ (p4 ∨ p2)))) ∧ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48424317400247751546861363002 : (((p3 → ((((p4 → ((True → ((p2 ∨ p3) ∧ p3)) ∨ True)) ∨ (p1 ∨ p2)) ∧ (p2 → True)) → (p5 → (False → p1)))) → (p2 ∨ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310665690479188085566413588733 : (p2 ∨ ((((p5 ∨ p5) → p4) → p5) → (((p3 → p2) ∨ (p4 → (p4 ∧ (p4 ∧ p5)))) ∧ ((False → ((False ∨ True) ∧ (True → p1))) ∨ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : ((p5 ∨ p5) → p4) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h6 =>
      -- One of the premise coincides with the conclusion.
      exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h7 := h1 h3
  -- One of the premise coincides with the conclusion.
  exact h7
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h8
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h8
  -- Implications on the right can always be decomposed.
  intro h9
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58582346177757242684262935845 : (((True → p4) ∧ ((((True → p4) → (False → (False ∧ p2))) ∧ p1) → ((((True → p3) ∧ True) ∧ p4) ∧ ((p1 → True) ∧ (p3 ∨ False))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258312265934253775756595277820 : ((p5 ∨ True) → ((p2 ∨ p2) ∨ ((False ∨ ((p5 → p3) ∨ p5)) → ((True → (p2 ∨ p3)) ∨ (p2 → ((p1 → p4) ∨ ((p3 → True) ∨ p2))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- False on the left can always be used.
      apply False.elim h4
    case inr h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h7
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h7
      case inr h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h9
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h9
  case inr h10 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h11
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- False on the left can always be used.
      apply False.elim h12
    case inr h13 =>
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h14 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h15
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h15
      case inr h16 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h17
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_765117153976783475090735383550 : (((p4 ∧ ((((p5 ∨ ((p4 ∨ (p3 ∧ p2)) ∨ p4)) → (((True ∧ False) → (True ∨ p3)) ∧ (p4 ∨ (True ∧ p3)))) ∨ p3) ∨ (True ∨ True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_655627953696353341518390559746 : (((((False → ((((p4 ∨ (p5 → ((((p2 ∨ p4) → p1) ∧ (False ∨ p4)) → p1))) → p4) → False) → p4)) → (p1 ∨ p4)) ∨ (p2 ∨ True)) ∨ False) ∧ True) := by
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
theorem thm_5_vars_172009413986877008503455616534 : (((((((p4 ∨ True) ∧ p4) ∧ (p1 ∨ p2)) → p3) → (p3 ∧ p5)) ∨ (p3 ∨ False)) ∨ (p5 ∨ (p5 → ((False ∧ p1) → ((False ∨ False) ∧ p5))))) := by
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
theorem thm_5_vars_323672778176777125691864389988 : (p5 ∨ (((((p4 ∨ p4) → p2) → p3) → (((True ∨ p3) → (p4 ∨ (p3 → p2))) → (p4 ∧ (False → p5)))) ∨ (p2 ∨ (p5 → (p4 → True))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_706587828339301533554047507053 : ((((p1 → ((p3 ∨ p3) ∧ ((True ∧ p3) ∧ p2))) ∧ (((True → p5) ∧ (False ∨ True)) → (p4 → (((p1 ∨ (p2 → p1)) ∧ p3) ∨ p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336501443057391115027271589314 : (p1 → ((((p2 → ((((((p4 ∧ p3) → p1) ∧ p3) → False) ∨ ((p5 ∨ (p1 ∧ p1)) ∨ p1)) ∨ (p1 ∨ (p1 ∨ p5)))) → False) ∧ p1) → p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h5 : (p2 → ((((((p4 ∧ p3) → p1) ∧ p3) → False) ∨ ((p5 ∨ (p1 ∧ p1)) ∨ p1)) ∨ (p1 ∨ (p1 ∨ p5)))) := by
    -- Implications on the right can always be decomposed.
    intro h6
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h7 := h3 h5
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308471017879734272328987371794 : (p2 ∨ ((((True → (((((p2 ∧ p5) ∨ False) ∧ ((p1 ∨ p5) → True)) → (p3 ∧ True)) → (False → p5))) ∨ (p5 ∨ True)) → (p1 ∧ p3)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200431223542968562283745135596 : (((p2 ∨ p5) ∨ ((False → p2) ∨ (p1 → p3))) → ((((p2 ∨ False) ∧ True) ∨ ((True ∨ ((p3 → p4) → p1)) ∨ (p1 ∨ p5))) ∨ (p3 ∧ p2))) := by
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h4 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_69045438985998638515267468433 : ((p5 → (((p5 ∨ (p1 ∨ p1)) ∧ ((p2 ∨ ((True ∨ p4) → (True ∧ True))) → ((p2 ∧ ((p4 ∨ (False ∨ p1)) ∨ p1)) ∨ False))) ∨ True)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53407045482915174883858887078 : (((((((p5 → (p4 → p1)) → p1) → True) → True) → (p5 ∧ p1)) → ((p2 ∧ (p4 ∧ True)) ∨ (p4 ∨ (((True → True) → True) → p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51792464824224924092496156590 : (((True ∨ ((p5 ∨ False) ∨ ((False ∨ p1) → (p1 ∨ ((p2 ∧ (False ∧ p5)) ∨ p1))))) ∧ (p4 ∨ (((True ∨ (p5 → p2)) → False) ∨ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119256164957424677949818521131 : ((p2 → (p4 ∨ (p1 → (((p2 ∨ p2) → False) ∨ (((p2 ∨ (p2 ∧ p2)) ∧ (True ∧ (((p2 ∨ p3) → p4) → p2))) ∧ p5))))) ∨ (True ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_609641365025756003136429538193 : (((((False ∨ ((((True ∨ ((False → (p3 → p1)) ∧ p2)) ∧ (p4 → ((False ∧ p3) ∧ (False ∨ (p4 ∧ p1))))) → p5) ∨ True)) ∨ p2) ∨ p3) ∨ p4) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328556858162595004078339127332 : (True → ((((False ∨ (p1 → p1)) ∧ p5) ∨ (p5 ∨ ((False ∧ False) ∨ ((p1 ∨ True) ∧ False)))) → (((False ∨ (p4 → (p3 → p4))) → p1) → p1))) := by
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
    let h5 := h4.left
    let h6 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- False on the left can always be used.
      apply False.elim h7
    case inr h8 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h9 : (False ∨ (p4 → (p3 → p4))) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h10
        -- Implications on the right can always be decomposed.
        intro h11
        -- One of the premise coincides with the conclusion.
        exact h10
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h12 := h3 h9
      -- One of the premise coincides with the conclusion.
      exact h12
  case inr h13 =>
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h14 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h15 : (False ∨ (p4 → (p3 → p4))) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h16
        -- Implications on the right can always be decomposed.
        intro h17
        -- One of the premise coincides with the conclusion.
        exact h16
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h18 := h3 h15
      -- One of the premise coincides with the conclusion.
      exact h18
    case inr h19 =>
      -- Disjunctions on the left can always be decomposed.
      cases h19
      case inl h20 =>
        -- Conjunctions on the left can always be decomposed.
        let h21 := h20.left
        let h22 := h20.right
        -- False on the left can always be used.
        apply False.elim h21
      case inr h23 =>
        -- Conjunctions on the left can always be decomposed.
        let h24 := h23.left
        let h25 := h23.right
        -- Disjunctions on the left can always be decomposed.
        cases h24
        case inl h26 =>
          -- False on the left can always be used.
          apply False.elim h25
        case inr h27 =>
          -- False on the left can always be used.
          apply False.elim h25



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233663185376729477917652393681 : ((p2 ∨ (p4 ∨ p4)) → (p5 → (((p4 ∧ (((p5 ∨ ((False → p1) ∧ True)) ∧ p1) → p2)) → (p5 → ((p3 ∨ True) → (p5 ∧ p3)))) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185978721008247638042354315162 : (((p5 ∧ (((((p2 ∨ p3) ∨ p2) → True) → False) → p2)) ∧ p1) → (((p3 → p1) → ((p5 ∧ (True → (p4 ∨ (False ∨ p5)))) → p4)) ∨ True)) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45738031512138095041960343736 : (((False → (((p1 → ((((True ∨ True) ∧ p4) ∨ (p5 → p1)) ∨ ((p5 → (True → p3)) → (True ∨ (p3 → p1))))) → False) ∧ False)) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37498533279599363438823237035 : (((((False ∧ p2) ∧ ((p4 ∧ ((((False → (True → (p2 → False))) ∧ p4) ∨ True) → (p1 ∧ ((p4 ∧ p5) ∧ True)))) ∧ p3)) ∨ p3) ∧ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313971658341982567796171389377 : (p3 ∨ (((((False ∨ True) ∨ (p4 ∧ ((p2 ∧ p1) ∧ p2))) ∧ (p4 ∧ (False → False))) ∨ (((False ∨ p4) ∨ (p4 → p2)) ∧ p3)) ∨ (p2 → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_605313693908107025410413878187 : ((((p3 → ((p4 → (((True → (p2 ∨ (False ∧ p1))) ∧ ((p4 ∧ (p1 → (True → (p2 ∨ p5)))) ∧ (p5 ∨ p3))) ∨ p4)) ∧ False)) ∧ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173309877754667382785518489326 : ((p1 → (p2 ∨ ((((p2 → ((p5 ∨ (p5 ∧ p4)) ∧ p5)) ∨ p1) ∨ p5) ∨ p4))) ∨ (True → (((False ∨ False) ∨ p2) → (p2 → (p4 ∨ p4))))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_668491936775800871684218179884 : ((((((p4 → (p5 ∧ ((((p4 ∧ (p2 ∧ (p5 ∨ p5))) → p1) → p1) ∨ p5))) ∧ ((p5 ∧ False) ∧ False)) ∧ False) ∨ ((p3 ∨ p4) ∨ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340811794115085972651483568940 : (p2 → (((((p2 → (p1 ∧ p3)) ∧ (((p1 ∧ (True → p5)) → False) ∨ p1)) → ((p3 ∨ (p3 → p1)) ∨ (p4 ∧ p5))) ∧ (p2 ∨ p1)) ∨ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
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
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h6 : p2 := by
      -- One of the premise coincides with the conclusion.
      exact h1
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h7 := h3 h6
    -- We need to get the right conjuct of h7 based on <expert-advice>.
    let h8 := h7.right
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h10
    -- One of the premise coincides with the conclusion.
    exact h9
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45939895381566256595256616465 : (((p5 → (((p4 ∨ p2) ∧ (p3 → (False ∧ ((((False ∨ p5) ∨ ((p1 → (p2 → p3)) ∧ p5)) ∧ (p5 → p4)) → True)))) ∨ p5)) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_810024595568040674402125332221 : (((p5 → ((p1 → ((True ∨ (p2 ∧ ((p5 → (p2 ∧ False)) ∨ ((p5 → p1) ∨ (True ∧ p3))))) ∨ (p2 ∨ True))) → ((p1 → p2) ∧ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301428772798069783961756144753 : (False ∨ (((p2 → p2) ∨ (False → True)) → ((p4 ∨ (((p5 → p3) ∨ ((True → True) → (True ∨ p3))) ∨ (True ∧ p4))) ∧ (p2 ∨ (False → p3))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- False on the left can always be used.
    apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315440064752174312754270150811 : (p3 ∨ ((p5 ∨ (p1 ∧ p1)) ∨ (((((False ∨ p2) ∧ True) ∨ ((p3 ∧ ((p2 ∧ (True → p2)) ∨ (True ∧ False))) ∨ True)) ∨ (p5 → p5)) ∨ False))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115436082253797674010776106529 : ((((False ∨ (p3 → ((p2 ∨ p5) ∧ p2))) → False) ∨ (p4 ∨ ((p3 ∨ ((p4 → ((p5 → p4) → True)) → True)) ∨ (False ∨ p5)))) ∨ (p1 ∧ p3)) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177865463180272581158972160280 : ((((p1 ∧ ((p4 ∧ ((p5 ∨ p4) ∨ p4)) → (False ∨ p3))) ∨ p1) ∨ p2) ∨ (((p5 → (p5 ∨ ((p3 ∨ p5) ∧ (p3 → p2)))) ∨ True) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118157599103255060794646821191 : ((False ∨ (((False ∨ p3) ∧ (p3 ∧ p2)) → (((p4 ∨ p5) → (False ∧ (p5 ∨ p1))) ∨ (p4 → (False → ((p2 ∨ False) → p5)))))) ∨ (False → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38220132003456815368123662852 : (((((p2 ∧ p3) ∨ (((p4 ∨ p4) ∧ p1) ∨ ((p4 → p4) → (((p4 → p4) → (False ∧ p3)) → p5)))) → (p4 ∨ (False ∨ p1))) ∧ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_312132443467929297073448919317 : (p2 ∨ (True → (((True → p3) → ((p1 → True) ∧ (p4 ∨ p1))) ∨ (p2 → ((((True → True) ∧ p4) → (False ∨ p3)) ∨ ((p4 → p2) ∧ True)))))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244522524665357715016177191594 : ((False ∧ p3) ∨ (((p4 ∧ p3) ∧ False) ∨ (True ∨ ((p1 ∨ (p5 ∨ (((((p2 ∧ p5) ∧ False) ∨ p2) ∨ ((p2 ∨ p5) ∧ p1)) ∨ p3))) ∧ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218781060417804448296897037140 : ((p1 ∧ ((False ∨ p1) → p2)) → (((p2 ∧ p2) → (p4 ∨ ((p4 → (p4 → (((p2 → True) → p3) ∨ True))) ∧ (p2 → (p2 ∨ True))))) ∨ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h7
  -- Implications on the right can always be decomposed.
  intro h8
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h9
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116036360419494606165865572208 : (((p1 ∨ (True ∨ (True ∨ True))) → (p5 ∧ (((p5 → ((p2 → ((p1 ∨ True) ∧ p1)) → True)) ∧ (p5 ∨ p4)) ∧ (p2 ∧ False)))) ∨ (p4 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_769596187471580007062541599337 : (((p5 ∧ (p5 ∧ (False ∨ (False ∧ (False ∨ (((p2 ∨ (p1 → p5)) → (p1 → p3)) ∧ (p5 ∧ (p5 ∨ ((p3 ∨ (p1 ∧ True)) → p5))))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_767074401587667965656616028641 : (((p4 ∧ (p3 → (((p3 → True) → (((((p5 ∨ True) ∨ p4) → p4) ∨ (True → p2)) ∧ ((p2 → p3) → p4))) ∧ ((p1 ∧ False) ∧ False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256898119395237019708514220474 : ((p1 ∨ p4) → ((p2 ∨ (((p2 → (p2 → p5)) → (p3 ∨ True)) → (((p2 → True) ∧ False) ∨ (p2 ∧ (p4 ∧ p3))))) → (p5 ∨ (p2 ∨ p3)))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h3
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h7 =>
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h8 : ((p2 → (p2 → p5)) → (p3 ∨ True)) := by
        -- Implications on the right can always be decomposed.
        intro h9
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h10 := h6 h8
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- Conjunctions on the left can always be decomposed.
        let h12 := h11.left
        let h13 := h11.right
        -- False on the left can always be used.
        apply False.elim h13
      case inr h14 =>
        -- Conjunctions on the left can always be decomposed.
        let h15 := h14.left
        let h16 := h14.right
        -- Conjunctions on the left can always be decomposed.
        let h17 := h16.left
        let h18 := h16.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h15
    case inr h19 =>
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h20 : ((p2 → (p2 → p5)) → (p3 ∨ True)) := by
        -- Implications on the right can always be decomposed.
        intro h21
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h22 := h6 h20
      -- Disjunctions on the left can always be decomposed.
      cases h22
      case inl h23 =>
        -- Conjunctions on the left can always be decomposed.
        let h24 := h23.left
        let h25 := h23.right
        -- False on the left can always be used.
        apply False.elim h25
      case inr h26 =>
        -- Conjunctions on the left can always be decomposed.
        let h27 := h26.left
        let h28 := h26.right
        -- Conjunctions on the left can always be decomposed.
        let h29 := h28.left
        let h30 := h28.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h27



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319180170093240255508824829912 : (p4 ∨ (((p4 → p1) → ((((p5 → (p5 ∧ (p5 ∧ (p2 ∧ False)))) → (False → p5)) ∨ True) → p5)) ∨ (((p2 ∧ False) ∨ True) ∨ (p1 → p1)))) := by
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
theorem thm_5_vars_336110784850124251855458682576 : (p1 → (((((p1 ∧ (p3 → False)) ∨ (((((((p5 ∨ (p1 ∨ p2)) ∨ p4) ∧ p5) ∨ p4) → p4) → p4) ∨ (p4 ∨ p1))) ∨ False) ∨ p2) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_355930523201450760008781283339 : (p5 → ((((((p1 → p3) → p5) ∨ p2) ∧ False) → (p1 ∧ ((((p1 ∧ (p5 ∨ False)) ∨ (p2 → p2)) ∨ True) → p2))) → ((True → p3) ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113323412084511286299243540673 : ((((False ∧ p1) ∧ (True → (((p3 → ((p2 → ((True ∨ p4) ∨ p1)) → (p1 ∨ (p4 ∧ True)))) → p4) ∨ p2))) ∧ (p1 ∨ False)) ∨ (False → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_689892318375101982770671024326 : (((((p2 ∧ p4) → ((p4 ∨ p3) ∧ ((p4 ∧ p2) → (p4 → ((p3 ∨ False) ∧ p3))))) ∨ ((p3 ∨ p3) → ((p2 ∨ p3) ∨ (False ∨ True)))) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304763870897101448215651205290 : (p1 ∨ ((p3 ∧ (((p3 → (p5 ∧ p3)) ∧ (((p2 → ((((p5 ∨ p1) ∧ False) → p2) ∨ p1)) ∨ (p1 → p4)) → p3)) ∧ p1)) ∨ (False → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_800158952872072877195643000827 : (((p2 → ((p5 ∨ ((True ∧ ((p1 → (((True ∧ (p4 ∧ (p3 ∧ True))) ∧ False) → p3)) → p5)) ∨ (p4 ∨ (p2 ∧ (False ∨ p2))))) ∧ True)) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_705800616664404367708849844023 : ((((((False ∧ p1) → (p2 ∨ p5)) → (p2 ∨ p2)) ∧ (True → (p3 ∧ (True ∨ ((p3 ∨ (((False ∨ (False → p1)) ∨ p2) ∨ p4)) → p4))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_76821016931542921306912589694 : ((((p4 ∧ (p5 → ((False ∨ (p2 ∧ ((p5 ∨ p4) → p4))) → p5))) ∨ (p2 ∨ ((((True ∧ (p1 → p5)) ∧ False) ∨ True) ∨ p5))) → p5) → p5) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p4 ∧ (p5 → ((False ∨ (p2 ∧ ((p5 ∨ p4) → p4))) → p5))) ∨ (p2 ∨ ((((True ∧ (p1 → p5)) ∧ False) ∨ True) ∨ p5))) := by
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
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64535427925521864784525606101 : ((p1 ∨ ((((p3 ∨ False) ∧ True) ∨ (True ∧ (p2 ∨ p5))) → (p5 ∨ (((p5 ∨ (True ∨ (p3 ∨ p5))) → (p5 ∧ (False → p5))) ∨ True)))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h6 =>
      -- False on the left can always be used.
      apply False.elim h6
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h11 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_252507177871760798469042637343 : ((p5 → p2) ∨ ((((((((((False ∨ (p1 ∨ p2)) ∧ (False → p4)) ∨ False) ∧ (p2 ∨ (p4 ∧ p5))) → p2) ∧ p1) → p5) → p2) ∧ p5) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317386533562897369632853129828 : (p4 ∨ ((((((p1 ∨ False) → p1) ∧ p2) ∧ p4) → (((p2 → (p1 ∧ p1)) ∧ (p2 ∨ (p4 ∨ ((False → p3) ∨ (p2 ∨ p5))))) → p1)) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h1.left
    let h7 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h6.left
    let h9 := h6.right
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h10 : p2 := by
      -- One of the premise coincides with the conclusion.
      exact h9
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h11 := h3 h10
    -- We need to get the left conjuct of h11 based on <expert-advice>.
    let h12 := h11.left
    -- One of the premise coincides with the conclusion.
    exact h12
  case inr h13 =>
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h14 =>
      -- Conjunctions on the left can always be decomposed.
      let h15 := h1.left
      let h16 := h1.right
      -- Conjunctions on the left can always be decomposed.
      let h17 := h15.left
      let h18 := h15.right
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h19 : p2 := by
        -- One of the premise coincides with the conclusion.
        exact h18
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h20 := h3 h19
      -- We need to get the left conjuct of h20 based on <expert-advice>.
      let h21 := h20.left
      -- One of the premise coincides with the conclusion.
      exact h21
    case inr h22 =>
      -- Disjunctions on the left can always be decomposed.
      cases h22
      case inl h23 =>
        -- Conjunctions on the left can always be decomposed.
        let h24 := h1.left
        let h25 := h1.right
        -- Conjunctions on the left can always be decomposed.
        let h26 := h24.left
        let h27 := h24.right
        -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
        have h28 : p2 := by
          -- One of the premise coincides with the conclusion.
          exact h27
        -- We have shown the premise of h3, we can now drive its conclusion.
        let h29 := h3 h28
        -- We need to get the left conjuct of h29 based on <expert-advice>.
        let h30 := h29.left
        -- One of the premise coincides with the conclusion.
        exact h30
      case inr h31 =>
        -- Disjunctions on the left can always be decomposed.
        cases h31
        case inl h32 =>
          -- Conjunctions on the left can always be decomposed.
          let h33 := h1.left
          let h34 := h1.right
          -- Conjunctions on the left can always be decomposed.
          let h35 := h33.left
          let h36 := h33.right
          -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
          have h37 : p2 := by
            -- One of the premise coincides with the conclusion.
            exact h36
          -- We have shown the premise of h3, we can now drive its conclusion.
          let h38 := h3 h37
          -- We need to get the left conjuct of h38 based on <expert-advice>.
          let h39 := h38.left
          -- One of the premise coincides with the conclusion.
          exact h39
        case inr h40 =>
          -- Conjunctions on the left can always be decomposed.
          let h41 := h1.left
          let h42 := h1.right
          -- Conjunctions on the left can always be decomposed.
          let h43 := h41.left
          let h44 := h41.right
          -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
          have h45 : p2 := by
            -- One of the premise coincides with the conclusion.
            exact h44
          -- We have shown the premise of h3, we can now drive its conclusion.
          let h46 := h3 h45
          -- We need to get the left conjuct of h46 based on <expert-advice>.
          let h47 := h46.left
          -- One of the premise coincides with the conclusion.
          exact h47
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_803275640049248563853224482452 : (((p3 → (((((p2 → p2) ∨ p2) ∧ ((((p3 ∨ False) ∨ (p3 → (p2 ∧ p3))) → False) ∧ True)) ∧ (((p1 → False) ∧ p5) ∧ p3)) ∨ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46879347954900898954443579332 : (((((((False ∨ p5) → (p1 ∨ (p4 ∧ ((p3 → (p1 ∧ (True → (p3 ∧ True)))) ∧ False)))) ∨ (p1 ∨ p3)) ∧ p1) ∨ True) ∨ (p1 ∨ p2)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_732412919836302055661871086624 : ((((False ∧ p3) ∧ (((p2 ∧ p3) ∧ ((p2 → (p3 ∨ (((p5 ∨ p2) ∧ (p2 ∨ p4)) ∧ p4))) ∧ (p2 → False))) ∨ (p3 → (p2 ∨ p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118141049141292514601493528128 : ((False ∨ (((p1 ∨ (((p2 ∧ p2) ∨ p5) ∧ (p5 ∨ (True ∧ p2)))) ∨ (False ∨ True)) ∨ (p3 → (((p3 ∨ True) ∨ p2) ∨ False)))) ∨ (p2 ∧ p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_17910839499669914560011887106 : (((((((((p2 ∨ (p3 ∨ True)) ∨ p3) ∧ (p2 ∨ False)) ∧ (p5 ∧ p3)) ∨ p5) ∨ p1) ∨ (False ∨ p2)) ∨ (p5 → ((True ∨ p3) ∧ p5))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_247432390474628871461812349554 : ((False ∨ p2) ∨ ((((p2 ∨ p3) → ((True → p4) → True)) → False) ∨ ((((p5 ∨ (p3 ∨ True)) ∨ True) ∧ True) ∨ (False ∨ ((p2 ∨ False) ∧ p3))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40025639209089503727369546257 : (((((((p2 ∧ False) ∧ (True ∧ (p5 ∧ (p4 ∨ (p4 ∧ (p1 → (((p5 → (p2 ∧ p5)) ∧ p1) ∧ p4))))))) ∨ p5) ∧ p4) ∧ p5) ∨ True) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172795422292900455077864452284 : (((p2 → p5) → (p4 ∨ (((((p3 ∨ p2) ∨ p3) → (p1 → p3)) ∨ True) → False))) ∨ ((((p2 ∧ p1) ∨ p5) ∨ True) ∨ (False ∧ (True ∧ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117185668730790675154660305834 : ((True ∧ ((p4 → (True ∧ ((True → p5) ∨ (((p2 ∨ ((p5 ∨ p3) ∧ (False ∧ p5))) → p4) ∧ (False ∧ p4))))) → (p1 ∧ p3))) ∨ (p5 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157026230236401197461841802036 : ((((p4 ∧ p5) ∨ ((p5 ∧ (False → (p1 → (p2 → ((False ∨ (p5 ∨ False)) → p5))))) ∧ p3)) ∨ p4) ∨ (((p5 ∧ (True → p2)) ∧ p5) → p5)) := by
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
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174800233759560403173925189130 : (((True → False) ∧ ((True ∧ ((p1 → False) ∧ (((p5 → True) → False) → p5))) ∨ p4)) → ((p4 ∨ (p5 ∨ p5)) → (((p3 ∨ p5) → p3) → False))) := by
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
    cases h6
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h12 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h13 := h5 h12
      -- False on the left can always be used.
      apply False.elim h13
    case inr h14 =>
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h15 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h16 := h5 h15
      -- False on the left can always be used.
      apply False.elim h16
  case inr h17 =>
    -- Disjunctions on the left can always be decomposed.
    cases h17
    case inl h18 =>
      -- Conjunctions on the left can always be decomposed.
      let h19 := h1.left
      let h20 := h1.right
      -- Disjunctions on the left can always be decomposed.
      cases h20
      case inl h21 =>
        -- Conjunctions on the left can always be decomposed.
        let h22 := h21.left
        let h23 := h21.right
        -- Conjunctions on the left can always be decomposed.
        let h24 := h23.left
        let h25 := h23.right
        -- We want to use the implication h19 based on <expert-advice>. So we show its premise.
        have h26 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h19, we can now drive its conclusion.
        let h27 := h19 h26
        -- False on the left can always be used.
        apply False.elim h27
      case inr h28 =>
        -- We want to use the implication h19 based on <expert-advice>. So we show its premise.
        have h29 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h19, we can now drive its conclusion.
        let h30 := h19 h29
        -- False on the left can always be used.
        apply False.elim h30
    case inr h31 =>
      -- Conjunctions on the left can always be decomposed.
      let h32 := h1.left
      let h33 := h1.right
      -- Disjunctions on the left can always be decomposed.
      cases h33
      case inl h34 =>
        -- Conjunctions on the left can always be decomposed.
        let h35 := h34.left
        let h36 := h34.right
        -- Conjunctions on the left can always be decomposed.
        let h37 := h36.left
        let h38 := h36.right
        -- We want to use the implication h32 based on <expert-advice>. So we show its premise.
        have h39 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h32, we can now drive its conclusion.
        let h40 := h32 h39
        -- False on the left can always be used.
        apply False.elim h40
      case inr h41 =>
        -- We want to use the implication h32 based on <expert-advice>. So we show its premise.
        have h42 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h32, we can now drive its conclusion.
        let h43 := h32 h42
        -- False on the left can always be used.
        apply False.elim h43



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158076224934848701809692388100 : ((((False ∧ (False ∧ p5)) ∨ (p2 → p5)) → ((p3 ∨ ((True ∧ p1) ∨ p2)) ∨ ((p5 → p4) ∧ p4))) ∨ ((p1 → True) ∨ ((p3 ∨ False) ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_84023817821314530369009083476 : ((((((False ∨ (p5 → p5)) → (True → p1)) ∧ (p3 → (p4 → (p5 ∨ p1)))) → False) ∧ (((True ∧ ((True ∧ p5) ∨ p2)) → False) ∧ p1)) → p2) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h6 : (((False ∨ (p5 → p5)) → (True → p1)) ∧ (p3 → (p4 → (p5 ∨ p1)))) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h7
    -- Implications on the right can always be decomposed.
    intro h8
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h9 =>
      -- False on the left can always be used.
      apply False.elim h9
    case inr h10 =>
      -- One of the premise coincides with the conclusion.
      exact h5
    -- Implications on the right can always be decomposed.
    intro h11
    -- Implications on the right can always be decomposed.
    intro h12
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h13 := h2 h6
  -- False on the left can always be used.
  apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319916295097799175283009547220 : (p4 ∨ (((True ∨ True) ∧ (p1 ∨ p5)) → ((((p4 ∨ p2) ∧ p5) ∨ (p5 ∨ True)) ∨ ((False ∧ (((False → True) ∨ False) ∧ (False ∧ False))) ∧ True)))) := by
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h6 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h6
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h8 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h9 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164706906618476840148737982304 : ((((p2 ∧ (p4 → ((False ∧ p1) ∧ (((p3 ∨ p1) ∨ False) ∨ (False ∨ p2))))) ∨ p2) ∨ p5) ∨ (((False → p1) ∨ ((p4 ∧ p5) ∧ p5)) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38006488038049383359445272915 : ((((False ∧ (((False → (p4 ∨ (False ∨ (((p2 ∨ p1) → True) → False)))) ∧ p2) ∧ (p1 ∨ (p3 ∧ (p1 → p4))))) ∨ (False ∨ p3)) ∧ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54764198499487917937003057040 : ((((False ∨ True) → (False → ((p2 ∨ p4) ∨ p4))) → (((p5 ∧ p3) → False) ∧ (p5 ∨ ((((p5 → (p5 → p2)) ∧ True) ∨ p5) ∧ p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178222310262049534775318187786 : (((False → ((False ∧ (p1 → (p3 ∧ p5))) ∨ ((p2 ∨ p5) ∧ p4))) → p2) ∨ ((p1 ∨ ((p3 ∧ ((p4 → True) ∨ False)) ∨ (p5 → p5))) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_151225555368973426704822311110 : ((((p1 ∧ (p5 ∧ p1)) ∨ ((p5 ∧ p5) → (((p4 ∧ ((p5 → False) → p4)) ∧ (p5 ∧ False)) → p3))) → p5) → (((p1 ∨ p2) ∨ p5) → p5)) := by
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
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h5 : ((p1 ∧ (p5 ∧ p1)) ∨ ((p5 ∧ p5) → (((p4 ∧ ((p5 → False) → p4)) ∧ (p5 ∧ False)) → p3))) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h6
        -- Implications on the right can always be decomposed.
        intro h7
        -- Conjunctions on the left can always be decomposed.
        let h8 := h7.left
        let h9 := h7.right
        -- Conjunctions on the left can always be decomposed.
        let h10 := h8.left
        let h11 := h8.right
        -- Conjunctions on the left can always be decomposed.
        let h12 := h9.left
        let h13 := h9.right
        -- False on the left can always be used.
        apply False.elim h13
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h14 := h1 h5
      -- One of the premise coincides with the conclusion.
      exact h14
    case inr h15 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h16 : ((p1 ∧ (p5 ∧ p1)) ∨ ((p5 ∧ p5) → (((p4 ∧ ((p5 → False) → p4)) ∧ (p5 ∧ False)) → p3))) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h17
        -- Implications on the right can always be decomposed.
        intro h18
        -- Conjunctions on the left can always be decomposed.
        let h19 := h18.left
        let h20 := h18.right
        -- Conjunctions on the left can always be decomposed.
        let h21 := h19.left
        let h22 := h19.right
        -- Conjunctions on the left can always be decomposed.
        let h23 := h20.left
        let h24 := h20.right
        -- False on the left can always be used.
        apply False.elim h24
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h25 := h1 h16
      -- One of the premise coincides with the conclusion.
      exact h25
  case inr h26 =>
    -- One of the premise coincides with the conclusion.
    exact h26



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346476391718831795864335446539 : (p3 → (((p3 → p2) ∧ (((p1 ∧ p1) → (p1 ∧ ((p3 → (p3 ∨ p5)) ∨ (p3 ∧ (p2 ∧ (False → p2)))))) → (p4 → p2))) → (p2 ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h5 : p3 := by
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h5
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308353482821091776775366029776 : (p2 ∨ ((((True ∧ False) ∨ ((p3 → (True → (p2 ∨ (((False ∨ ((p3 → p5) ∧ p3)) → p1) → p4)))) ∨ (p3 ∨ (p5 → p3)))) ∧ True) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59684341666408466577252485342 : (((True ∧ p4) → ((((True → (p5 ∨ False)) ∧ (p4 ∨ (p4 → p1))) ∧ p3) → ((p3 ∨ (p5 → (True → (False → p4)))) → (p3 → p5)))) ∨ False) := by
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
  cases h3
  case inl h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h2.left
    let h7 := h2.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h6.left
    let h9 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h1.left
      let h12 := h1.right
      -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
      have h13 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h8, we can now drive its conclusion.
      let h14 := h8 h13
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h15 =>
        -- One of the premise coincides with the conclusion.
        exact h15
      case inr h16 =>
        -- False on the left can always be used.
        apply False.elim h16
    case inr h17 =>
      -- Conjunctions on the left can always be decomposed.
      let h18 := h1.left
      let h19 := h1.right
      -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
      have h20 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h8, we can now drive its conclusion.
      let h21 := h8 h20
      -- Disjunctions on the left can always be decomposed.
      cases h21
      case inl h22 =>
        -- One of the premise coincides with the conclusion.
        exact h22
      case inr h23 =>
        -- False on the left can always be used.
        apply False.elim h23
  case inr h24 =>
    -- Conjunctions on the left can always be decomposed.
    let h25 := h2.left
    let h26 := h2.right
    -- Conjunctions on the left can always be decomposed.
    let h27 := h25.left
    let h28 := h25.right
    -- Disjunctions on the left can always be decomposed.
    cases h28
    case inl h29 =>
      -- Conjunctions on the left can always be decomposed.
      let h30 := h1.left
      let h31 := h1.right
      -- We want to use the implication h27 based on <expert-advice>. So we show its premise.
      have h32 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h27, we can now drive its conclusion.
      let h33 := h27 h32
      -- Disjunctions on the left can always be decomposed.
      cases h33
      case inl h34 =>
        -- One of the premise coincides with the conclusion.
        exact h34
      case inr h35 =>
        -- False on the left can always be used.
        apply False.elim h35
    case inr h36 =>
      -- Conjunctions on the left can always be decomposed.
      let h37 := h1.left
      let h38 := h1.right
      -- We want to use the implication h27 based on <expert-advice>. So we show its premise.
      have h39 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h27, we can now drive its conclusion.
      let h40 := h27 h39
      -- Disjunctions on the left can always be decomposed.
      cases h40
      case inl h41 =>
        -- One of the premise coincides with the conclusion.
        exact h41
      case inr h42 =>
        -- False on the left can always be used.
        apply False.elim h42



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197933009814672150834993960756 : (((p5 → (p3 ∧ p1)) → (p5 ∨ (p4 ∧ p5))) ∨ (True ∨ (p3 ∨ (((p1 ∨ (p4 ∧ ((p2 ∧ p2) ∧ p4))) ∧ ((False ∧ True) → True)) ∧ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246568843756315820301407429549 : ((p5 ∧ p2) ∨ ((((((p5 → p3) ∨ p1) ∧ (((True ∨ p1) → (p2 → p2)) ∨ p4)) → ((p3 ∧ p1) ∧ p4)) ∧ (p3 ∨ False)) ∨ (p1 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65058021572734136589110804742 : ((p2 ∨ (p2 ∧ ((p4 → (False ∧ (p3 ∨ (p5 → p3)))) ∧ (p3 → ((p3 ∧ (((p2 ∧ (p5 → p4)) ∧ True) ∧ (False ∨ p2))) ∨ True))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_614205896176349299239172256669 : ((((((((p5 → p2) ∧ (p5 → p1)) ∧ ((((True ∧ p2) → (p5 ∧ False)) ∨ p5) → (p1 ∧ p5))) → p4) → ((p4 ∧ p1) → p4)) ∨ p2) ∨ p3) ∧ True) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68196815518854263473189041476 : ((p3 → (((p5 ∧ True) ∧ ((p4 → ((p3 → False) ∧ (((p2 ∨ p2) → (p5 ∧ ((True → p2) ∧ p5))) → p5))) ∧ (p5 ∨ p4))) ∨ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_663151070001608521524053620212 : (((((p5 ∨ True) ∧ (((p3 ∨ ((p2 ∧ True) ∧ ((p5 ∨ p3) ∨ ((True ∧ p2) → p3)))) ∨ (p3 ∧ (p4 ∨ False))) → p2)) → (False ∧ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110841153766219036387551323713 : ((((p4 ∨ ((p3 → ((((p2 ∧ (p3 → p4)) ∨ ((p5 ∧ p1) → p4)) ∧ p1) → (p4 ∨ p3))) ∨ (p1 ∧ False))) ∨ p1) ∧ p1) ∨ (p1 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134692446730690113587143182415 : ((((True → (p3 → ((p1 ∨ p5) ∨ False))) → ((p1 → p1) ∨ ((p4 → (p4 ∧ p1)) → ((False ∨ p5) ∨ p2)))) → p2) ∨ (True ∧ (True ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55497159083943771610979597342 : ((((p4 ∨ (p4 → p2)) → (p4 ∨ p1)) → (((((True → (((False ∨ p3) ∨ p2) ∨ p2)) ∨ p4) ∨ (p5 ∧ True)) ∨ (p4 ∨ False)) → p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_629449472589014879119764335806 : (((((((p2 ∧ p5) → ((True ∨ p5) ∧ ((p1 → ((False ∨ ((p5 → p5) ∧ p3)) ∧ p1)) → (p5 ∧ p5)))) ∧ (p3 → p2)) ∨ p3) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_615084824594823321712620531969 : (((((p3 → (False ∨ ((p4 → (True ∨ True)) ∨ (((p2 ∨ p2) → (p1 ∧ (p4 → p1))) ∨ True)))) → (((p2 → p1) → p4) → p5)) ∨ True) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_314960685412355592180123559250 : (p3 ∨ (((True → p2) → ((((p5 ∧ p2) ∧ p5) ∨ p1) ∧ p1)) → ((((p5 ∨ False) ∨ p1) → False) → (p2 → (((p3 ∧ True) → p2) → p5))))) := by
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
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h5 : (True → p2) := by
    -- Implications on the right can always be decomposed.
    intro h6
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h7 := h1 h5
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h9 : ((p5 ∨ False) ∨ p1) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h8
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h10 := h2 h9
  -- False on the left can always be used.
  apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56571261031563988247285705903 : (((True → (False ∧ (p5 ∨ p3))) → ((((p5 → p2) ∧ (p5 → p1)) ∧ (p5 ∧ (p1 → (((p1 ∨ p3) → False) ∨ p4)))) ∨ (True ∧ p5))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the left conjuct of h3 based on <expert-advice>.
  let h4 := h3.left
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171604432689373381386251534298 : (((((((False → p3) ∨ True) → p2) ∨ p2) → (p2 → ((p5 ∧ p3) ∧ p1))) ∨ True) ∨ (((p3 → (((p5 → True) ∨ p1) ∧ False)) ∧ p3) ∧ p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_627106017572687978219343141889 : ((((((p4 ∨ (p2 → ((((p5 ∨ (p5 ∨ p4)) → (p2 → p1)) ∧ p2) → (p5 ∨ ((False ∨ p5) → (p5 → False)))))) ∧ p4) ∧ True) → False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_774812145894604507188942221723 : (((False ∨ (((p3 ∨ p4) ∨ (p3 ∨ (p1 ∧ True))) → ((True ∧ ((p5 ∨ True) → p1)) → ((((p1 → False) ∨ False) → False) ∧ (False → p1))))) ∨ p1) ∧ True) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h2.left
    let h6 := h2.right
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
        have h9 : (p5 ∨ True) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h6, we can now drive its conclusion.
        let h10 := h6 h9
        -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
        have h11 : p1 := by
          -- One of the premise coincides with the conclusion.
          exact h10
        -- We have shown the premise of h4, we can now drive its conclusion.
        let h12 := h4 h11
        -- False on the left can always be used.
        apply False.elim h12
      case inr h13 =>
        -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
        have h14 : (p5 ∨ True) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h6, we can now drive its conclusion.
        let h15 := h6 h14
        -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
        have h16 : p1 := by
          -- One of the premise coincides with the conclusion.
          exact h15
        -- We have shown the premise of h4, we can now drive its conclusion.
        let h17 := h4 h16
        -- False on the left can always be used.
        apply False.elim h17
    case inr h18 =>
      -- Disjunctions on the left can always be decomposed.
      cases h18
      case inl h19 =>
        -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
        have h20 : (p5 ∨ True) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h6, we can now drive its conclusion.
        let h21 := h6 h20
        -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
        have h22 : p1 := by
          -- One of the premise coincides with the conclusion.
          exact h21
        -- We have shown the premise of h4, we can now drive its conclusion.
        let h23 := h4 h22
        -- False on the left can always be used.
        apply False.elim h23
      case inr h24 =>
        -- Conjunctions on the left can always be decomposed.
        let h25 := h24.left
        let h26 := h24.right
        -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
        have h27 : p1 := by
          -- One of the premise coincides with the conclusion.
          exact h25
        -- We have shown the premise of h4, we can now drive its conclusion.
        let h28 := h4 h27
        -- False on the left can always be used.
        apply False.elim h28
  case inr h29 =>
    -- False on the left can always be used.
    apply False.elim h29
  -- Implications on the right can always be decomposed.
  intro h30
  -- False on the left can always be used.
  apply False.elim h30
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110782297136598852995236438354 : ((((((p1 → (((False ∧ False) → ((False → p3) ∨ False)) ∨ (False ∨ (((p2 ∧ p2) → p3) → p2)))) → False) ∨ p2) ∨ p5) ∧ True) ∨ (False → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



