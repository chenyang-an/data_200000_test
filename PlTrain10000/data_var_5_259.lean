variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336431073750108308491915942409 : (p1 → ((p2 ∨ ((p4 ∨ (p2 ∧ (p3 ∨ (p2 → (p3 ∧ (p3 ∨ (((p1 ∧ p5) ∧ False) ∨ False))))))) ∧ (True → ((True ∨ p1) → p1)))) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_641312970165989015338068718457 : (((((False → p3) ∨ (True ∨ (True → ((p1 → (((p4 ∨ p2) → False) → (p3 ∧ (False → (p1 ∨ (p4 ∧ (False → p3))))))) ∧ True)))) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166191011230288173211589875159 : ((p1 ∧ (((((p3 → (p2 ∧ p4)) ∧ p1) → (p5 ∧ False)) ∧ p3) ∧ (True ∧ (p5 ∧ p3)))) ∨ (p3 → ((True ∨ (p3 ∨ p2)) ∧ (p3 ∨ False)))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_85123774138684714994508697438 : (((((p3 ∨ (p2 ∨ (p3 → p1))) → (((p1 → True) ∨ p1) ∨ True)) → True) → (((p4 → ((p5 → (p3 ∧ True)) ∧ True)) ∧ p2) ∧ p1)) → p2) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p3 ∨ (p2 ∨ (p3 → p1))) → (((p1 → True) ∨ p1) ∨ True)) → True) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315058241749337333215813198802 : (p3 ∨ ((p1 ∧ (((p4 ∧ p2) ∨ (p3 ∨ p1)) ∨ False)) → ((((p3 → ((True → p2) ∧ p3)) ∨ ((p4 ∨ True) ∨ (p1 ∧ p2))) ∨ p1) ∨ True))) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53252400050145164171658272572 : ((((p5 → p1) ∧ ((False ∨ p1) ∧ (p2 → (p5 → (p3 ∨ p1))))) ∨ ((p3 → ((((p3 ∧ False) ∨ (p4 ∧ p1)) → p5) ∧ False)) ∨ True)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173054229978240940457976143123 : ((False ∨ ((p5 ∧ ((p3 ∧ (p4 ∨ p4)) ∧ ((p3 ∨ True) → p5))) ∧ (False → False))) ∨ (((False ∨ ((p5 ∨ p2) → True)) ∨ (p4 → p3)) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_69146542754969419147317576240 : ((p5 → ((((((p3 → ((p4 ∨ False) ∧ p3)) → p4) ∨ (True → (p1 ∨ (p2 → p3)))) ∨ (True → p4)) ∨ p2) → ((p3 → p3) → False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184155196685568650041944708094 : (((p2 ∨ (p2 ∧ ((p3 ∧ (p1 ∧ (False ∧ p1))) ∨ True))) ∨ p3) ∨ (((False → p2) ∨ (((p2 ∧ True) ∨ (p5 → p4)) → p4)) ∨ (p2 ∨ p4))) := by
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
theorem thm_5_vars_735286087823334034350344619498 : ((((p4 ∨ True) ∧ (((((p5 → (p4 ∧ (p3 ∨ ((False ∧ p2) ∨ p5)))) ∨ ((p1 → p5) ∧ p5)) → p5) → p5) ∨ ((p2 → p2) → p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_10014003314848793134428968071 : (((p4 ∧ (((p5 → (p2 ∧ ((((((False ∧ (p1 → p5)) ∨ (p3 ∨ (p4 → p4))) ∧ p3) ∧ p5) ∧ False) → p4))) ∧ p3) → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64932758677755027756668157466 : ((p2 ∨ (((((True ∧ p1) ∨ (p3 ∨ (p3 ∨ p4))) ∨ p2) ∨ (p5 ∨ (p4 ∨ False))) → (p1 ∨ ((p3 ∧ p3) ∧ ((p5 ∨ p1) → p2))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48254185627913266242032076770 : (((p1 ∧ (p3 → ((((p1 ∨ p3) ∧ (((((p1 → False) ∨ p3) ∧ p4) → (p3 → p3)) ∨ p1)) → (True → False)) → p2))) → (p2 → p2)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249434217361114702473582854520 : ((p5 ∨ False) ∨ (((((((p2 ∨ (True → p4)) → p4) ∨ True) ∧ p2) ∨ p3) ∨ p1) → (((p1 ∨ ((p1 → p2) ∨ True)) → (p3 ∧ False)) → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h7 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h8 : (p1 ∨ ((p1 → p2) ∨ True)) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h9 := h2 h8
        -- We need to get the right conjuct of h9 based on <expert-advice>.
        let h10 := h9.right
        -- False on the left can always be used.
        apply False.elim h10
      case inr h11 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h12 : (p1 ∨ ((p1 → p2) ∨ True)) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h13 := h2 h12
        -- We need to get the right conjuct of h13 based on <expert-advice>.
        let h14 := h13.right
        -- False on the left can always be used.
        apply False.elim h14
    case inr h15 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h16 : (p1 ∨ ((p1 → p2) ∨ True)) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h17 := h2 h16
      -- We need to get the right conjuct of h17 based on <expert-advice>.
      let h18 := h17.right
      -- False on the left can always be used.
      apply False.elim h18
  case inr h19 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h20 : (p1 ∨ ((p1 → p2) ∨ True)) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h19
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h21 := h2 h20
    -- We need to get the right conjuct of h21 based on <expert-advice>.
    let h22 := h21.right
    -- False on the left can always be used.
    apply False.elim h22



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_622618543866923189605972904350 : ((((p4 ∧ (((p1 ∧ (True → p5)) ∨ (p5 ∨ ((((p5 ∨ (p3 → p2)) → p3) ∧ p2) ∧ (p1 ∧ (p4 ∨ p3))))) ∧ (p5 → p1))) ∨ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68808823220519582368400824683 : ((p4 → (((p4 ∧ (False ∨ True)) ∨ False) → ((((p4 ∨ p4) ∨ ((((True ∧ p3) ∨ p4) → p5) → p5)) ∨ p2) → ((p4 → False) ∧ p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_330349933136129711837734795037 : (True → (p2 ∨ ((((p4 → ((((False ∧ (p3 ∨ (((p3 ∨ (p2 → p2)) → p2) ∧ p3))) ∨ p3) ∧ (p5 ∧ True)) ∧ p5)) ∨ True) ∨ False) ∧ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_114360075934420106078053036488 : (((((p5 → (((p3 ∨ p1) ∧ (p3 ∨ p1)) ∨ p5)) ∨ ((p4 ∨ True) ∧ (p2 → p3))) ∧ p1) ∨ ((p1 ∨ (p1 → p2)) ∨ p1)) ∨ (True → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_196999352929621544814189253913 : ((((p4 → (p2 → (p1 ∧ p4))) → False) ∨ p5) ∨ (((p1 → (p4 → (True ∧ False))) ∨ p3) → (((p2 ∧ False) → (True ∨ (p4 → p1))) ∨ False))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h7
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- False on the left can always be used.
    apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135095227988015824303768451045 : ((((p5 ∧ (((p1 ∨ p5) ∨ p3) ∧ (p1 → p5))) ∨ (p5 → (p2 ∨ (((p1 → True) → False) ∧ p2)))) ∨ (p4 → False)) ∨ ((p3 ∧ p5) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_107465416367667326246605715823 : (((p1 ∧ (p4 → p2)) → ((p5 ∨ (p3 ∧ ((((p2 ∨ p1) → (p3 ∧ p5)) ∧ ((p2 ∨ p2) ∨ False)) ∧ (p2 → p5)))) → p5)) ∧ (True ∨ False)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Conjunctions on the left can always be decomposed.
    let h11 := h9.left
    let h12 := h9.right
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h13 =>
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h14 =>
        -- Conjunctions on the left can always be decomposed.
        let h15 := h1.left
        let h16 := h1.right
        -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
        have h17 : (p2 ∨ p1) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h15
        -- We have shown the premise of h11, we can now drive its conclusion.
        let h18 := h11 h17
        -- We need to get the right conjuct of h18 based on <expert-advice>.
        let h19 := h18.right
        -- One of the premise coincides with the conclusion.
        exact h19
      case inr h20 =>
        -- Conjunctions on the left can always be decomposed.
        let h21 := h1.left
        let h22 := h1.right
        -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
        have h23 : (p2 ∨ p1) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h21
        -- We have shown the premise of h11, we can now drive its conclusion.
        let h24 := h11 h23
        -- We need to get the right conjuct of h24 based on <expert-advice>.
        let h25 := h24.right
        -- One of the premise coincides with the conclusion.
        exact h25
    case inr h26 =>
      -- False on the left can always be used.
      apply False.elim h26
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180306389003270834032760412665 : ((((p2 → (p4 ∨ ((p4 → True) ∧ (False → p3)))) → True) ∧ (p3 → True)) → (p2 → (True ∧ ((True → (p3 ∧ ((p3 ∧ False) ∨ p3))) → p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h6 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h7 := h3 h6
  -- We need to get the left conjuct of h7 based on <expert-advice>.
  let h8 := h7.left
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134569634741431727563695574400 : ((((((p4 ∨ ((p5 → True) ∧ p3)) ∨ ((p2 → (((p2 → p3) ∧ p4) ∨ p4)) ∨ p5)) → p2) ∧ (p4 ∨ p1)) → p2) ∨ ((False ∨ True) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_684557225606644294232239384 : (((((((True ∧ (p5 → p4)) ∧ p4) → (p5 ∨ (False ∧ True))) → p5) → p5) ∨ ((False ∨ True) ∨ (p4 → (p1 → (p5 → p5))))) ∨ p3) := by
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
theorem thm_5_vars_40938066590974646688980372418 : (((((False ∧ (p2 ∨ (True ∧ (p4 → ((p3 ∨ (p2 ∨ (p3 ∧ (p4 ∨ ((p4 ∧ True) ∧ p4))))) ∨ p4))))) ∨ p5) ∨ (False → p3)) ∨ p5) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_339653040685251356007167011322 : (p1 → (p2 ∨ (p2 → (((True ∨ ((True → p2) ∨ p4)) → (((p1 → (True → (p3 ∨ (False ∧ (p3 ∨ p5))))) → p5) ∨ (False ∧ p3))) ∨ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_140095182718943345836971576100 : (((True ∨ ((((((p1 ∧ ((p1 ∨ p4) ∧ (p3 ∨ False))) → p2) ∨ False) ∨ True) ∧ (True → p5)) ∨ False)) ∨ (p2 ∨ True)) → ((p4 ∨ p2) ∨ True)) := by
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
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h4 =>
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h5 =>
        -- Conjunctions on the left can always be decomposed.
        let h6 := h5.left
        let h7 := h5.right
        -- Disjunctions on the left can always be decomposed.
        cases h6
        case inl h8 =>
          -- Disjunctions on the left can always be decomposed.
          cases h8
          case inl h9 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h10 =>
            -- False on the left can always be used.
            apply False.elim h10
        case inr h11 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h12 =>
        -- False on the left can always be used.
        apply False.elim h12
  case inr h13 =>
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h14 =>
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
theorem thm_5_vars_41454546549269572873121285298 : (((((((p4 ∧ (p5 ∧ (p1 → p3))) ∨ True) → p3) → (p4 ∨ p2)) ∧ ((p4 ∨ (((p1 → p3) ∧ p3) ∧ (p3 → p3))) → p5)) ∨ True) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42315784736163960321817088629 : (((p2 ∧ ((p4 ∨ False) ∨ (((((p4 ∨ p3) ∨ True) → (p4 → p3)) ∨ (((False ∧ (p3 ∨ p3)) → p3) ∧ False)) → (p4 ∧ True)))) ∨ True) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_109763050022288838596433674921 : ((p5 ∨ (((False ∨ (p5 ∧ (p4 ∨ ((((p5 ∨ p3) ∨ False) ∧ (p3 → (True → (p2 ∧ (p5 ∧ True))))) → False)))) ∧ p1) ∨ True)) ∧ (True ∨ True)) := by
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
theorem thm_5_vars_336122699709619556902406946883 : (p1 → ((((False ∨ (((p3 ∧ (p5 → ((True → (p1 ∨ False)) → True))) → p4) ∧ p1)) ∨ ((p3 → False) ∨ (p2 ∧ (p5 ∧ p5)))) ∨ True) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342117929541195295729624966625 : (p2 → (((False ∨ (p3 ∨ (p3 ∨ p2))) ∨ ((((((p3 ∧ p2) ∨ (False ∧ p5)) ∨ False) ∨ False) ∧ p5) ∨ p1)) ∧ ((p3 ∨ p3) ∨ (p4 → True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160577948659378129770082023421 : (((True ∨ (((False → p4) → (p3 ∨ ((p3 → True) ∨ True))) → True)) → ((True ∧ (p5 → True)) ∧ False)) → ((p1 ∨ (p2 → (p3 → False))) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (True ∨ (((False → p4) → (p3 ∨ ((p3 → True) ∨ True))) → True)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45166727093538489087721774667 : (((True ∧ ((p5 → ((p3 ∧ (p1 → p2)) ∨ ((p3 → p5) ∨ p4))) → ((p4 ∧ ((p1 ∧ True) ∧ p3)) → ((True → p3) → p2)))) → p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191303777094435542971704851959 : (((p2 → p5) ∧ ((p1 ∨ True) ∨ ((False → p2) ∨ p3))) ∨ (((((p1 ∧ p2) ∧ p2) ∧ (p1 → p3)) ∨ (((p1 ∨ p2) ∨ p5) ∨ True)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41423133266357136813805380845 : ((((p2 → (((((True ∧ p2) ∧ p1) ∨ p5) ∧ p1) ∨ (p2 ∧ (p4 → False)))) ∨ (((p4 ∨ False) ∨ (p3 ∨ (False → p5))) ∨ p4)) ∨ True) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346347826515604230195256445366 : (p3 → (((((p2 ∧ p4) ∧ False) ∨ p1) ∨ (True ∧ ((((False ∧ p5) ∨ True) → p4) ∨ ((p2 ∧ p1) → (p5 ∨ (p5 ∨ True)))))) ∨ (True → p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_745857637498146699381458935913 : ((((False ∨ p1) → (p2 → ((p3 ∧ (p5 → (True → ((((p2 ∧ (False → p1)) ∧ ((p4 ∨ p5) → False)) ∨ False) ∨ p5)))) ∨ (p2 ∧ False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119407182397814749649358454531 : ((p4 → ((False ∨ (p3 ∨ (((p3 ∨ ((p2 → False) ∧ ((p3 ∧ ((p3 ∧ p3) ∨ False)) ∧ (p1 ∨ p3)))) → p4) → p5))) ∨ p4)) ∨ (p3 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37451650078871795700922234674 : ((((((((p2 ∧ p5) ∨ p3) ∧ ((p3 → (False → p1)) → p3)) ∧ p3) ∨ (True ∨ (p4 ∧ ((p1 ∧ False) → (p5 ∧ False))))) ∨ p2) ∧ True) ∨ False) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_422128034716802226833899646866 : ((((((p1 ∨ (p3 ∨ p3)) → (False ∨ (((p5 ∨ p1) → p1) ∧ (((p3 ∧ True) → (p5 ∨ (p4 → p3))) → True)))) ∨ True) ∧ (p4 ∨ True)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46935592675171477928377532290 : ((((p2 ∧ ((((((((p3 → p2) ∨ p1) ∧ False) ∨ (True ∨ (p1 → (p2 ∨ p2)))) ∧ p5) ∨ p2) ∧ True) → p3)) ∨ p1) ∨ (True ∨ p2)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48921759052585552814894737104 : (((((((p5 ∧ (p2 ∨ ((True → True) ∨ p3))) → (p5 ∨ (p3 ∨ False))) → ((False ∧ p1) ∧ p4)) ∨ True) ∧ p2) ∨ (p4 ∨ (p5 → p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42698480114502431266401819500 : (((p5 ∨ ((((p4 → p1) ∨ ((p1 ∨ ((p3 → False) ∧ True)) → ((False ∨ p1) ∨ False))) ∧ p1) ∧ (((True → p3) ∧ p2) ∧ False))) ∨ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_679172125893779061981811102554 : ((((p4 ∨ (((p1 → p5) → p5) ∨ (True ∧ ((p3 ∨ ((p4 → ((p4 ∧ p1) ∨ p3)) ∧ p4)) ∨ p3)))) ∨ (p1 → ((True ∧ p1) ∧ True))) ∨ p5) ∧ True) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192866820559530177015859864433 : ((((p5 ∨ (p5 → False)) → (p5 → p3)) ∧ (p5 → p4)) → (p3 ∨ ((p3 → (((p1 → False) → (p5 ∧ (p2 → p2))) → p3)) ∨ (True ∧ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46924519633580057582183679492 : (((((p1 ∨ (p3 ∨ p1)) ∨ ((p5 ∨ p2) ∧ (((p1 → (False → ((p5 ∨ p2) → p3))) ∧ False) ∨ (p1 → p1)))) ∨ True) ∨ (p4 → p4)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340774652702634866606090450302 : (p2 → (((((((False ∨ ((((False ∧ (p4 ∧ (p3 ∨ p3))) ∧ p4) → False) ∧ (p3 → (p4 ∧ p4)))) → p1) ∨ p2) ∧ False) → True) → p1) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111838213915195225056925825654 : ((((((p2 → False) ∧ ((True ∧ p1) ∧ False)) ∨ (((p3 → False) ∨ (p5 ∨ (False ∨ p1))) → p1)) ∨ (False ∨ (p4 ∨ True))) ∨ True) ∨ (p5 → False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321128909717893162248151766189 : (p4 ∨ (p2 ∨ (((((p1 → False) ∧ True) → (p2 ∨ ((p1 ∧ (False → p5)) → ((p2 ∨ p2) ∨ p5)))) → False) → ((p5 → (p3 ∨ p2)) → p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : (((p1 → False) ∧ True) → (p2 ∨ ((p1 ∧ (False → p5)) → ((p2 ∨ p2) ∨ p5)))) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h10 : p1 := by
      -- One of the premise coincides with the conclusion.
      exact h8
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h11 := h5 h10
    -- False on the left can always be used.
    apply False.elim h11
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h12 := h1 h3
  -- False on the left can always be used.
  apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215796011128099873640845065152 : ((p1 ∨ (p2 ∨ (p3 → p2))) ∨ ((p2 ∨ ((True ∨ p2) → (((p4 ∨ (p1 → True)) ∧ p4) ∧ (p2 ∧ ((p2 → True) → True))))) → (p5 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_40074232691959397679705615238 : (((((((p4 → ((p2 ∧ p2) ∧ ((p3 → p3) ∧ (p1 ∧ p3)))) ∧ ((False ∨ p5) ∧ ((p1 ∧ p3) ∨ p2))) ∧ p4) → p1) ∧ p5) ∨ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37379567118095332566967236755 : ((((((p2 ∧ (((p3 ∧ False) → (((((p3 ∨ p1) ∨ p1) → (p2 ∨ (p3 ∧ p5))) ∨ p2) ∧ True)) ∨ p2)) → p5) → p2) ∨ p1) ∧ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_706504729319329267559550211110 : ((((p5 ∨ ((p4 → ((p1 → p4) → p5)) ∨ True)) ∧ (p1 ∨ ((((p2 ∧ p3) → (False → (((True → False) ∨ p3) → False))) ∨ False) → True))) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_620228823776934666628860666175 : (((((p4 ∧ p4) ∨ (True ∧ ((p1 ∧ ((True → ((p1 ∨ (p3 ∧ False)) → ((False → (False → p4)) ∧ p2))) ∨ p3)) ∨ (p4 ∨ True)))) ∨ p2) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_262102426434044711870129018090 : (True ∧ (((((((p3 → p5) ∨ (p2 ∨ p3)) → p2) → ((False ∧ p3) ∧ ((p1 → False) ∨ ((p4 → p1) → (False ∨ p2))))) ∨ p2) ∧ p4) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112844058674712227015472028471 : (((((p4 ∧ p4) ∨ p3) ∧ (((p2 → (p5 ∨ (p5 → (p4 → ((p1 ∨ (p5 → (False ∨ p5))) ∧ p5))))) ∨ p1) ∨ p1)) → p2) ∨ (False → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_637263219399352226754370647196 : ((((((False → ((((p4 → True) ∧ p2) → p3) → True)) ∧ (p4 → p1)) → (p4 → ((True ∨ (p5 ∨ True)) → (p2 → (p3 ∧ p1))))) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_609661693790839986612670973899 : (((((False ∨ (True → (((((True ∨ True) ∨ ((p4 → ((p5 ∧ p3) ∨ (p1 ∨ (p2 ∧ p3)))) ∧ p3)) ∧ p5) ∨ p4) ∨ p3))) ∨ False) ∨ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321660988249864678057881834666 : (p4 ∨ (p4 → ((p5 → (((p3 → (False ∨ (((p3 → p1) ∨ p3) ∧ (p3 ∨ p4)))) → False) ∧ (((p3 → False) ∧ False) ∧ (p5 → True)))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_664600257536690339678953233584 : ((((True → ((True ∨ ((False → p4) → (((((p1 → p3) ∧ p3) ∨ (False → ((False → p2) ∨ p5))) ∨ p2) ∨ True))) ∧ False)) → (p3 ∨ p2)) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- False on the left can always be used.
  apply False.elim h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_747774986876917782884498615407 : ((((False → p1) → ((p1 → p4) ∧ ((True → (((((p3 ∨ p4) → False) ∨ True) ∧ p2) ∨ p1)) → ((p4 ∨ (True → p2)) → (p4 ∧ False))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_749474167257612267073665036520 : (((True ∧ ((((((False → p4) → p5) ∧ True) → False) ∨ ((p1 → True) ∧ (((p3 ∨ p5) → (((p2 ∧ False) ∨ p3) → p5)) → False))) ∧ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49620096188686540774069416408 : (((((p5 ∧ (True ∨ (False ∨ p4))) ∨ (p5 ∨ p2)) → ((p2 → (p3 ∧ p2)) ∧ (((p2 → p2) ∧ False) ∧ p3))) → ((True ∧ p5) ∧ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47574823227427834853984906500 : (((p1 → ((((p4 → (p1 ∧ p4)) ∧ (p5 → ((True ∧ p5) ∨ False))) → (((p3 ∨ p5) ∨ p4) ∧ p3)) ∨ (p5 ∨ p1))) ∨ (p5 → p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_624202875459026955432772816875 : ((((p3 ∨ ((((((p5 ∧ True) ∧ (p4 ∨ False)) → p1) ∧ (p4 ∨ True)) → (((p3 → True) → p5) ∨ (p4 → (False ∨ p4)))) ∧ False)) ∨ True) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_304854636438453332329647714334 : (p1 ∨ (((p5 ∧ ((False ∨ (p4 → p4)) → p3)) ∧ (((False ∨ p3) ∧ True) ∨ (((p5 ∧ ((p1 ∧ True) → p4)) → True) ∧ p5))) → (p3 ∨ False))) := by
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
  cases h3
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h9 =>
      -- False on the left can always be used.
      apply False.elim h9
    case inr h10 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h10
  case inr h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h14 : (False ∨ (p4 → p4)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h15
      -- One of the premise coincides with the conclusion.
      exact h15
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h16 := h5 h14
    -- One of the premise coincides with the conclusion.
    exact h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351642851926549989801943089147 : (p4 → (((p4 ∨ p1) ∧ (p2 ∧ (((True ∧ (p3 → p5)) ∨ ((p2 ∨ True) ∧ False)) ∨ p3))) ∨ ((p2 ∨ False) ∨ ((p2 ∨ p4) ∨ (p3 → p4))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44135390664776740577777643121 : ((((False ∨ ((p3 ∨ p5) → ((False ∧ (p1 ∨ p4)) ∨ ((p5 ∨ True) ∧ ((p3 ∨ p3) ∧ (False ∨ p2)))))) ∨ ((p5 → False) ∧ p4)) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_678246817830382599259706622048 : ((((((p4 ∨ p5) → ((False ∧ (p1 ∧ p2)) → (p4 ∨ p3))) → ((p4 ∨ (p1 ∨ (p2 → p4))) ∧ False)) ∨ ((p1 ∧ (False → True)) → True)) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168546893456919351717172816562 : ((p1 ∧ ((((p3 ∨ (((p5 → True) ∨ p3) ∨ p2)) ∧ p1) ∧ False) → (p5 → (p1 ∨ p3)))) → (((p3 ∧ ((p2 ∨ p1) ∧ p4)) → p5) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_221723322079667207727419430035 : (((False ∧ p2) → p2) ∧ (((p4 ∨ (p5 ∨ (p3 → (p4 ∧ p4)))) ∨ False) ∨ (((((p3 ∨ p4) → (False ∧ p3)) → p4) → True) → (True ∨ p5)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50608177149596900311697465253 : ((((((True ∧ (((p4 → (p4 → p1)) ∨ True) ∨ (p1 → (True ∨ p2)))) ∧ p1) ∨ p2) → (p5 → p4)) → (p3 ∨ (p5 → (p4 → p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204137079967783416334956564885 : ((((p5 ∨ (p3 ∧ p2)) ∧ True) ∧ p4) ∨ (p2 → ((p3 ∨ p1) ∨ (True ∧ (((p2 → p2) → p1) ∨ ((((p5 → True) ∧ True) ∨ p1) ∨ p3)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57199953187312971553567369397 : ((((p5 ∨ False) ∨ False) ∨ (((True → False) → (False ∨ p2)) ∧ (((False ∨ ((False ∨ True) ∨ (p4 ∧ ((True ∨ p2) ∧ p3)))) ∧ p5) ∨ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47295378616870846867317088944 : (((((p3 ∨ p3) ∨ p3) ∧ ((((((True → (p1 → p2)) → False) ∧ p5) ∨ p2) ∧ (p4 ∨ p5)) → (p2 → (p1 ∨ p1)))) ∨ (p3 → True)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56604828811527625594828070047 : (((p4 → (p2 → (p5 → p1))) → ((((p2 ∨ (True → p2)) ∨ p5) ∨ (True → ((p1 → (p3 ∧ p2)) ∨ p4))) ∧ (p4 ∧ (False ∨ p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115748846837442892600114107602 : ((((p4 → False) → (p1 → (p5 ∧ True))) → (((False ∨ p2) ∧ (p3 ∨ p5)) ∨ (p2 ∨ ((p1 → ((p4 → p1) ∨ p5)) ∨ p3)))) ∨ (False ∨ p4)) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_343800716407734960382857881193 : (p2 → (p2 ∧ ((((False ∨ (((((p4 ∨ p2) ∧ p1) ∧ p2) ∧ True) ∨ (((p1 ∨ (True ∧ p2)) → p1) ∨ False))) ∨ p2) ∨ (p1 ∧ True)) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328924344490353082975519914162 : (True → (((p2 ∨ p4) ∨ (((p4 ∧ True) ∨ p3) ∨ p4)) → ((p4 ∨ (True ∧ p1)) ∨ (((p1 → p1) → p5) ∨ ((True → p1) → (False → p4)))))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h5
      -- Implications on the right can always be decomposed.
      intro h6
      -- False on the left can always be used.
      apply False.elim h6
    case inr h7 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h7
  case inr h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Conjunctions on the left can always be decomposed.
        let h11 := h10.left
        let h12 := h10.right
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h11
      case inr h13 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h14
        -- Implications on the right can always be decomposed.
        intro h15
        -- False on the left can always be used.
        apply False.elim h15
    case inr h16 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_756219982673973651624043536689 : (((p1 ∧ (((p1 → (True → (p2 ∨ (p2 ∧ p2)))) ∧ ((((p4 → (p3 → False)) → (p3 → (True ∧ p1))) ∨ p2) ∧ True)) ∨ (p4 ∨ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323228411265844072910866530033 : (p5 ∨ ((((p3 ∨ (p2 ∧ p3)) ∨ (True → True)) ∧ (((p4 ∨ (p4 ∨ p3)) ∨ p1) → (p3 → (True ∧ ((p5 ∨ p2) → p2))))) ∨ (p5 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213240894038009332697155703988 : ((((p4 ∧ False) → True) ∧ p4) ∨ (p5 → ((((p1 ∧ (p5 ∨ p3)) ∧ (((p2 → p4) ∧ p4) → p4)) ∨ (p3 ∧ ((p2 ∨ p3) ∨ True))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_155787471778965691650199646179 : (((False → p3) → (p2 → ((((True ∨ p1) ∨ (p5 → (p3 ∨ p5))) ∨ p5) → (p3 → (p3 ∨ True))))) ∧ (p5 ∨ (p4 ∨ ((False → p5) ∨ p5)))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h11
  -- False on the left can always be used.
  apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150206415128190504765734667679 : ((p2 → (((p3 ∧ ((((p3 → False) → p3) → True) ∧ (False → p1))) ∨ False) → (True → (False ∧ (p2 ∨ p4))))) ∨ ((p4 ∧ False) → (p4 ∧ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259799546161194453939466519575 : ((p1 → p3) → ((p3 ∨ (((p5 ∨ (p3 → (p2 ∧ False))) → True) → (p2 ∨ ((p2 ∧ p2) ∨ ((True ∨ (False ∨ p1)) ∨ (p5 → p4)))))) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
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
theorem thm_5_vars_17917957054474036620580739765 : ((((p5 ∨ (p5 ∨ ((p3 → (((p1 ∧ p4) ∨ (p4 → (True → p4))) ∨ p2)) ∧ p4))) ∨ (p4 ∧ p2)) ∨ (((True ∨ p3) ∨ p1) → True)) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158514892395877067660332982705 : (((p2 ∨ False) → ((p1 ∨ (False ∧ p2)) ∨ (((False → (p3 ∧ ((p4 → p3) ∧ p5))) → False) ∧ True))) ∨ ((((p3 ∧ False) → p3) → p4) → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p3 ∧ False) → p3) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- False on the left can always be used.
    apply False.elim h5
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41102486010288740573046604534 : (((((False ∧ (False ∧ ((p3 ∧ p2) → True))) ∧ ((p4 ∧ True) → ((False ∧ ((p3 → p2) → p4)) ∧ False))) ∧ (p5 → (p4 → p1))) ∨ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_701553081857419144409943381383 : (((((p1 ∧ p4) ∧ ((p4 ∧ (False ∧ p4)) ∨ (p1 → p3))) ∧ (False ∧ (((p2 → ((p4 ∨ p3) → p1)) → ((p2 ∧ True) → p2)) → p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_687562909515190854377988114268 : (((((((((p1 ∧ True) ∧ p2) ∧ (p1 ∨ ((False → True) ∨ p3))) ∨ p4) → p2) → p4) ∧ (False → (p2 ∧ (False ∧ ((True ∨ p4) → p2))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48585693902731184184624663472 : ((((((False ∨ (p2 → p4)) ∧ ((p4 ∧ (p3 ∨ (p3 ∨ (p4 ∨ (p3 ∨ p2))))) ∧ p4)) ∨ p2) ∧ (p4 → p2)) ∧ (p5 → (False → p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_640220698842850345253512134614 : (((((True ∧ (p3 ∨ False)) → ((((((((False → p4) ∨ p5) ∨ p4) ∨ p2) → p1) → (((p2 → p2) ∨ p1) ∨ p1)) ∨ p4) ∨ p4)) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158618923419470149504590476884 : ((False ∧ (p1 ∧ ((((((p5 → p4) ∨ (p2 ∨ p4)) → p4) ∧ True) ∨ True) → (True → (p5 ∧ p1))))) ∨ (p2 → (((p4 ∨ p4) → p3) ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_224375047772727066624093023932 : ((False → (p5 → True)) ∧ (((p3 → p3) → ((False ∧ True) ∨ p5)) ∨ ((p3 → ((p5 ∨ (p1 ∨ p3)) → True)) → (((p5 ∧ p2) ∧ False) → p4)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_616041800016277738829003245506 : ((((((p2 → p4) → (p1 ∨ ((p2 ∨ True) → (p4 ∧ (p3 → (True → False)))))) → (((True → ((True ∧ p2) → p3)) ∨ p4) ∨ False)) ∨ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_667587743967163721127798494752 : ((((p1 ∧ (p2 → ((False ∨ True) → (p3 → (((False ∧ ((p2 ∨ p3) ∧ (p4 ∧ p5))) ∨ (p4 ∧ p5)) ∨ p4))))) ∧ ((False ∧ False) ∧ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315030184509105297311035690872 : (p3 ∨ ((p2 ∨ (p3 ∧ ((p4 ∨ p5) ∨ (p2 ∧ p2)))) ∨ (((p4 ∧ p4) → (p4 ∨ p1)) ∨ ((False → p3) ∨ ((p4 ∨ False) ∨ (p1 ∨ p4)))))) := by
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
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_153834243616494727444888768839 : ((p5 → (p4 ∧ ((((p1 ∧ False) ∨ (p2 → (False ∨ ((((p2 ∧ p3) ∨ False) ∨ p2) ∨ p4)))) ∧ p2) → p4))) → ((True ∧ p4) ∨ (p2 → p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350156757771229556054260573631 : (p4 → (((((p4 ∧ p4) → (False ∨ (p2 ∧ p4))) ∨ True) ∧ ((p5 → ((True ∨ (((p1 → (p2 → p3)) ∨ True) ∧ p3)) → False)) ∧ p2)) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



