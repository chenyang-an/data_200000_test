variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_739447654308009113402840163994 : ((((p5 ∧ False) ∨ (((((((p3 ∨ (p2 ∨ p3)) ∧ p2) ∧ p3) ∨ (((p3 → p3) ∨ (p5 ∨ p3)) ∧ (p1 ∨ True))) ∨ False) ∨ True) ∨ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_783968063253347065627392101432 : (((p3 ∨ ((True → (p3 → p2)) → (p2 → (True ∧ ((p2 ∧ ((p2 ∧ p4) ∧ ((p1 → (p4 → p3)) ∧ ((False → p2) ∧ False)))) ∨ p5))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66199089562322156777897782964 : ((p5 ∨ (((True → p1) ∧ (((True → True) ∧ (p3 ∨ ((p4 → (p1 ∨ p1)) → p3))) → p3)) → ((p2 ∧ True) ∧ (True ∧ (p5 ∨ True))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174282783055058999331227372499 : (((p3 ∧ ((p3 ∨ p2) ∧ (((p4 ∧ p5) → p4) ∨ p4))) ∧ ((p3 ∨ p1) ∧ p3)) → (((p5 ∧ p3) ∧ p3) ∨ (p5 → (p2 → (p5 ∨ False))))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h3.left
      let h11 := h3.right
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h13
        -- Implications on the right can always be decomposed.
        intro h14
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h13
      case inr h15 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h16
        -- Implications on the right can always be decomposed.
        intro h17
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h16
    case inr h18 =>
      -- Conjunctions on the left can always be decomposed.
      let h19 := h3.left
      let h20 := h3.right
      -- Disjunctions on the left can always be decomposed.
      cases h19
      case inl h21 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h22
        -- Implications on the right can always be decomposed.
        intro h23
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h22
      case inr h24 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h25
        -- Implications on the right can always be decomposed.
        intro h26
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h25
  case inr h27 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h28 =>
      -- Conjunctions on the left can always be decomposed.
      let h29 := h3.left
      let h30 := h3.right
      -- Disjunctions on the left can always be decomposed.
      cases h29
      case inl h31 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h32
        -- Implications on the right can always be decomposed.
        intro h33
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h32
      case inr h34 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h35
        -- Implications on the right can always be decomposed.
        intro h36
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h35
    case inr h37 =>
      -- Conjunctions on the left can always be decomposed.
      let h38 := h3.left
      let h39 := h3.right
      -- Disjunctions on the left can always be decomposed.
      cases h38
      case inl h40 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h41
        -- Implications on the right can always be decomposed.
        intro h42
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h41
      case inr h43 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h44
        -- Implications on the right can always be decomposed.
        intro h45
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h44



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165930846997100852066298594780 : (((p4 ∧ p2) ∧ (p3 ∨ (p5 ∧ ((p1 ∧ ((p1 → p5) ∧ (p3 ∨ (p4 → p3)))) ∧ p5)))) ∨ (((p2 ∨ p3) → (False → (False → p1))) ∧ True)) := by
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
  -- False on the left can always be used.
  apply False.elim h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_343619403555530169351638829657 : (p2 → (True ∧ ((((((True → False) → ((p2 → True) ∧ p2)) ∧ p5) ∨ (p5 ∧ True)) ∧ (p5 ∧ ((p2 → p1) → ((p3 ∧ p3) ∧ p5)))) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158443381976176822049899505921 : (((p3 ∨ p1) ∨ (p5 ∧ (((p3 ∧ p4) ∧ True) ∧ (p5 ∨ (p4 → (((p2 ∧ p1) ∧ True) → p1)))))) ∨ ((p1 ∨ p2) → ((False ∧ p2) → p5))) := by
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
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37529948541250388649192809672 : ((((p1 ∧ (p1 ∧ (((p4 → (False ∨ p4)) ∨ p4) → ((((p4 ∨ False) ∨ (p4 ∧ (p3 ∨ (p3 ∧ p2)))) → p5) ∧ False)))) ∨ p2) ∧ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179166169008665156246441787970 : ((p2 ∧ (True ∧ ((p5 → ((p3 ∨ p5) ∨ ((False ∧ p1) → p2))) → p1))) ∨ (((False ∧ (p3 → (((p2 → True) ∨ p2) → p3))) ∧ p2) → p2)) := by
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
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56660040524764696397513560166 : ((((p5 ∨ False) ∧ p2) ∧ ((((p3 ∧ ((p4 ∨ p4) ∨ p1)) ∨ ((p4 → (False ∨ p2)) → (p4 → p3))) ∨ (True ∨ p1)) ∨ (p5 ∨ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_155678037110622573046301650289 : (((p5 ∧ p1) ∨ ((p5 ∧ ((p5 → False) ∨ False)) ∨ ((p1 ∨ (p1 → p2)) → ((p1 ∧ False) → True)))) ∧ (p2 → (((p2 ∨ p1) ∨ p3) → True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190880328349631121941373760626 : ((((True ∧ p2) ∨ (True → (True → p2))) → (p1 ∨ p1)) ∨ (((((((p1 ∨ True) ∨ True) ∨ p5) ∨ False) ∨ False) ∨ p2) ∧ (p3 → (p2 → p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_790745764885782889339077081888 : (((p5 ∨ (True → (p2 → (((((True → p4) ∧ (False → (True ∧ True))) ∧ (p3 ∨ ((p3 ∨ p2) ∨ (p1 ∧ p4)))) → (p3 → False)) ∨ True)))) ∨ False) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337529718394755653604916425303 : (p1 → (((((((p2 ∨ ((p3 → p4) ∧ ((True ∧ p2) ∧ False))) ∧ p4) ∧ p3) ∨ p3) ∧ p5) ∨ (False → True)) ∨ ((p1 → False) ∨ (p5 ∧ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118133777939599952865329806965 : ((False ∨ ((p5 ∨ (((p2 ∨ ((p2 ∧ p5) ∨ True)) ∧ (True ∧ (p1 ∨ (p2 ∧ p1)))) ∧ (p5 → p4))) ∨ (False ∨ (p1 ∨ True)))) ∨ (p3 ∨ p5)) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180713854420277677632799754555 : ((((p4 → False) ∨ (p5 ∧ p1)) ∧ (((p1 → (p5 ∨ p3)) ∨ p4) ∨ p4)) → ((p4 ∧ False) ∨ (((p3 → p2) ∨ (p4 ∨ True)) ∨ (p5 → p4)))) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
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
      case inr h7 =>
        -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
        have h8 : p4 := by
          -- One of the premise coincides with the conclusion.
          exact h7
        -- We have shown the premise of h4, we can now drive its conclusion.
        let h9 := h4 h8
        -- False on the left can always be used.
        apply False.elim h9
    case inr h10 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h11 : p4 := by
        -- One of the premise coincides with the conclusion.
        exact h10
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h12 := h4 h11
      -- False on the left can always be used.
      apply False.elim h12
  case inr h13 =>
    -- Conjunctions on the left can always be decomposed.
    let h14 := h13.left
    let h15 := h13.right
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h16 =>
      -- Disjunctions on the left can always be decomposed.
      cases h16
      case inl h17 =>
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
      case inr h18 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h18
    case inr h19 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45711104837237460355392146174 : (((True → (((((((p3 → p4) ∧ ((p2 ∧ ((p1 ∨ p1) → p2)) → True)) ∨ p3) → p4) ∧ p2) → (p4 ∨ False)) → (p5 ∨ p1))) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_748722350827365586493664713661 : ((((p3 → p4) → (True ∧ (p1 ∧ (((True ∨ True) → p4) → ((p3 ∨ p1) ∧ ((p5 ∧ (((p1 → p5) ∧ False) ∧ (p2 → p4))) → False)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_311910289892524723084228336253 : (p2 ∨ (p2 ∨ (p3 ∨ ((((False → p3) → True) ∨ p4) → (((False ∧ p5) ∨ p3) ∨ ((p5 ∨ ((True ∧ p5) ∧ p5)) → (True ∧ (p2 ∨ p5)))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Conjunctions on the left can always be decomposed.
      let h8 := h6.left
      let h9 := h6.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h7
  case inr h10 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h11
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h12
    case inr h13 =>
      -- Conjunctions on the left can always be decomposed.
      let h14 := h13.left
      let h15 := h13.right
      -- Conjunctions on the left can always be decomposed.
      let h16 := h14.left
      let h17 := h14.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178592769975073782353434112546 : ((((p2 ∨ ((p5 ∧ p3) → False)) → p5) ∨ (((p2 → False) → p2) ∨ False)) ∨ (p1 → (p2 ∨ (((p4 → (False ∨ p1)) ∧ p5) → (p5 ∨ p2))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_616583680723653735678377802276 : (((((((((p4 → False) ∨ p2) ∨ p5) → p3) ∨ (True ∧ p4)) ∧ ((((False → False) ∧ ((p4 → p2) → p3)) ∧ p4) → (p3 ∧ p3))) ∨ True) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_40616000040927264712027774547 : ((((((True → p2) ∨ ((p2 ∧ ((((p4 ∨ (p1 ∨ p3)) ∧ True) ∧ (p4 ∧ p4)) ∧ (p2 ∨ p3))) → (p3 ∨ p2))) ∨ p4) → p1) ∨ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68584456543318110983717905932 : ((p4 → (((p1 ∧ p1) → ((p1 ∨ (True ∨ True)) → (p5 ∨ (p2 ∨ ((((p2 ∨ p1) ∧ (p5 ∧ True)) ∨ (p5 ∧ p1)) ∨ p1))))) ∧ p4)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h2.left
      let h10 := h2.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h10
    case inr h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h2.left
      let h13 := h2.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h13
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_339982900970390165799071884678 : (p1 → (p1 → (((p5 → p1) → ((p3 ∨ p2) ∨ (((p5 ∨ (p3 ∨ ((p3 ∧ (p2 → p4)) ∧ p4))) → p4) ∧ p5))) ∨ ((True → p1) ∨ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171811317588487825755178915165 : (((((((p3 ∧ p2) ∧ p4) ∧ False) → p2) ∨ (p5 → (p5 ∨ (p1 ∨ p1)))) → p2) ∨ ((p5 ∧ (p2 → (((p3 ∧ p2) ∨ p5) ∧ p4))) → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_766836678883698180081498081901 : (((p4 ∧ (p4 ∨ ((True → (((((p3 → p5) → False) ∨ ((((p1 ∨ p4) ∨ p3) ∨ True) → p5)) → p3) ∨ (True → p3))) ∨ (p4 ∨ True)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227118019695851041875583879063 : (((p4 ∨ p2) → p5) ∨ ((p5 ∧ (False ∧ (((((((False → False) ∧ p4) ∧ ((p1 ∧ p5) ∧ (True ∧ True))) → p5) ∧ p3) ∨ p4) → p2))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191617324431239296370025213101 : ((p3 ∧ ((p5 ∨ p4) → ((p1 ∧ p3) → (p4 → p4)))) ∨ (p2 → (((True ∧ ((p4 ∨ p2) ∨ p4)) → (((p4 → p3) → p4) ∨ p5)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42683976307337016492503262789 : (((p5 ∨ (((p1 ∨ (((p4 → p1) ∧ (p4 ∧ (p3 ∨ p4))) ∨ (p1 ∧ (p1 ∨ (p3 ∧ False))))) ∨ (True ∧ (p3 → False))) ∧ False)) ∨ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42987267761250679963507483286 : (((p5 → (False ∧ ((p2 → (True ∨ True)) → (True → (False ∨ ((p5 ∧ (p1 → (p5 → ((p3 ∧ p3) ∨ p2)))) → (p2 ∨ p4))))))) ∨ True) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147067883782538313793750181051 : (((((p3 ∨ p5) ∧ ((p5 → True) ∧ (p5 ∧ p3))) → (((((p4 ∨ False) ∧ p2) ∨ p1) ∨ p2) ∧ p5)) ∧ p5) ∨ (((False ∧ p3) ∨ True) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157016870046439154130083071595 : ((((True ∧ p1) ∧ (p3 ∧ (p4 → ((p4 ∧ (((p1 ∧ True) ∧ (p4 ∧ p4)) → p3)) ∨ p2)))) ∨ p5) ∨ ((p2 → p4) ∨ ((True → p3) → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52683809418076761371186925083 : (((p4 ∨ ((((p4 ∨ p5) → False) ∧ p4) ∧ ((p3 ∨ (True ∧ p3)) ∨ p5))) ∨ ((((p4 → p3) ∧ (p1 → (p2 → p3))) ∨ False) → True)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263429024032615842810447705499 : (True ∧ ((p1 → ((((((p1 ∨ True) ∨ (((p1 ∨ (p5 ∨ p5)) → p3) ∧ p2)) → (p1 → p5)) ∨ False) ∨ True) ∧ False)) ∨ (p2 ∨ (p3 → True)))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225191707414323488412593556376 : (((p4 ∧ p3) ∧ p1) ∨ ((True → ((p1 ∨ (((p3 ∧ p5) → (((((p4 → p3) ∨ False) ∧ (p1 ∧ False)) → p5) ∧ p1)) → p1)) → p1)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61780745251585357291527017827 : ((p2 ∧ (((p3 ∧ False) ∧ ((((((p2 → False) ∧ p2) ∧ ((True → (p4 ∧ p3)) ∧ True)) ∨ p3) ∨ (p5 ∧ p4)) → (p2 → p3))) ∧ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160371603840091772751183839831 : ((((((p2 → (p2 → p5)) ∧ p4) ∧ False) ∨ (((p4 ∨ p3) ∨ p3) → p3)) ∧ ((p2 ∧ p1) → True)) → (((p2 ∧ (p4 ∨ p2)) → False) ∨ True)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- False on the left can always be used.
    apply False.elim h6
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115701358920615786444970157251 : (((((p2 ∨ (p3 ∨ p2)) ∧ True) ∧ True) → ((p5 → ((p1 ∧ (p5 ∨ p5)) → p2)) ∧ (p2 → ((False → (p5 ∧ True)) → p1)))) ∨ (True ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_617888354155673205195785346936 : ((((((p3 → p1) ∧ ((p4 → p4) → p1)) → (((((p3 ∧ p4) → (p5 ∨ p4)) → (p2 → p3)) ∨ (p2 → (p1 → p2))) ∨ p5)) ∨ False) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- One of the premise coincides with the conclusion.
  exact h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228887482018865442910158419431 : ((p4 ∨ (p2 ∧ p2)) ∨ (p5 ∨ (True ∧ (((False ∧ ((((False ∨ (((False → p2) ∧ False) → p3)) → (p3 → p2)) ∨ p1) ∨ p1)) ∨ True) ∨ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_640852755908527122663860729264 : (((((p3 → p4) ∧ ((False ∨ (p1 ∨ ((p5 → p5) → p1))) → ((p1 ∧ p1) → (p4 → ((((False ∧ p3) ∧ p3) ∨ p4) → p4))))) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42704616536629064478437036151 : (((p5 ∨ ((False ∨ ((p3 ∨ (p3 ∧ p2)) ∧ p4)) → (p1 ∨ (p4 ∧ ((p3 → False) ∧ (((p2 → False) ∨ (True → True)) ∨ p3)))))) ∨ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308463242899335553151533793125 : (p2 ∨ (((((p3 → p1) → p2) → ((((p4 ∧ p4) ∨ ((p2 → (p5 ∨ (False → p3))) → p3)) → p5) ∨ (False ∨ True))) ∨ (p2 ∨ p5)) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217297646199186747259352944516 : (((p4 ∧ (p1 → p4)) ∨ p5) → (p1 ∨ (p4 ∨ ((((p4 ∨ (((p4 ∨ (p3 ∨ p2)) → False) → p5)) → (p2 ∧ p1)) → (p2 ∨ p4)) ∧ p5)))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h6
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h7 : (p4 ∨ (((p4 ∨ (p3 ∨ p2)) → False) → p5)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- One of the premise coincides with the conclusion.
      exact h5
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h9 := h6 h7
    -- We need to get the left conjuct of h9 based on <expert-advice>.
    let h10 := h9.left
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h10
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314638808455881395335344998510 : (p3 ∨ ((((p4 → ((True ∨ (p2 ∧ (p5 ∧ (False → (p5 ∧ p3))))) ∧ True)) → False) ∧ p5) ∨ ((p2 ∧ (p1 ∨ ((p4 ∧ False) → p3))) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_226456751756217612801657319218 : (((p1 → p4) ∨ False) ∨ (p4 → ((p2 ∧ p5) ∨ ((p1 → ((p1 ∨ (False ∧ p1)) → (p2 ∧ True))) → ((p2 → ((False ∨ p3) → p1)) ∨ True))))) := by
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
theorem thm_5_vars_59623425862875104393519629994 : (((p5 → False) ∨ ((p2 ∧ False) ∨ ((p5 ∧ ((((((p3 ∨ False) ∨ (p5 ∧ (False → p2))) ∧ p5) ∧ p5) ∨ p4) ∨ (False ∧ p3))) ∧ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193569097480062982089160322219 : (((p2 ∨ True) → ((False → (p5 ∨ p4)) ∧ (False ∧ True))) → ((p3 → (((((p4 ∨ p4) ∨ (p3 ∨ True)) ∨ (True ∧ p4)) ∨ p5) → p2)) ∧ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Disjunctions on the left can always be decomposed.
        cases h6
        case inl h7 =>
          -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
          have h8 : (p2 ∨ True) := by
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h1, we can now drive its conclusion.
          let h9 := h1 h8
          -- We need to get the right conjuct of h9 based on <expert-advice>.
          let h10 := h9.right
          -- We need to get the left conjuct of h10 based on <expert-advice>.
          let h11 := h10.left
          -- False on the left can always be used.
          apply False.elim h11
        case inr h12 =>
          -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
          have h13 : (p2 ∨ True) := by
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h1, we can now drive its conclusion.
          let h14 := h1 h13
          -- We need to get the right conjuct of h14 based on <expert-advice>.
          let h15 := h14.right
          -- We need to get the left conjuct of h15 based on <expert-advice>.
          let h16 := h15.left
          -- False on the left can always be used.
          apply False.elim h16
      case inr h17 =>
        -- Disjunctions on the left can always be decomposed.
        cases h17
        case inl h18 =>
          -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
          have h19 : (p2 ∨ True) := by
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h1, we can now drive its conclusion.
          let h20 := h1 h19
          -- We need to get the right conjuct of h20 based on <expert-advice>.
          let h21 := h20.right
          -- We need to get the left conjuct of h21 based on <expert-advice>.
          let h22 := h21.left
          -- False on the left can always be used.
          apply False.elim h22
        case inr h23 =>
          -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
          have h24 : (p2 ∨ True) := by
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h1, we can now drive its conclusion.
          let h25 := h1 h24
          -- We need to get the right conjuct of h25 based on <expert-advice>.
          let h26 := h25.right
          -- We need to get the left conjuct of h26 based on <expert-advice>.
          let h27 := h26.left
          -- False on the left can always be used.
          apply False.elim h27
    case inr h28 =>
      -- Conjunctions on the left can always be decomposed.
      let h29 := h28.left
      let h30 := h28.right
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h31 : (p2 ∨ True) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h32 := h1 h31
      -- We need to get the right conjuct of h32 based on <expert-advice>.
      let h33 := h32.right
      -- We need to get the left conjuct of h33 based on <expert-advice>.
      let h34 := h33.left
      -- False on the left can always be used.
      apply False.elim h34
  case inr h35 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h36 : (p2 ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h37 := h1 h36
    -- We need to get the right conjuct of h37 based on <expert-advice>.
    let h38 := h37.right
    -- We need to get the left conjuct of h38 based on <expert-advice>.
    let h39 := h38.left
    -- False on the left can always be used.
    apply False.elim h39
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h40 : (p2 ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h41 := h1 h40
  -- We need to get the right conjuct of h41 based on <expert-advice>.
  let h42 := h41.right
  -- We need to get the left conjuct of h42 based on <expert-advice>.
  let h43 := h42.left
  -- False on the left can always be used.
  apply False.elim h43



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_712726918015019633457979631370 : (((((p1 ∧ p3) ∨ ((p4 ∧ p4) ∨ False)) ∨ ((p2 ∧ (((p1 → p3) ∨ ((False ∨ p3) ∨ (False → p5))) → (True ∧ False))) → (p1 ∧ p1))) ∨ p3) ∧ True) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : ((p1 → p3) ∨ ((False ∨ p3) ∨ (False → p5))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- False on the left can always be used.
    apply False.elim h5
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h4
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- False on the left can always be used.
  apply False.elim h7
  -- Conjunctions on the left can always be decomposed.
  let h8 := h1.left
  let h9 := h1.right
  -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
  have h10 : ((p1 → p3) ∨ ((False ∨ p3) ∨ (False → p5))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h11
    -- False on the left can always be used.
    apply False.elim h11
  -- We have shown the premise of h9, we can now drive its conclusion.
  let h12 := h9 h10
  -- We need to get the right conjuct of h12 based on <expert-advice>.
  let h13 := h12.right
  -- False on the left can always be used.
  apply False.elim h13
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190096336210706518129472813851 : ((((p2 ∧ ((p2 ∧ False) ∧ p5)) ∨ (p4 ∨ False)) ∧ p3) ∨ (p3 → (p1 ∨ (((((p1 → (p4 ∧ p5)) → p1) ∧ p3) ∨ p4) → (p3 ∨ False))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354670897274682630288809042972 : (p5 → (((p3 ∨ (True ∧ (((False ∨ ((((((p5 ∨ False) → p3) ∨ (False ∨ p2)) → False) ∧ p1) ∧ p5)) ∨ False) ∨ (p2 → False)))) → False) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147507346441897817665525253679 : (((p2 ∨ (((((p1 ∧ (p1 ∨ p1)) ∨ (False ∨ False)) → p5) ∨ ((False ∨ p5) ∧ p2)) ∧ (p2 ∧ p1))) ∨ True) ∨ ((p2 ∨ p4) ∧ (True → p2))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_619343643761270557290734899998 : ((((((p2 ∧ p1) → True) → ((((p4 → (True ∧ p5)) ∧ ((p2 ∧ p5) ∨ p3)) → (p5 ∧ ((p4 → p2) ∨ (True ∨ p4)))) ∧ True)) ∨ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66149774487002654190231307805 : ((p5 ∨ ((((((p4 ∨ (p2 → p1)) ∨ (p2 ∧ True)) ∧ p4) ∨ (((p4 ∧ (p3 ∧ p3)) → True) ∨ p2)) ∧ (p3 ∨ p4)) → (False ∧ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227952507806555990390550469112 : ((p3 ∧ (p4 ∧ False)) ∨ (p5 → ((p1 ∨ (((((True ∨ p4) ∧ p5) ∧ (((p5 → ((p1 ∧ p4) ∧ True)) ∧ p2) ∨ False)) ∧ p3) ∧ p4)) → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h7.left
    let h10 := h7.right
    -- Conjunctions on the left can always be decomposed.
    let h11 := h9.left
    let h12 := h9.right
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h13 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h14 =>
        -- Conjunctions on the left can always be decomposed.
        let h15 := h14.left
        let h16 := h14.right
        -- We want to use the implication h15 based on <expert-advice>. So we show its premise.
        have h17 : p5 := by
          -- One of the premise coincides with the conclusion.
          exact h1
        -- We have shown the premise of h15, we can now drive its conclusion.
        let h18 := h15 h17
        -- We need to get the left conjuct of h18 based on <expert-advice>.
        let h19 := h18.left
        -- We need to get the left conjuct of h19 based on <expert-advice>.
        let h20 := h19.left
        -- One of the premise coincides with the conclusion.
        exact h20
      case inr h21 =>
        -- False on the left can always be used.
        apply False.elim h21
    case inr h22 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h23 =>
        -- Conjunctions on the left can always be decomposed.
        let h24 := h23.left
        let h25 := h23.right
        -- We want to use the implication h24 based on <expert-advice>. So we show its premise.
        have h26 : p5 := by
          -- One of the premise coincides with the conclusion.
          exact h1
        -- We have shown the premise of h24, we can now drive its conclusion.
        let h27 := h24 h26
        -- We need to get the left conjuct of h27 based on <expert-advice>.
        let h28 := h27.left
        -- We need to get the left conjuct of h28 based on <expert-advice>.
        let h29 := h28.left
        -- One of the premise coincides with the conclusion.
        exact h29
      case inr h30 =>
        -- False on the left can always be used.
        apply False.elim h30



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119149794731231846956713021301 : ((p1 → (p5 → (((p3 ∧ ((((p2 ∧ p1) ∨ p3) ∨ (p5 → ((p4 ∧ p1) ∨ p2))) ∧ p3)) ∨ False) ∨ ((p1 ∨ p2) ∨ p4)))) ∨ (p3 → p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64409664282367224196667169669 : ((p1 ∨ (((p2 ∧ (False → True)) → (p1 ∨ ((((p5 → p3) ∨ (p1 → (((True ∧ p3) → p1) ∨ p4))) → p3) → (p5 → p1)))) → p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113494800702571744645573520381 : (((((((p2 → (((False → (p3 ∧ p3)) ∨ (p1 ∨ False)) ∧ False)) ∨ p5) ∧ p4) ∧ p5) ∨ ((True → p2) ∨ p3)) ∨ (p3 ∧ p5)) ∨ (True ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_650171739115694680418917161541 : (((((p5 ∨ (((True ∧ False) → ((False ∨ True) ∧ (p4 → (p2 ∨ False)))) ∧ (True → True))) ∧ (((p3 ∨ p5) → False) ∧ p2)) ∧ (p1 → p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_329665003582004576356611769319 : (True → ((True ∨ p1) → ((((p1 ∧ (((p1 ∧ p4) → False) → (((p5 → p1) → True) ∧ p5))) ∨ p2) ∨ (((True ∨ p4) → False) → p1)) ∨ p3))) := by
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
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h5 : (True ∨ p4) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h6 := h4 h5
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231096228469201360943434380312 : (((False ∨ p3) ∨ p1) → ((((p2 ∨ False) ∧ p2) ∨ (((p2 → True) → (p4 ∨ p2)) ∨ True)) → ((False ∧ p5) ∨ ((p2 → (True ∨ False)) ∨ p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h7 =>
        -- Disjunctions on the left can always be decomposed.
        cases h7
        case inl h8 =>
          -- False on the left can always be used.
          apply False.elim h8
        case inr h9 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h5
      case inr h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h5
    case inr h11 =>
      -- False on the left can always be used.
      apply False.elim h11
  case inr h12 =>
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h13 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h14 =>
        -- Disjunctions on the left can always be decomposed.
        cases h14
        case inl h15 =>
          -- False on the left can always be used.
          apply False.elim h15
        case inr h16 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Implications on the right can always be decomposed.
          intro h17
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h18 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h19
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h20 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h21 =>
        -- Disjunctions on the left can always be decomposed.
        cases h21
        case inl h22 =>
          -- False on the left can always be used.
          apply False.elim h22
        case inr h23 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Implications on the right can always be decomposed.
          intro h24
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h25 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h26
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_631350371462397847829997123409 : ((((((((False ∨ (((p1 ∧ True) ∨ True) → p1)) ∨ (p5 ∧ (p4 ∨ (((p5 → False) → p3) ∧ p3)))) ∨ p2) ∧ (False → p1)) → False) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118771699485275996653727552963 : ((p5 ∨ (p4 ∧ (((p4 ∨ (False ∧ (p1 ∧ p2))) ∧ (p4 ∨ (((p1 ∨ ((p4 → p1) → p2)) → (p3 → True)) ∨ True))) → p2))) ∨ (p5 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44810168482274118122038423800 : ((((p2 ∧ (p3 → p4)) ∧ (((False ∨ True) ∨ p1) → ((p2 ∨ ((((True ∨ p4) → p3) ∨ (p2 ∨ p3)) ∨ (p5 ∧ True))) ∧ False))) → False) ∨ p5) := by
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
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h6 : ((False ∨ True) ∨ p1) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h7 := h3 h6
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56588492751563696365446530953 : (((p2 → ((p2 → p2) ∨ p1)) → ((True ∨ p4) → ((p1 ∧ p2) ∧ (((p5 → p5) ∧ (True ∨ p5)) ∨ ((True ∧ (p1 ∨ p3)) ∨ p1))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46161022882234726124344425628 : (((((((((False ∧ True) ∨ False) → True) ∨ (((p4 ∧ p1) ∧ p2) ∧ p2)) ∨ False) → (p1 ∧ ((True ∧ False) ∧ True))) → False) ∧ (p1 ∨ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50675452958572144665967181464 : (((((False → (True ∧ False)) ∨ False) ∧ (p2 → (p5 → (p5 ∧ (p1 ∨ ((p4 ∨ (False ∨ p2)) ∨ p3)))))) → (((p4 → p2) ∧ p1) ∨ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_666759063790681350427997398354 : (((((((p2 ∧ (p1 ∨ True)) ∨ (p5 ∨ p3)) ∨ p4) ∧ ((p5 ∨ p4) ∨ ((p3 ∨ p1) ∧ ((True ∨ p5) ∧ p3)))) ∧ ((p5 ∧ True) ∨ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213480971123494588311423890135 : (((p1 → (p2 ∨ p2)) ∧ p5) ∨ ((p3 ∨ p4) ∨ (False → (True → (p3 ∨ (p2 ∨ ((p1 → (p2 → (((p5 ∨ p1) ∨ p1) → p3))) → p3))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51085701026701402412006568794 : ((((((True ∧ ((p5 → p4) ∧ p2)) ∧ ((False ∨ p2) ∧ ((p4 → p1) ∨ False))) ∧ False) ∧ p4) ∨ (((False → True) → (p1 → True)) → p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328715919010666672226716501961 : (True → ((p2 ∨ ((((p4 → p5) → p1) ∧ False) ∨ (False ∨ (p2 ∧ p5)))) ∨ ((p1 → ((p5 → (True ∧ (p3 ∨ p2))) ∨ (p5 ∨ p2))) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166777559544772659046010876818 : ((p5 → (((p3 ∧ (((p2 ∧ p3) ∨ p1) ∧ p2)) ∨ p1) ∨ (((True → False) ∧ p4) → p5))) ∨ (((p3 → False) ∧ (True ∧ False)) ∨ (p4 ∧ p3))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_672795167535382759521744637918 : ((((((((True → p5) ∧ p1) → ((p3 ∧ p5) ∧ (p2 → (False → (p1 → False))))) ∧ p3) ∧ ((True ∨ p5) → p3)) → ((p4 ∧ False) ∧ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_624887966681214492045656724207 : ((((p5 ∨ (((p5 ∨ p4) ∧ (((p3 → p3) → False) ∧ p1)) → ((((((p3 ∧ p5) → (True → False)) → False) ∧ p5) ∨ False) ∨ p5))) ∨ p1) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h3.left
    let h6 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h3.left
    let h9 := h3.right
    -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
    have h10 : (p3 → p3) := by
      -- Implications on the right can always be decomposed.
      intro h11
      -- One of the premise coincides with the conclusion.
      exact h11
    -- We have shown the premise of h8, we can now drive its conclusion.
    let h12 := h8 h10
    -- False on the left can always be used.
    apply False.elim h12
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_261103215360633160345603907353 : ((p4 → p3) → ((p1 ∨ (True ∧ p4)) → (p1 ∨ ((p3 ∧ ((p4 ∨ ((p3 ∨ True) → p4)) → (p3 → (p4 ∧ False)))) → ((p3 ∨ p1) ∧ p1))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h8
    -- Conjunctions on the left can always be decomposed.
    let h10 := h7.left
    let h11 := h7.right
    -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
    have h12 : (p4 ∨ ((p3 ∨ True) → p4)) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h6
    -- We have shown the premise of h11, we can now drive its conclusion.
    let h13 := h11 h12
    -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
    have h14 : p3 := by
      -- One of the premise coincides with the conclusion.
      exact h10
    -- We have shown the premise of h13, we can now drive its conclusion.
    let h15 := h13 h14
    -- We need to get the right conjuct of h15 based on <expert-advice>.
    let h16 := h15.right
    -- False on the left can always be used.
    apply False.elim h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_656384547380851333023639875530 : (((((p2 → (((p5 ∧ (p2 → ((p4 ∧ False) ∧ p5))) ∧ p5) ∨ p3)) → ((((False ∨ True) ∧ False) ∨ (p2 ∨ p2)) ∨ False)) ∨ (p3 → True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50241006100737488756928326721 : (((((((((((p3 ∧ p1) → False) ∧ p2) ∧ (p3 ∧ True)) → p4) ∨ p3) ∨ p1) ∨ (p2 ∧ p5)) → p2) ∨ ((True ∨ True) ∨ (True ∧ p3))) ∨ False) := by
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
theorem thm_5_vars_624513813962132048284118942293 : ((((p4 ∨ ((p3 ∨ ((p2 → ((False → ((((p3 → p5) → p2) ∧ (p3 → p1)) ∨ p3)) → p3)) ∨ ((p3 → p3) ∨ True))) ∨ p2)) ∨ p4) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342378120494142476681209539140 : (p2 → ((((False ∨ p3) ∧ (p3 ∨ (((p2 ∨ p3) → ((p5 ∧ p1) ∨ p4)) ∧ True))) ∧ True) ∨ (p2 ∧ (p5 → (p1 ∨ (p2 → (p4 → p5))))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h4
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179138668916977541817317817811 : ((p1 ∧ (p3 ∧ (((p4 ∧ p3) ∨ ((True → p1) ∨ p4)) → (p4 → p4)))) ∨ (((((False ∧ (p5 ∨ (False → False))) ∧ p1) → p3) → p4) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_613840483426681063158175117212 : ((((((((p5 ∨ (True ∧ p4)) → (True → (False ∨ p1))) ∧ ((p4 ∨ p5) ∨ (p4 → (p5 ∨ p1)))) ∧ p2) ∨ ((True ∨ p3) ∧ True)) ∨ p4) ∨ p3) ∧ True) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61215435658966232836556717437 : ((False ∧ (True ∧ (((True ∧ p1) ∨ (p4 → True)) → ((p5 ∧ (((False ∨ p2) ∧ p1) ∧ (p3 ∧ True))) → (((p3 ∨ p3) ∧ p4) ∨ False))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_937848884860844834778317222197 : ((((False ∨ ((p1 ∨ (False ∨ True)) → False)) ∧ ((True ∧ ((p5 ∨ (p1 ∧ p4)) ∧ ((p5 → (False ∨ (p1 → p5))) ∧ (True ∧ p2)))) ∨ False)) → p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h11 =>
        -- Conjunctions on the left can always be decomposed.
        let h12 := h10.left
        let h13 := h10.right
        -- Conjunctions on the left can always be decomposed.
        let h14 := h13.left
        let h15 := h13.right
        -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
        have h16 : (p1 ∨ (False ∨ True)) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h5, we can now drive its conclusion.
        let h17 := h5 h16
        -- False on the left can always be used.
        apply False.elim h17
      case inr h18 =>
        -- Conjunctions on the left can always be decomposed.
        let h19 := h18.left
        let h20 := h18.right
        -- Conjunctions on the left can always be decomposed.
        let h21 := h10.left
        let h22 := h10.right
        -- Conjunctions on the left can always be decomposed.
        let h23 := h22.left
        let h24 := h22.right
        -- One of the premise coincides with the conclusion.
        exact h19
    case inr h25 =>
      -- False on the left can always be used.
      apply False.elim h25
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_650563998756779546170181703876 : ((((((((p4 ∨ (((True → False) → p5) ∧ p2)) → p3) ∧ True) → p5) → ((p1 ∧ p5) ∧ (((p1 ∧ p2) ∨ p1) ∨ True))) ∧ (p2 → True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166489732092021163106418369112 : ((p3 ∨ (((p4 ∨ p3) ∨ False) ∨ ((p3 → (p3 ∧ True)) → ((p5 ∧ (p3 ∨ p5)) ∧ False)))) ∨ (((((False ∧ p5) → False) ∧ True) ∨ False) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310564763782405199187447155945 : (p2 ∨ ((((p1 ∨ p3) ∨ True) ∨ p1) ∧ (p3 ∨ (p3 → (((((p1 ∧ False) ∨ p4) ∨ ((p4 ∧ False) ∧ p4)) ∧ p1) ∨ (p5 ∨ (False → p3))))))) := by
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
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177366767780339212176466047784 : ((p4 ∨ ((p1 ∨ (((True ∧ False) ∨ ((p4 ∧ p4) ∨ p5)) ∨ False)) ∨ True)) ∧ ((p5 ∧ (p1 → (p3 → (p3 ∧ p4)))) ∨ ((p5 ∧ p2) → p2))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_748515482626654396837016226981 : ((((p3 → True) → (((p4 ∨ ((p4 → (p2 ∧ (p1 ∨ (True ∨ False)))) → True)) → p3) ∨ ((p4 ∧ p4) → (True → (p1 → (p5 → p2)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113576284782550614006786225359 : (((False ∧ ((((p4 ∧ (p2 ∨ (True ∧ (p3 ∧ (p2 ∨ True))))) ∨ (((p5 ∨ True) → False) ∨ p3)) ∨ p4) ∧ True)) ∨ (True ∧ p4)) ∨ (True ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49289997839169350550147033852 : (((p5 ∧ (p1 ∧ (((True ∧ p4) → p3) ∧ ((((((p1 ∨ p3) ∨ p3) → p4) ∧ True) ∨ (p1 ∧ False)) ∨ p3)))) ∨ ((p2 ∧ p4) → p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135075880701697396023992815776 : (((((True → (p3 → (p3 → (False ∨ p2)))) ∨ ((p4 ∧ ((p5 → p4) ∨ p4)) → p2)) → (p1 ∧ p4)) ∨ (False → p4)) ∨ ((p2 ∧ True) ∧ p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39733727440161935927241474756 : (((p5 ∨ ((p5 ∨ p4) ∨ (((p4 ∧ (p2 ∨ (p2 → p3))) → p5) ∨ (p4 → (p3 ∧ ((p5 → (p1 → (p4 ∨ p3))) → p5)))))) ∧ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113467462413383132098168165649 : ((((p3 ∧ ((((((True → (p3 ∧ (p4 → (p2 → p4)))) ∧ p5) ∧ p4) ∧ (p2 ∧ p4)) → p3) ∧ p1)) → p5) ∨ (True ∧ p1)) ∨ (True ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345446710773267580327051341878 : (p3 → (((((((p3 ∧ p2) → False) ∧ True) ∧ p1) → ((True → (((False → p2) ∧ (p2 → (p4 → False))) ∧ p2)) → False)) ∨ (False ∧ p2)) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h8 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h9 := h3 h8
  -- We need to get the right conjuct of h9 based on <expert-advice>.
  let h10 := h9.right
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h11 : (p3 ∧ p2) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h1
    -- One of the premise coincides with the conclusion.
    exact h10
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h12 := h6 h11
  -- False on the left can always be used.
  apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_201201085728890300385947068937 : ((p1 → (False → (((True ∧ True) → True) ∧ p2))) → (p5 → ((p3 → ((((p4 → p3) ∨ p3) → True) → (p2 ∨ True))) → ((p2 ∧ p3) ∨ True)))) := by
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
theorem thm_5_vars_691055321257773388064812777561 : (((((True ∧ (p3 ∨ ((p5 → (p3 → False)) → (p2 → False)))) ∨ ((p3 ∧ p2) → False)) → (p2 ∨ (p4 ∨ (True ∨ ((True ∧ p2) → True))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197681595570705879985178980933 : (((p3 ∧ (p4 → (True ∧ p2))) → (False ∨ p1)) ∨ ((p2 ∧ p5) ∨ ((p5 ∧ (p4 → (True → (p4 ∨ p5)))) ∨ (True ∨ ((p5 ∨ p1) ∧ p2))))) := by
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
theorem thm_5_vars_622798377834789450600762036294 : ((((p4 ∧ (p2 → (((p2 ∧ p4) ∧ ((((False ∨ p4) ∨ ((False ∧ (p1 ∨ (p2 ∨ p2))) → p3)) ∧ (p5 ∨ p1)) ∨ p4)) ∨ p5))) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113254597266810814046715098291 : (((((True ∨ ((((p3 → ((False ∨ p4) ∧ (True ∧ p4))) ∨ p2) ∨ p3) ∨ (p2 → p4))) ∨ p2) → (p4 → False)) ∧ (True → p5)) ∨ (False → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305781418897113085408112939623 : (p1 ∨ ((p4 ∧ ((False → p2) ∧ ((False → p2) ∧ p3))) ∨ (((True ∧ (p3 ∧ p3)) ∨ ((p2 → (((p4 ∧ p3) ∧ p5) ∨ p2)) ∧ p5)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



