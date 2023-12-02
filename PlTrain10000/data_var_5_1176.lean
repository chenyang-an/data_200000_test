variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217103291346560740787414842399 : ((((p5 ∧ p2) ∨ p2) ∨ p3) → (p5 → ((True ∨ p3) → (((((((True ∨ True) → p4) ∧ False) → (p2 ∧ p4)) → p2) ∨ p3) ∨ (True ∨ p4))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Conjunctions on the left can always be decomposed.
        let h7 := h6.left
        let h8 := h6.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h10 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h10
  case inr h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h12 =>
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- Conjunctions on the left can always be decomposed.
        let h14 := h13.left
        let h15 := h13.right
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h11
      case inr h16 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h11
    case inr h17 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51167111659682792328950497998 : ((((p1 → (((((p4 ∨ False) → p2) ∧ p3) ∨ (False → p2)) → (True → p5))) ∧ (p5 → True)) ∨ ((p2 → (p2 → (True → p3))) ∨ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_175263958906941609934131607110 : ((p2 ∨ (((p2 ∧ p1) ∨ p1) ∨ (((p2 → p4) ∧ (True ∧ p5)) ∨ (p1 ∨ p4)))) → (((False → p4) ∧ ((p5 ∨ p2) ∧ (p2 → True))) ∨ True)) := by
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
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Conjunctions on the left can always be decomposed.
        let h11 := h10.left
        let h12 := h10.right
        -- Conjunctions on the left can always be decomposed.
        let h13 := h12.left
        let h14 := h12.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h15 =>
        -- Disjunctions on the left can always be decomposed.
        cases h15
        case inl h16 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h17 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_262098976002032217272153195875 : (True ∧ ((((((p4 ∨ False) ∨ p2) ∨ ((True → p4) ∨ (p5 ∨ (True ∨ ((p5 ∧ ((p2 ∧ p4) ∧ p5)) ∧ (False → False)))))) ∧ p1) ∧ True) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148803546845386003999971936238 : ((((True → (p4 ∧ (p5 → p5))) ∨ p3) → (p1 ∨ (((False → True) → (p5 → p2)) → (False ∨ (False ∨ True))))) ∨ ((p4 ∨ p1) → (p4 ∨ p5))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206260058135376157503737936830 : ((False ∨ ((p5 → (p5 → p3)) → p5)) ∨ ((p4 ∧ (((False → p2) ∧ ((True ∨ p5) ∨ False)) ∨ p2)) ∨ ((p4 → p4) ∨ (p2 ∨ (p1 → p4))))) := by
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
theorem thm_5_vars_157903735093061604379428981095 : ((((p3 ∨ ((p3 ∧ ((p4 ∨ p1) ∨ p2)) ∧ p2)) → p1) → ((p4 ∨ p1) → (p5 ∨ (p5 ∧ p3)))) ∨ (p5 → ((True ∨ p2) ∧ (p2 ∨ p5)))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_224549320980308687985465723734 : ((p2 → (p1 ∨ True)) ∧ ((((p3 ∨ p2) ∧ ((p3 → p3) ∧ (False ∨ p1))) ∧ p3) ∨ (p3 → (p3 ∨ ((p3 → (False ∧ p3)) ∨ (True ∧ False)))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317638607888779336605378826558 : (p4 ∨ ((((True → p2) ∧ (((p4 ∧ p5) → (p2 ∨ ((p3 → p1) ∧ False))) ∨ (p1 ∨ (False ∨ ((p1 ∧ True) → (p2 → False)))))) ∨ True) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67577445053138894217054931136 : ((p1 → ((p5 → p2) ∨ ((True ∨ (((p2 ∧ (p3 ∧ ((p4 ∨ (p5 ∨ False)) ∧ p5))) ∨ (False ∨ p3)) ∧ p2)) → (p5 ∧ (p2 ∨ p5))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150192696270339396884009871693 : ((p2 → ((((True ∧ p3) ∧ p5) ∧ ((p5 ∨ p5) ∨ (False ∨ (p2 ∨ ((False ∧ (p5 ∨ True)) → p4))))) ∨ True)) ∨ ((p5 ∨ (p2 ∧ p1)) → p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157154796791816346613243779139 : ((((((True → p4) ∨ p1) ∨ ((True ∧ (p2 ∧ ((p5 ∨ p4) → p2))) ∨ (p5 → p2))) ∨ p3) → False) ∨ (((p1 → False) → False) → (False → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206379532314801770622822850215 : ((p2 ∨ (p3 → (p2 ∨ (p2 ∨ p5)))) ∨ (((p2 ∨ (p2 ∨ ((False → ((True ∨ p2) ∧ p2)) ∧ False))) ∨ ((p1 → p4) ∨ (True → True))) ∧ True)) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_124503229400480073901973375741 : ((((p5 → (p3 ∧ (p5 → p5))) → p4) ∧ ((p4 ∨ ((p3 → (True ∧ p2)) → ((p3 → False) ∨ True))) ∧ (False → (p5 ∨ p2)))) → (p2 ∨ True)) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_766479170191995306569323421852 : (((p4 ∧ (p2 ∧ (((p5 ∨ p4) ∧ (((((False → p4) ∧ True) ∨ (p3 → p1)) ∨ (p2 → False)) ∨ (p3 ∧ (True ∨ (False → p5))))) → p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246083939510009272514703090839 : ((p4 ∧ p1) ∨ ((p4 ∨ (((p2 ∨ (True ∧ p5)) ∧ True) → (p3 ∧ (((p2 → (p2 ∧ False)) ∧ (p3 ∨ (p1 ∧ p3))) ∨ p1)))) ∨ (True ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_618070589899640308255970048757 : ((((((p5 → False) ∧ (p1 → p2)) ∧ (((p3 → p3) → ((p2 → (p2 ∨ (((p4 ∨ p4) ∨ (p2 ∨ p3)) → True))) ∧ False)) ∨ True)) ∨ True) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_216685634341180999721974697660 : ((((p3 → p4) ∨ p4) ∧ True) → ((p2 → (True ∨ p3)) → (p2 → ((p1 → (True ∧ p5)) ∨ ((p4 ∨ ((p3 → p1) → (True → p1))) ∨ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245548454287194447837915836378 : ((p3 ∧ True) ∨ (((p1 ∨ (True ∧ (p4 ∨ ((p4 ∨ p1) ∧ True)))) → False) ∨ (p2 → (p1 → ((((p5 → True) ∨ True) → (p2 ∧ p4)) ∨ p1))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149443939166495967654635586878 : ((False ∧ (((((p3 ∧ ((False ∨ p5) → (False → p5))) ∨ (True → p2)) ∨ (p2 ∨ p5)) ∧ (p3 ∨ p3)) ∨ False)) ∨ ((p4 → p2) ∨ (True ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42272437403667922059526981441 : (((p1 ∧ ((p3 ∧ ((p1 → p2) → p5)) ∨ ((p2 ∨ (((p4 ∧ (p5 ∨ p2)) ∨ p2) ∧ (p3 ∨ (p2 ∨ (p2 ∧ p5))))) ∧ p5))) ∨ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198530771864387843205929753630 : ((False ∨ (((True ∨ p4) ∧ True) → (p3 ∨ p4))) ∨ ((True ∨ p3) ∧ ((p1 ∨ p4) ∨ (p4 ∨ (False → ((p3 ∧ ((p1 ∧ p5) ∨ True)) ∧ p4)))))) := by
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
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58652280720469224910801342810 : (((p1 → p2) ∧ (p3 → ((True ∨ ((((((p5 ∨ (False ∧ p3)) ∨ p5) ∨ True) ∧ (p5 ∧ p1)) → False) ∨ p2)) → ((p2 → p2) ∧ False)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_120121668319788045252887169093 : (((((p5 → p3) → p1) ∧ (p1 ∨ ((p2 ∧ (p1 ∧ ((True ∧ p2) ∨ (p3 → p5)))) ∨ ((p5 ∨ (False ∧ p3)) ∨ p5)))) ∧ p3) → (p1 ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- Conjunctions on the left can always be decomposed.
        let h14 := h13.left
        let h15 := h13.right
        -- One of the premise coincides with the conclusion.
        exact h11
      case inr h16 =>
        -- One of the premise coincides with the conclusion.
        exact h11
    case inr h17 =>
      -- Disjunctions on the left can always be decomposed.
      cases h17
      case inl h18 =>
        -- Disjunctions on the left can always be decomposed.
        cases h18
        case inl h19 =>
          -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
          have h20 : (p5 → p3) := by
            -- Implications on the right can always be decomposed.
            intro h21
            -- One of the premise coincides with the conclusion.
            exact h3
          -- We have shown the premise of h4, we can now drive its conclusion.
          let h22 := h4 h20
          -- One of the premise coincides with the conclusion.
          exact h22
        case inr h23 =>
          -- Conjunctions on the left can always be decomposed.
          let h24 := h23.left
          let h25 := h23.right
          -- False on the left can always be used.
          apply False.elim h24
      case inr h26 =>
        -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
        have h27 : (p5 → p3) := by
          -- Implications on the right can always be decomposed.
          intro h28
          -- One of the premise coincides with the conclusion.
          exact h3
        -- We have shown the premise of h4, we can now drive its conclusion.
        let h29 := h4 h27
        -- One of the premise coincides with the conclusion.
        exact h29
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157262021445245022620522613436 : (((((p5 → (p1 ∧ p1)) ∧ p5) → (p5 ∨ ((p4 → (p2 ∧ (p5 ∧ False))) → (p2 ∨ p2)))) → p5) ∨ ((p3 → (False ∧ p2)) → (False → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134714413793770721297740535774 : ((((p3 ∨ (p4 ∨ p2)) ∧ ((p1 ∨ ((p2 ∧ ((p5 ∧ True) ∧ p2)) ∨ ((True ∨ p1) ∨ (p1 → p3)))) ∧ p4)) → p2) ∨ (True ∨ (p5 ∧ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_671269784434242542862156266997 : ((((p5 ∨ ((p5 ∨ (p5 → (((p3 ∧ p3) → (p1 → True)) → (p4 ∧ ((p5 ∧ (p4 → False)) ∨ p4))))) ∧ p1)) ∨ (False ∨ (False ∧ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148930839953604852674829659438 : ((((p3 ∧ p3) → (True ∨ True)) → ((p4 → (p5 → p2)) ∨ (((p1 → p1) ∧ ((p1 ∨ p1) ∧ p4)) ∨ False))) ∨ (False ∨ (False ∨ (p4 → True)))) := by
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
theorem thm_5_vars_213090877019611202486612732569 : ((((p5 ∧ p1) ∧ False) ∧ p5) ∨ ((p5 → True) → ((((p2 → p5) → (((p3 ∨ ((p1 → p4) → False)) ∨ True) ∧ True)) ∨ p5) ∨ (p5 → False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_558997184064062388254131305763 : (((p4 ∨ ((p4 ∧ (((False ∨ ((p2 → p4) ∨ p5)) ∨ ((p5 ∨ p1) ∨ True)) ∧ ((p2 ∧ ((p1 ∨ (False → p2)) ∧ p1)) ∨ False))) ∨ True)) ∧ True) ∧ True) := by
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
theorem thm_5_vars_59023711325103726429989381495 : (((p4 ∧ True) ∨ (((((p5 ∧ (p4 ∨ (((p4 → False) → (p1 → p2)) ∨ p5))) ∧ (((False ∨ p2) ∧ p4) ∧ p4)) → True) → False) ∧ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_677463503146463072810374719066 : ((((((p4 ∨ ((p5 → (True → ((p1 ∨ p5) → p2))) → False)) → (p2 → ((True ∨ p4) → p1))) ∨ True) ∨ (p2 ∨ (p5 → (False → p3)))) ∨ False) ∧ True) := by
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
theorem thm_5_vars_321235761705834089805867407824 : (p4 ∨ (p4 ∨ ((p3 → (p2 ∨ (p2 ∨ ((p2 ∨ ((False ∧ False) ∨ True)) ∨ (((((True ∧ (p5 → p2)) → p4) ∧ False) ∨ p1) ∧ p5))))) ∨ p4))) := by
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
theorem thm_5_vars_183845927973455628956486467943 : (((((p4 ∧ p5) ∧ ((p4 ∧ p5) ∧ p1)) ∨ (p4 ∨ True)) ∧ True) ∨ ((True ∧ (p4 ∨ True)) ∧ ((True ∧ True) ∧ ((p5 → False) → (p4 ∧ p4))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184172823928190841311754111520 : (((p1 → (((True ∧ (p2 ∧ (p3 → True))) → p1) → p2)) ∨ p1) ∨ ((p2 ∧ ((((p1 ∧ p4) ∨ p5) ∨ ((p4 ∨ p4) ∧ p4)) → p4)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187021914675621628725841172140 : (((p2 ∨ (False → True)) → ((((p4 ∨ p3) → p2) → p2) → False)) → (((p5 ∨ p2) ∧ ((p2 → False) → (p2 ∧ ((p2 ∧ False) ∨ False)))) → False)) := by
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
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h6 : (p2 → False) := by
      -- Implications on the right can always be decomposed.
      intro h7
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h8 : (p2 ∨ (False → True)) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h7
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h9 := h1 h8
      -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
      have h10 : (((p4 ∨ p3) → p2) → p2) := by
        -- Implications on the right can always be decomposed.
        intro h11
        -- One of the premise coincides with the conclusion.
        exact h7
      -- We have shown the premise of h9, we can now drive its conclusion.
      let h12 := h9 h10
      -- False on the left can always be used.
      apply False.elim h12
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h13 := h4 h6
    -- We need to get the right conjuct of h13 based on <expert-advice>.
    let h14 := h13.right
    -- Disjunctions on the left can always be decomposed.
    cases h14
    case inl h15 =>
      -- Conjunctions on the left can always be decomposed.
      let h16 := h15.left
      let h17 := h15.right
      -- False on the left can always be used.
      apply False.elim h17
    case inr h18 =>
      -- False on the left can always be used.
      apply False.elim h18
  case inr h19 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h20 : (p2 ∨ (False → True)) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h19
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h21 := h1 h20
    -- We want to use the implication h21 based on <expert-advice>. So we show its premise.
    have h22 : (((p4 ∨ p3) → p2) → p2) := by
      -- Implications on the right can always be decomposed.
      intro h23
      -- One of the premise coincides with the conclusion.
      exact h19
    -- We have shown the premise of h21, we can now drive its conclusion.
    let h24 := h21 h22
    -- False on the left can always be used.
    apply False.elim h24



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_752141076920233255983896341397 : (((True ∧ (p1 → (p4 → (p4 ∧ ((p2 ∨ ((p2 ∨ (((p1 → True) ∨ False) → p4)) ∨ (p3 ∨ (p1 ∧ p3)))) → ((p1 ∧ p5) ∨ p4)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246573812872821997224874192640 : ((p5 ∧ p2) ∨ ((((p2 ∧ False) → (False → p1)) ∨ ((((((p2 ∧ False) ∧ p5) → (p2 ∧ p2)) ∨ p2) → p3) ∨ p4)) → ((p3 ∨ True) ∨ p1))) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245839680696184902398031283019 : ((p3 ∧ p4) ∨ ((((((True ∧ ((p3 → p2) ∨ p3)) → p4) → (False ∨ ((p4 → p2) ∨ p5))) ∧ (p3 ∨ (p1 → p1))) ∧ p5) ∨ (False → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_175037972108729809175296879382 : ((p2 ∧ (((p2 → ((p4 ∧ (p3 → p5)) ∧ (p4 → False))) → (p2 → p4)) ∧ True)) → (((p1 ∨ True) → (p2 → (False ∧ p5))) → (True ∧ p3))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h7 : (p1 ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h8 := h2 h7
  -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
  have h9 : p2 := by
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h8, we can now drive its conclusion.
  let h10 := h8 h9
  -- We need to get the left conjuct of h10 based on <expert-advice>.
  let h11 := h10.left
  -- False on the left can always be used.
  apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150596385345972738227926271396 : ((((p4 → False) ∨ ((True ∧ (p1 ∨ ((p4 ∨ (False ∧ (p1 ∨ p4))) → (p1 → p2)))) ∨ (False ∧ p4))) ∧ p1) → ((False ∧ (p5 ∨ False)) ∨ p1)) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h3
      case inr h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h3
    case inr h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- False on the left can always be used.
      apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356066799852099735816797413403 : (p5 → (((p4 ∨ ((p3 → (p3 ∧ (((p2 ∧ p2) ∨ (p3 ∨ p3)) ∧ True))) ∧ ((False → p1) ∨ False))) → False) → (p4 ∧ ((False ∧ p2) ∨ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (p4 ∨ ((p3 → (p3 ∧ (((p2 ∧ p2) ∨ (p3 ∨ p3)) ∧ True))) ∧ ((False → p1) ∨ False))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h4
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- False on the left can always be used.
    apply False.elim h5
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h3
  -- False on the left can always be used.
  apply False.elim h6
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66785344236092209831367669761 : ((True → (False ∨ ((p4 ∧ (((p3 ∨ ((False → (p5 ∨ True)) → p3)) → ((p3 → (False → (False ∨ False))) → p5)) ∨ False)) ∨ (p4 → p4)))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_709731720824172511958143188846 : ((((False → (((True ∨ p3) ∨ (True → True)) ∧ p1)) → ((True ∧ p5) ∧ (((((p5 ∨ (False → p2)) → p2) ∧ (True ∧ p3)) ∧ p4) ∧ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43865392280018572279517510895 : (((((p5 → (((False ∧ p5) → True) ∨ p4)) ∧ (((p4 ∧ p4) ∨ ((p4 ∧ False) ∨ (p3 ∨ True))) → (p4 ∧ p3))) ∧ (p1 → p4)) → p3) ∨ p3) := by
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
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h6 : ((p4 ∧ p4) ∨ ((p4 ∧ False) ∨ (p3 ∨ True))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h7 := h5 h6
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_90059826348173013025261247913 : ((((False ∧ p5) → False) → (((((((p1 ∧ p4) ∧ (p2 ∧ (p2 ∧ (p4 ∧ p3)))) ∨ (p2 ∧ p1)) ∧ (p1 ∨ True)) ∨ False) → p5) ∧ p1)) → p1) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((False ∧ p5) → False) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- False on the left can always be used.
    apply False.elim h4
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h2
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113073003753142207221788438195 : (((p3 ∨ ((p3 → p2) ∨ (((p3 → (p1 ∧ p4)) → p5) ∧ (((p4 ∨ (p3 ∧ (p3 ∨ p4))) ∨ False) → (p4 ∨ p1))))) → False) ∨ (p2 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156670828535775825617144756907 : (((((((p1 → (p1 ∨ p1)) ∧ p2) → True) → (((p4 ∨ False) ∧ p5) → p1)) ∧ (p2 ∧ True)) ∧ p5) ∨ (False ∨ (p1 ∨ (False → (p5 ∧ p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_52854891235665306109671897436 : ((((p1 → True) → ((((p4 ∧ p2) ∧ True) ∨ (False ∨ True)) ∧ (p5 → p4))) → ((p2 ∧ p3) → (p5 ∧ ((True ∧ p4) → (p5 ∨ p4))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356761353011116398549403940185 : (p5 → ((((p3 → p1) ∨ (False ∨ p1)) → p3) → ((p3 ∧ (p4 → p3)) ∨ (p1 → ((((True → ((p2 ∧ p3) ∧ p4)) ∨ True) ∧ p4) → p3))))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h7 =>
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h8 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h9 := h7 h8
    -- We need to get the left conjuct of h9 based on <expert-advice>.
    let h10 := h9.left
    -- We need to get the right conjuct of h10 based on <expert-advice>.
    let h11 := h10.right
    -- One of the premise coincides with the conclusion.
    exact h11
  case inr h12 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h13 : ((p3 → p1) ∨ (False ∨ p1)) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h14
      -- One of the premise coincides with the conclusion.
      exact h3
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h15 := h2 h13
    -- One of the premise coincides with the conclusion.
    exact h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215257866022368654963585531039 : ((False ∧ (p4 ∧ (False ∧ p4))) ∨ ((p5 ∨ p3) ∨ ((p1 ∧ (True ∧ ((((False ∧ ((p1 ∨ False) ∧ p1)) ∧ p3) ∧ False) → (False ∨ p5)))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328811730642355912436905593700 : (True → ((((p4 ∧ p3) → (((p4 → p3) ∧ p5) ∨ True)) ∧ p4) → (p2 ∨ (((((p2 ∨ p2) → p3) ∨ p4) ∧ (p2 → True)) ∨ (True ∨ p1))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41520282048477886959197233215 : ((((((p3 ∨ p5) → p4) ∧ (((p1 ∨ False) → False) → p2)) ∧ ((((True ∨ p2) → (p5 ∨ (p3 ∨ p4))) ∨ False) → (p4 → False))) ∨ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149221180797106327300576468191 : (((p2 ∧ p4) ∨ (((False ∧ p2) ∧ (p2 ∨ (((((p5 ∧ (p2 ∧ p2)) ∨ True) ∨ p1) ∧ p2) ∨ p1))) ∨ True)) ∨ (p1 → (False ∨ (True → p5)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119565071999893970334440032092 : ((p5 → (((True ∨ False) ∧ (True ∨ (p4 → (False ∨ (p1 → p3))))) → (((p1 → (p3 ∨ p5)) ∨ (p2 ∨ (p2 → False))) ∧ p2))) ∨ (p3 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187073479878284318966140099581 : (((p4 ∨ p4) ∧ (((p3 → True) ∨ (p2 ∨ p1)) → (False ∧ p2))) → ((False ∨ ((False ∧ p4) ∨ (False ∨ (p4 ∧ False)))) ∨ (True ∨ (p2 → p2)))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354911893903432636795438917377 : (p5 → ((False ∨ ((((((((((p1 ∨ p1) → p2) ∨ p2) ∨ (p3 ∨ p2)) → p4) ∨ p3) ∨ p3) ∧ p3) → p5) → ((p1 → p5) → p2))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_24994396515563678232047600470 : (((p3 ∧ (p3 ∨ True)) ∨ ((((p2 → p3) ∧ p2) ∧ (True → ((p3 → (p1 → p4)) ∨ (True ∨ ((p1 ∨ False) → (p1 → p3)))))) → p3)) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h6 : p2 := by
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h7 := h4 h6
  -- One of the premise coincides with the conclusion.
  exact h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157247891480168198051768372247 : ((((True ∨ ((p5 ∧ (p4 → p2)) ∧ p4)) ∧ (p2 ∧ (p1 → (p4 → ((False ∧ False) → p5))))) → p4) ∨ ((p1 ∨ ((p1 → p1) ∧ p4)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48634941169986222197074903786 : ((((True → (((p1 → p2) → ((False ∨ p2) ∧ p3)) ∧ (((p5 ∨ p2) ∧ False) ∨ p4))) ∨ (p3 ∧ (p3 → p4))) ∧ ((False → p1) ∨ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68552072631280202750440029641 : ((p3 → (p5 → ((((p4 → p2) → ((p1 ∨ ((False → (True ∨ p1)) ∨ True)) ∨ ((p3 ∧ p1) → (p5 → (p5 ∧ p4))))) → False) ∨ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_754854661485846541344997846196 : (((False ∧ (p2 ∨ (((p1 ∨ p1) ∧ (((p2 → (((p1 → p5) ∨ (p4 ∧ True)) ∧ False)) → (p3 ∧ (True → True))) ∧ True)) ∨ (p3 ∨ p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178770219936968759882738710908 : (((False ∧ (p3 ∨ False)) ∧ ((False ∨ (p2 ∧ False)) ∨ (True ∨ (p3 ∨ p3)))) ∨ ((((p5 ∨ ((True ∨ False) ∧ p1)) ∧ (p5 ∧ p1)) ∧ p5) → p5)) := by
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
  cases h4
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h5.left
      let h14 := h5.right
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h15 =>
      -- False on the left can always be used.
      apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_780281371005190817432798188368 : (((p2 ∨ (((p4 ∨ ((False ∧ (True ∧ ((p2 ∨ ((False ∧ p3) ∨ p4)) → True))) ∨ p3)) → (p2 ∨ p2)) ∧ (p3 ∨ ((p4 → p1) → p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114405256808910836667373703767 : (((((p4 ∧ (p3 ∨ False)) ∨ (True ∨ p3)) → (((p1 ∧ ((p1 ∨ True) ∧ p2)) → p3) → p5)) ∨ ((p5 ∨ p2) ∧ (True ∧ p4))) ∨ (p1 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_594074724476649191658646899856 : (((((((p1 → (False → (False → (p4 ∧ True)))) ∨ ((p4 ∧ p1) ∧ (p3 → (False ∧ p3)))) ∨ p2) → (p3 → (True ∧ (p4 ∨ p4)))) ∧ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112271464373049071133976826720 : (((p5 ∨ (p3 → (((((p2 ∨ p3) → (False ∧ False)) ∧ ((p3 ∧ ((p4 → p1) ∨ (p1 ∧ p3))) ∨ p3)) ∧ p1) ∨ p5))) ∨ p5) ∨ (False → False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135941418108321533002468521481 : ((((((p3 ∨ (p1 ∧ p4)) → p4) ∨ (p3 → p2)) → True) ∧ (((p2 → (p5 ∧ p4)) → ((p4 ∧ p3) ∨ p1)) → False)) ∨ ((p2 → p3) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321040983449289167198518856019 : (p4 ∨ (False ∨ (p4 → (((((p5 ∨ p1) ∧ (((p4 ∨ ((p1 → True) ∧ p2)) ∧ p4) → (p5 → True))) ∧ p2) ∨ ((p4 ∨ True) ∧ True)) ∨ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_927963395717599455702204131863 : (((((p4 → (p3 → (True ∨ p4))) → ((p3 ∧ True) ∧ p5)) ∧ ((((p2 ∨ p5) → p2) ∧ (((p1 → p5) ∨ p5) ∧ (True → p2))) ∨ True)) → p3) ∧ True) := by
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
    let h7 := h6.left
    let h8 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h9 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h10 : (p4 → (p3 → (True ∨ p4))) := by
        -- Implications on the right can always be decomposed.
        intro h11
        -- Implications on the right can always be decomposed.
        intro h12
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h13 := h2 h10
      -- We need to get the left conjuct of h13 based on <expert-advice>.
      let h14 := h13.left
      -- We need to get the left conjuct of h14 based on <expert-advice>.
      let h15 := h14.left
      -- One of the premise coincides with the conclusion.
      exact h15
    case inr h16 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h17 : (p4 → (p3 → (True ∨ p4))) := by
        -- Implications on the right can always be decomposed.
        intro h18
        -- Implications on the right can always be decomposed.
        intro h19
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h20 := h2 h17
      -- We need to get the left conjuct of h20 based on <expert-advice>.
      let h21 := h20.left
      -- We need to get the left conjuct of h21 based on <expert-advice>.
      let h22 := h21.left
      -- One of the premise coincides with the conclusion.
      exact h22
  case inr h23 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h24 : (p4 → (p3 → (True ∨ p4))) := by
      -- Implications on the right can always be decomposed.
      intro h25
      -- Implications on the right can always be decomposed.
      intro h26
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h27 := h2 h24
    -- We need to get the left conjuct of h27 based on <expert-advice>.
    let h28 := h27.left
    -- We need to get the left conjuct of h28 based on <expert-advice>.
    let h29 := h28.left
    -- One of the premise coincides with the conclusion.
    exact h29
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_320366561347586401579280645327 : (p4 ∨ ((p3 → p5) ∨ (p3 → (((True → (True → (True → p5))) → False) ∨ ((((p1 ∧ p2) ∧ p1) ∨ ((p4 ∧ p1) ∨ (p3 ∨ p1))) ∨ p2))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337561881343305265237020583849 : (p1 → ((((((True ∨ (((True ∧ (p5 ∨ p2)) ∨ (p2 → (p4 ∧ p4))) ∧ False)) ∨ p4) → False) ∧ p4) ∧ p4) → (p2 ∨ (p5 ∧ (p4 ∨ p2))))) := by
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
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h7 : ((True ∨ (((True ∧ (p5 ∨ p2)) ∨ (p2 → (p4 ∧ p4))) ∧ False)) ∨ p4) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h8 := h5 h7
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190611396906182468453144978313 : ((((p5 → p3) → ((p4 → p5) ∨ (p2 ∨ p3))) → False) ∨ (False → (((False ∨ (((p2 ∧ (p4 → True)) ∨ p3) ∨ p4)) ∨ True) ∧ (p5 ∧ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138341873432798108610106659990 : ((p4 → ((False ∧ (((p2 → p3) → (p4 → (((p3 ∨ p2) ∨ p3) ∨ p3))) → ((False ∧ p1) ∧ (p1 → p4)))) ∧ p4)) ∨ (False → (p1 ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351753967962756412933023190471 : (p4 → (((((p2 → p2) ∧ ((((p3 → p5) ∨ True) ∧ p5) → True)) → False) → p4) → ((p5 ∨ True) ∨ (p5 ∨ ((p4 ∨ p5) ∨ (p2 ∨ p4)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61268066100098672836207853821 : ((False ∧ (p1 ∨ (p2 → ((((True → p3) → ((((((p2 ∨ True) → p5) ∨ p5) ∧ (True ∨ (False → p5))) ∧ True) → False)) → True) → p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64183117374947334007736242190 : ((False ∨ ((p3 ∨ p5) → ((p3 ∨ (p3 ∨ (p4 ∨ p5))) ∧ ((p3 → (False ∨ ((False → ((p2 ∧ p2) ∧ p2)) ∧ p3))) ∨ (p3 ∧ True))))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h4
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h6
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h7
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- False on the left can always be used.
    apply False.elim h7
    -- False on the left can always be used.
    apply False.elim h7
    -- False on the left can always be used.
    apply False.elim h7
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_102820388690970930212617587833 : ((((True → (p5 → (((False → (((p3 ∨ p2) → (p3 ∧ (p5 ∨ (p1 ∧ p4)))) → (p2 ∧ p4))) → p2) → p5))) → p4) ∨ True) ∧ (p2 ∨ True)) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52897841529733247337049080062 : (((p5 ∨ (True ∨ (p1 ∨ ((p3 → True) → (((p5 ∨ p1) ∧ False) ∧ True))))) → ((True → p2) ∧ (False ∧ ((p5 → True) ∧ (p5 → p1))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178293209882413613712536424487 : (((p3 ∨ (p4 ∨ (p3 → (p3 ∨ ((p1 → p5) → p3))))) ∧ (p5 ∨ p2)) ∨ ((p2 ∧ (p1 ∧ ((True → True) ∧ p4))) ∨ ((False ∨ p3) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228156155091044163191282173257 : ((p4 ∧ (p5 → p2)) ∨ ((p3 ∨ (((False ∨ (p4 ∨ (True ∧ p1))) ∧ p3) ∨ p2)) ∨ ((p4 → (True ∨ ((True → (p4 ∨ False)) ∨ p2))) ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112671591729098743128638505324 : ((((((p3 → p2) ∧ (((p5 ∧ p2) → ((p3 ∧ (p1 ∨ p3)) ∨ p4)) ∧ (False ∧ True))) ∧ p5) → (p4 → (p1 ∧ p4))) → p4) ∨ (False → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300725863877420936562778011821 : (False ∨ ((True ∧ (True ∨ (p2 → ((p4 ∧ p3) → ((p4 ∧ (True ∧ ((p3 → False) → True))) ∧ p5))))) → (p4 ∨ (True → (p2 ∨ (p2 ∨ True)))))) := by
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
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178849416170411863272296687127 : (((True ∧ (p2 ∨ p1)) → ((True ∧ (p5 ∧ ((p3 → p5) ∧ False))) ∨ p4)) ∨ (((p5 ∨ p2) ∧ p1) ∨ (False ∨ ((False ∧ p3) → (True ∧ p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307122802561025380573045331209 : (p1 ∨ (False ∨ ((p5 ∧ (p3 ∨ (p2 ∨ (((False ∨ ((p5 → (p1 → p3)) → p5)) ∨ ((p2 ∨ (p3 → p5)) ∧ p2)) → (False ∨ p3))))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198388049196050565867668132424 : ((p3 ∧ ((p3 → p1) → ((p2 → True) ∨ p4))) ∨ ((p4 ∧ (((((((p5 ∧ True) ∨ p1) ∧ True) → p2) ∧ (p3 → p4)) ∨ True) ∨ p5)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_718383170438938378854196003350 : ((((((p1 ∧ False) → p5) → p5) ∨ (True → (((p4 ∧ (False ∨ ((False → ((p5 ∧ (False → p1)) → p5)) ∧ p1))) ∧ (p1 ∨ p4)) ∧ True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190811246123934800291593545208 : ((((p3 → p1) → ((p3 ∨ False) ∧ p4)) ∨ (True ∧ p4)) ∨ (True ∨ (((False ∨ p5) ∧ p1) → (((p3 ∨ p2) ∧ p3) → ((True ∧ True) → True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_71295417015555268478217932781 : (((((p4 → p3) ∨ p2) → ((((p5 → (p3 ∨ False)) → (p2 ∧ (p1 ∨ ((True ∧ False) ∨ ((p4 ∨ p1) ∧ p2))))) ∧ False) ∧ p4)) ∧ p3) → p4) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : ((p4 → p3) ∨ p2) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h4
  -- We need to get the left conjuct of h6 based on <expert-advice>.
  let h7 := h6.left
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_348508273251373407479267984045 : (p3 → (p3 ∧ ((p2 ∨ ((((p2 ∨ p1) → p2) ∧ (p3 ∨ p5)) ∨ p4)) ∨ (p2 → (p1 → (p4 ∨ (p5 ∨ (True ∨ ((p1 → p1) ∨ False))))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_954112163863780280790425510404 : ((((p5 ∧ (p3 ∧ False)) ∨ ((True → ((p1 → p3) ∨ p2)) ∧ ((p1 ∨ (((p4 ∧ False) ∨ p4) ∨ (p5 → (p1 → p5)))) → (False ∧ False)))) → False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
    have h10 : (p1 ∨ (((p4 ∧ False) ∨ p4) ∨ (p5 → (p1 → p5)))) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h11
      -- Implications on the right can always be decomposed.
      intro h12
      -- One of the premise coincides with the conclusion.
      exact h11
    -- We have shown the premise of h9, we can now drive its conclusion.
    let h13 := h9 h10
    -- We need to get the left conjuct of h13 based on <expert-advice>.
    let h14 := h13.left
    -- False on the left can always be used.
    apply False.elim h14
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215462565136486319690632701751 : ((p3 ∧ (p1 ∨ (p1 ∧ True))) ∨ ((((True → ((p1 → False) ∧ (p4 → p3))) → p5) → (p1 ∨ (p3 ∧ ((p5 ∧ p1) ∨ p2)))) ∨ (p3 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_189718024447303090092514196372 : ((p4 ∨ ((((p2 ∧ (p3 ∨ p4)) ∧ False) → False) ∨ p4)) ∧ ((((p4 → p1) ∨ ((p3 ∧ True) → p2)) → p4) ∨ (False → ((True → p4) ∧ True)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  cases h5
  case inl h6 =>
    -- False on the left can always be used.
    apply False.elim h3
  case inr h7 =>
    -- False on the left can always be used.
    apply False.elim h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h8
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h9
  -- False on the left can always be used.
  apply False.elim h8
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354771415141745648782136312750 : (p5 → (((((((p3 → p5) ∨ p4) ∧ p5) ∨ p2) → (p4 ∨ p4)) ∧ ((False ∨ False) ∧ (((((p2 ∨ p1) ∧ False) ∨ p4) ∨ False) ∨ True))) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260207770250784934078714853724 : ((p2 → p2) → (p5 ∨ (((p2 ∧ (p3 ∧ (p5 → ((p4 ∨ (p5 ∨ (((p2 ∧ p4) → (p2 ∨ (p3 ∨ p3))) ∧ True))) → p3)))) ∧ p3) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257564938455632701023535924375 : ((p3 ∨ p1) → ((((p4 ∨ p1) ∧ (((p5 → True) → p3) ∨ p5)) ∨ (True ∧ (False → ((p5 ∨ p1) ∨ (True ∧ p3))))) ∨ (False → (True ∧ p2)))) := by
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
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300211960809873649676963033742 : (False ∨ ((((((p3 ∨ p2) ∧ p3) ∨ ((p4 ∨ (False ∨ p1)) ∧ (((p3 ∨ p5) → p3) ∨ True))) ∨ p5) ∨ ((p2 → p4) ∧ True)) → (False ∨ True))) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h4 =>
        -- Conjunctions on the left can always be decomposed.
        let h5 := h4.left
        let h6 := h4.right
        -- Disjunctions on the left can always be decomposed.
        cases h5
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
        -- Conjunctions on the left can always be decomposed.
        let h10 := h9.left
        let h11 := h9.right
        -- Disjunctions on the left can always be decomposed.
        cases h10
        case inl h12 =>
          -- Disjunctions on the left can always be decomposed.
          cases h11
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
          -- Disjunctions on the left can always be decomposed.
          cases h15
          case inl h16 =>
            -- False on the left can always be used.
            apply False.elim h16
          case inr h17 =>
            -- Disjunctions on the left can always be decomposed.
            cases h11
            case inl h18 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- True on the right can always be proven directly.
              apply True.intro
            case inr h19 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- True on the right can always be proven directly.
              apply True.intro
    case inr h20 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h21 =>
    -- Conjunctions on the left can always be decomposed.
    let h22 := h21.left
    let h23 := h21.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307378849641681938112443692192 : (p1 ∨ (p4 ∨ ((p1 → (((False ∨ (p4 ∧ (p1 ∨ ((False → (p4 ∧ p5)) → p3)))) ∨ (False ∧ True)) ∧ (False ∨ p5))) ∨ ((p2 ∧ p5) ∨ True)))) := by
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
theorem thm_5_vars_785463090414986138518647313827 : (((p4 ∨ (((p5 → (p4 ∨ ((False → False) ∨ p4))) → (((True ∧ (p4 ∧ p1)) → (False ∧ ((p4 → (False ∨ p5)) ∨ True))) ∨ p2)) ∨ True)) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_198245198457501734122523959565 : ((True ∧ (p2 ∨ ((False → (False ∧ p4)) ∧ False))) ∨ (p4 → (((p4 ∨ p1) ∧ (False ∨ (p5 ∧ p3))) → ((True → p3) → (p2 ∨ (p2 ∨ True)))))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- False on the left can always be used.
      apply False.elim h7
    case inr h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h12 =>
      -- False on the left can always be used.
      apply False.elim h12
    case inr h13 =>
      -- Conjunctions on the left can always be decomposed.
      let h14 := h13.left
      let h15 := h13.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



