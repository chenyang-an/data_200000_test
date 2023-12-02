variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149860954969341808670963772215 : ((p2 ∨ ((((p1 → p5) → (p5 ∨ (p2 ∨ p4))) ∨ (p3 → (True ∨ (p1 → (True → (p3 ∨ False)))))) ∧ True)) ∨ (p5 ∧ (False ∧ (p3 ∨ p4)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_723395146793703914972235612560 : (((((p1 ∧ p4) → p1) ∧ ((((False ∨ ((p2 ∧ p4) → p5)) → ((p2 ∨ p5) ∨ p5)) ∧ (False → (True → (p4 → True)))) ∨ (False ∨ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167377642759498384100341445609 : ((((p4 → (p3 → (p3 ∨ p3))) → ((p4 ∧ p4) ∧ (((p4 → True) → p1) ∨ p1))) → True) → ((p1 ∨ True) ∨ (((p4 → True) ∧ False) ∧ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_613229377235161024007634594441 : (((((((p5 → (p2 ∧ (True ∨ p2))) ∨ (p1 ∧ ((p1 → False) → p3))) ∨ ((False ∧ (p2 → False)) → (False ∨ p3))) → (p3 → p3)) ∨ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111655118200201841536281784406 : ((((True ∧ ((p5 ∧ ((((p2 → False) ∨ (p3 → False)) → (p5 ∨ ((p5 ∧ True) ∧ (p1 ∧ False)))) → p1)) ∨ p3)) ∨ p5) ∨ True) ∨ (False ∧ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55110504799196634745994972523 : (((((p5 ∨ (p1 ∨ p1)) ∧ p4) ∧ p2) ∨ (((p1 → (p4 ∨ (p1 ∧ ((p3 ∨ (p4 → (p3 ∨ p4))) ∨ p1)))) ∨ True) ∧ (p1 ∧ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_327165174058786364704058033357 : (True → ((p5 ∧ (p4 ∨ (p4 ∨ (p3 → ((p5 ∧ (p1 → (p5 → (((False ∧ ((False → (p3 ∨ False)) ∨ p1)) ∨ p2) → True)))) ∨ p1))))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135956544299448606664805144378 : ((((p4 → False) ∨ (((p3 → (p2 ∨ p2)) ∨ p4) ∧ p5)) ∧ (((p4 ∨ ((False ∧ p2) ∧ True)) → (p1 ∧ p2)) → p2)) ∨ ((False → False) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_120782797844500335837597975962 : ((((True → ((((p1 → p1) ∧ (False → (p1 ∨ True))) → (True ∧ (p3 ∧ p5))) ∨ (p5 → p5))) → (False ∧ (p4 → p1))) ∨ False) → (p3 → p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h4 =>
    -- False on the left can always be used.
    apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48997346120936592426200009495 : ((((p3 ∨ ((((((True ∨ True) → p3) ∨ ((False → p2) → True)) ∧ (False ∧ p5)) ∨ p2) ∨ (p2 ∨ p3))) ∨ p4) ∨ (False → (p1 → False))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150652148675597432441705463060 : (((p2 ∨ (((p3 ∧ (((p3 → p1) ∧ False) ∨ p1)) ∨ (p1 ∧ ((p3 ∧ p5) → False))) ∨ (True → False))) ∧ True) → ((True → (False ∧ p5)) → p3)) := by
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
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h6 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h7 := h2 h6
    -- We need to get the left conjuct of h7 based on <expert-advice>.
    let h8 := h7.left
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- Conjunctions on the left can always be decomposed.
        let h12 := h11.left
        let h13 := h11.right
        -- Disjunctions on the left can always be decomposed.
        cases h13
        case inl h14 =>
          -- Conjunctions on the left can always be decomposed.
          let h15 := h14.left
          let h16 := h14.right
          -- False on the left can always be used.
          apply False.elim h16
        case inr h17 =>
          -- One of the premise coincides with the conclusion.
          exact h12
      case inr h18 =>
        -- Conjunctions on the left can always be decomposed.
        let h19 := h18.left
        let h20 := h18.right
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h21 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h22 := h2 h21
        -- We need to get the left conjuct of h22 based on <expert-advice>.
        let h23 := h22.left
        -- False on the left can always be used.
        apply False.elim h23
    case inr h24 =>
      -- We want to use the implication h24 based on <expert-advice>. So we show its premise.
      have h25 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h24, we can now drive its conclusion.
      let h26 := h24 h25
      -- False on the left can always be used.
      apply False.elim h26



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134633379639456520570548866916 : ((((((p1 ∨ (p2 ∧ (p5 → p2))) ∧ True) ∨ ((p5 → (p3 ∧ p5)) ∨ p2)) ∨ (True ∨ (p1 ∧ (p3 ∧ p3)))) → p1) ∨ (True ∨ (p3 ∧ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137752949991137924783640000936 : ((p2 ∨ ((False ∧ ((True → ((p2 ∧ (p2 → False)) ∧ ((p2 ∧ p2) ∨ p5))) ∧ (p3 ∧ (p2 ∧ (False ∨ p2))))) ∨ p5)) ∨ (p2 ∨ (True ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190079742910979012310814953064 : ((((p2 → (((p5 ∧ p4) ∨ True) ∨ False)) → True) ∧ p1) ∨ ((p1 ∨ p3) ∨ ((p4 ∨ (p4 ∨ ((p4 ∧ (p4 → p2)) → (True ∧ True)))) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342658528553424350890090977645 : (p2 → (((((p3 → (p5 ∨ False)) ∧ p4) ∨ p5) ∧ (p1 → p3)) ∨ (((True → ((False → p2) ∧ p4)) → (p3 ∧ (False ∨ (p2 ∧ p4)))) → p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46756098252355745013905776821 : (((p2 → (((((False ∧ ((p1 → False) ∨ (p5 → (p5 ∧ (True → p1))))) ∨ p3) ∧ p2) ∨ (p1 ∨ (p3 ∨ False))) ∧ p4)) ∧ (True ∨ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60457417235650291522803115909 : (((p5 → p1) → (p4 → (p1 → (p1 → (True ∧ ((p2 ∧ True) ∨ ((((p1 ∧ p4) → False) ∧ (((p4 ∨ True) ∧ p1) ∧ p4)) ∨ p1))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156961121580303963589402473807 : (((((((p3 ∧ (p4 ∧ (p2 ∧ True))) ∧ p2) → (p1 ∧ p2)) → p3) → ((p4 ∧ p3) ∧ False)) ∨ True) ∨ ((p3 ∧ p3) ∨ (p2 → (p1 ∧ p5)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179055450523881365317857621040 : (((p5 → False) → ((((p5 → p2) ∨ (p2 ∨ (p3 ∧ p3))) ∧ p4) ∧ p3)) ∨ ((p5 ∧ (((p3 ∨ True) ∨ p3) → False)) → ((p1 ∨ p4) ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : ((p3 ∨ True) ∨ p3) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232332365657627858248467982158 : (((p4 → True) → False) → ((p4 ∨ (((p3 ∧ ((p1 ∨ (p1 ∧ p1)) ∧ (True ∨ p2))) ∨ p5) → ((p4 ∨ p1) ∨ (p2 ∧ p2)))) ∧ (p2 ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p4 → True) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- False on the left can always be used.
  apply False.elim h4
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h5 : (p4 → True) := by
    -- Implications on the right can always be decomposed.
    intro h6
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h7 := h1 h5
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118106913253915474795797432962 : ((False ∨ (((p5 → True) → (((((False ∨ p3) ∨ ((p3 ∨ p5) → (p5 ∧ p4))) ∧ p3) ∧ (p3 ∧ p2)) ∧ (p2 ∨ p3))) ∨ True)) ∨ (p2 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328728073685794377932807495160 : (True → ((((p2 ∨ (p5 ∧ False)) ∨ (((False ∧ p3) → p4) ∧ True)) → False) → ((p4 ∧ p2) ∧ (((p2 → (p5 ∨ p5)) ∧ False) ∨ (False → p1))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : ((p2 ∨ (p5 ∧ False)) ∨ (((False ∧ p3) → p4) ∧ True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- False on the left can always be used.
    apply False.elim h5
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h7 := h2 h3
  -- False on the left can always be used.
  apply False.elim h7
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h8 : ((p2 ∨ (p5 ∧ False)) ∨ (((False ∧ p3) → p4) ∧ True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h9
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- False on the left can always be used.
    apply False.elim h10
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h12 := h2 h8
  -- False on the left can always be used.
  apply False.elim h12
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h13
  -- False on the left can always be used.
  apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310074347832463138633045139135 : (p2 ∨ ((p1 ∨ (((p3 ∨ (p3 ∨ False)) ∧ ((p5 ∧ p3) → (True ∧ (True ∨ True)))) ∨ p5)) → ((p2 → p4) ∨ (((p2 ∨ p3) ∧ False) → p3)))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- False on the left can always be used.
      apply False.elim h5
    case inr h7 =>
      -- False on the left can always be used.
      apply False.elim h5
  case inr h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h13
        -- Conjunctions on the left can always be decomposed.
        let h14 := h13.left
        let h15 := h13.right
        -- Disjunctions on the left can always be decomposed.
        cases h14
        case inl h16 =>
          -- False on the left can always be used.
          apply False.elim h15
        case inr h17 =>
          -- False on the left can always be used.
          apply False.elim h15
      case inr h18 =>
        -- Disjunctions on the left can always be decomposed.
        cases h18
        case inl h19 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h20
          -- Conjunctions on the left can always be decomposed.
          let h21 := h20.left
          let h22 := h20.right
          -- Disjunctions on the left can always be decomposed.
          cases h21
          case inl h23 =>
            -- False on the left can always be used.
            apply False.elim h22
          case inr h24 =>
            -- False on the left can always be used.
            apply False.elim h22
        case inr h25 =>
          -- False on the left can always be used.
          apply False.elim h25
    case inr h26 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h27
      -- Conjunctions on the left can always be decomposed.
      let h28 := h27.left
      let h29 := h27.right
      -- Disjunctions on the left can always be decomposed.
      cases h28
      case inl h30 =>
        -- False on the left can always be used.
        apply False.elim h29
      case inr h31 =>
        -- False on the left can always be used.
        apply False.elim h29



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2500740415121530370074461471 : ((True ∨ ((p5 ∨ (p2 → ((p3 ∨ True) → p5))) → p3)) → ((p4 ∨ p1) → ((p4 → (p3 ∧ p1)) → ((p5 → (False ∧ p4)) → p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h6 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h7 : p4 := by
        -- One of the premise coincides with the conclusion.
        exact h5
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h8 := h3 h7
      -- We need to get the right conjuct of h8 based on <expert-advice>.
      let h9 := h8.right
      -- One of the premise coincides with the conclusion.
      exact h9
    case inr h10 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h11 : p4 := by
        -- One of the premise coincides with the conclusion.
        exact h5
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h12 := h3 h11
      -- We need to get the right conjuct of h12 based on <expert-advice>.
      let h13 := h12.right
      -- One of the premise coincides with the conclusion.
      exact h13
  case inr h14 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h15 =>
      -- One of the premise coincides with the conclusion.
      exact h14
    case inr h16 =>
      -- One of the premise coincides with the conclusion.
      exact h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_194233875709726778150117068750 : ((p4 → (((p1 ∧ (p4 ∨ p4)) ∧ (p5 ∨ p1)) → p4)) → (((True ∧ ((p5 ∨ p4) ∧ ((p5 ∧ (False ∨ p2)) → p5))) → (True → p3)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54494363691061668577742476608 : (((((p1 ∨ p1) ∧ p3) ∧ ((p5 → False) → True)) ∨ (p2 ∨ ((p1 ∨ (p4 → (((p4 → (True ∨ False)) → p1) ∨ p2))) ∨ (p5 → True)))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_113310451468121197979083513068 : (((((p4 ∧ (p3 ∨ False)) → p2) → (p1 ∧ (((p5 → False) → (p1 ∨ (((p1 ∧ True) → p2) → p5))) ∨ True))) ∧ (p3 → p1)) ∨ (p5 → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149168563396632520820538443897 : (((p4 ∨ p5) ∧ (((((False ∨ False) ∧ (p3 → (p3 ∧ p2))) ∧ False) ∧ (p2 ∨ p1)) ∧ ((p1 ∨ p1) ∨ True))) ∨ (True ∨ ((p3 ∨ p1) → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179772510836399372724978555106 : ((((p2 → (p1 → (p5 ∨ False))) ∧ (p1 → ((p3 ∨ p1) ∨ p3))) ∧ p3) → (p3 ∧ (p1 → ((p3 → (((p3 → p5) → False) ∧ p3)) ∨ p3)))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Implications on the right can always be decomposed.
  intro h6
  -- Conjunctions on the left can always be decomposed.
  let h7 := h1.left
  let h8 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h9 := h7.left
  let h10 := h7.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113702865937254664863276324091 : ((((p2 → (((((True ∧ True) ∨ p4) ∧ ((True ∨ p2) ∨ p4)) ∧ ((p1 ∧ p1) ∧ True)) → (p3 ∨ p1))) → False) → (False ∧ p3)) ∨ (p1 ∨ p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p2 → (((((True ∧ True) ∨ p4) ∧ ((True ∨ p2) ∨ p4)) ∧ ((p1 ∧ p1) ∧ True)) → (p3 ∨ p1))) := by
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
      let h10 := h9.left
      let h11 := h9.right
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h12 =>
        -- Disjunctions on the left can always be decomposed.
        cases h12
        case inl h13 =>
          -- Conjunctions on the left can always be decomposed.
          let h14 := h6.left
          let h15 := h6.right
          -- Conjunctions on the left can always be decomposed.
          let h16 := h14.left
          let h17 := h14.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h17
        case inr h18 =>
          -- Conjunctions on the left can always be decomposed.
          let h19 := h6.left
          let h20 := h6.right
          -- Conjunctions on the left can always be decomposed.
          let h21 := h19.left
          let h22 := h19.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h22
      case inr h23 =>
        -- Conjunctions on the left can always be decomposed.
        let h24 := h6.left
        let h25 := h6.right
        -- Conjunctions on the left can always be decomposed.
        let h26 := h24.left
        let h27 := h24.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h27
    case inr h28 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h29 =>
        -- Disjunctions on the left can always be decomposed.
        cases h29
        case inl h30 =>
          -- Conjunctions on the left can always be decomposed.
          let h31 := h6.left
          let h32 := h6.right
          -- Conjunctions on the left can always be decomposed.
          let h33 := h31.left
          let h34 := h31.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h34
        case inr h35 =>
          -- Conjunctions on the left can always be decomposed.
          let h36 := h6.left
          let h37 := h6.right
          -- Conjunctions on the left can always be decomposed.
          let h38 := h36.left
          let h39 := h36.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h39
      case inr h40 =>
        -- Conjunctions on the left can always be decomposed.
        let h41 := h6.left
        let h42 := h6.right
        -- Conjunctions on the left can always be decomposed.
        let h43 := h41.left
        let h44 := h41.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h44
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h45 := h1 h2
  -- False on the left can always be used.
  apply False.elim h45
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h46 : (p2 → (((((True ∧ True) ∨ p4) ∧ ((True ∨ p2) ∨ p4)) ∧ ((p1 ∧ p1) ∧ True)) → (p3 ∨ p1))) := by
    -- Implications on the right can always be decomposed.
    intro h47
    -- Implications on the right can always be decomposed.
    intro h48
    -- Conjunctions on the left can always be decomposed.
    let h49 := h48.left
    let h50 := h48.right
    -- Conjunctions on the left can always be decomposed.
    let h51 := h49.left
    let h52 := h49.right
    -- Disjunctions on the left can always be decomposed.
    cases h51
    case inl h53 =>
      -- Conjunctions on the left can always be decomposed.
      let h54 := h53.left
      let h55 := h53.right
      -- Disjunctions on the left can always be decomposed.
      cases h52
      case inl h56 =>
        -- Disjunctions on the left can always be decomposed.
        cases h56
        case inl h57 =>
          -- Conjunctions on the left can always be decomposed.
          let h58 := h50.left
          let h59 := h50.right
          -- Conjunctions on the left can always be decomposed.
          let h60 := h58.left
          let h61 := h58.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h61
        case inr h62 =>
          -- Conjunctions on the left can always be decomposed.
          let h63 := h50.left
          let h64 := h50.right
          -- Conjunctions on the left can always be decomposed.
          let h65 := h63.left
          let h66 := h63.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h66
      case inr h67 =>
        -- Conjunctions on the left can always be decomposed.
        let h68 := h50.left
        let h69 := h50.right
        -- Conjunctions on the left can always be decomposed.
        let h70 := h68.left
        let h71 := h68.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h71
    case inr h72 =>
      -- Disjunctions on the left can always be decomposed.
      cases h52
      case inl h73 =>
        -- Disjunctions on the left can always be decomposed.
        cases h73
        case inl h74 =>
          -- Conjunctions on the left can always be decomposed.
          let h75 := h50.left
          let h76 := h50.right
          -- Conjunctions on the left can always be decomposed.
          let h77 := h75.left
          let h78 := h75.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h78
        case inr h79 =>
          -- Conjunctions on the left can always be decomposed.
          let h80 := h50.left
          let h81 := h50.right
          -- Conjunctions on the left can always be decomposed.
          let h82 := h80.left
          let h83 := h80.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h83
      case inr h84 =>
        -- Conjunctions on the left can always be decomposed.
        let h85 := h50.left
        let h86 := h50.right
        -- Conjunctions on the left can always be decomposed.
        let h87 := h85.left
        let h88 := h85.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h88
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h89 := h1 h46
  -- False on the left can always be used.
  apply False.elim h89



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208796744478894378348571612310 : ((p2 ∧ (False → ((p1 → p2) → p2))) → (((p3 ∧ (((True ∨ p4) ∧ (((p1 → (p3 ∧ True)) ∨ False) → p4)) ∧ p5)) ∨ (True → p1)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_84175571291587569584188888024 : (((True → ((((p4 ∧ False) → p1) ∧ p1) ∧ ((p4 ∧ (p2 ∧ (p5 ∧ p3))) ∧ p3))) ∧ (((False → (p4 → p4)) ∧ p5) ∨ (True ∨ p1))) → p2) := by
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
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h7 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h8 := h2 h7
    -- We need to get the right conjuct of h8 based on <expert-advice>.
    let h9 := h8.right
    -- We need to get the left conjuct of h9 based on <expert-advice>.
    let h10 := h9.left
    -- We need to get the right conjuct of h10 based on <expert-advice>.
    let h11 := h10.right
    -- We need to get the left conjuct of h11 based on <expert-advice>.
    let h12 := h11.left
    -- One of the premise coincides with the conclusion.
    exact h12
  case inr h13 =>
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h14 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h15 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h16 := h2 h15
      -- We need to get the right conjuct of h16 based on <expert-advice>.
      let h17 := h16.right
      -- We need to get the left conjuct of h17 based on <expert-advice>.
      let h18 := h17.left
      -- We need to get the right conjuct of h18 based on <expert-advice>.
      let h19 := h18.right
      -- We need to get the left conjuct of h19 based on <expert-advice>.
      let h20 := h19.left
      -- One of the premise coincides with the conclusion.
      exact h20
    case inr h21 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h22 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h23 := h2 h22
      -- We need to get the right conjuct of h23 based on <expert-advice>.
      let h24 := h23.right
      -- We need to get the left conjuct of h24 based on <expert-advice>.
      let h25 := h24.left
      -- We need to get the right conjuct of h25 based on <expert-advice>.
      let h26 := h25.right
      -- We need to get the left conjuct of h26 based on <expert-advice>.
      let h27 := h26.left
      -- One of the premise coincides with the conclusion.
      exact h27



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_674040594912949081131865327868 : ((((p1 ∧ ((((p5 ∧ (p4 → p1)) ∧ ((((p5 ∨ p5) → p2) → (p5 → p4)) ∨ True)) → p5) ∨ (False ∨ p3))) → ((p1 ∧ p1) ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116937287121015903319391222383 : (((p1 ∧ p1) → ((((((p2 ∨ p4) ∧ p1) → True) → p5) → (((p2 → True) → p3) ∨ (p5 ∧ (p1 → (p4 ∧ p3))))) ∨ p3)) ∨ (True ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_352851512030905506434074990590 : (p4 → ((p4 → p5) → (p2 ∨ ((p1 ∨ ((p1 → (((p5 ∨ (p3 ∨ p4)) → (((p3 ∧ (p3 → p1)) → p3) ∧ False)) ∧ False)) → True)) → p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h5 : p4 := by
      -- One of the premise coincides with the conclusion.
      exact h1
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h6 := h2 h5
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h8 : p4 := by
      -- One of the premise coincides with the conclusion.
      exact h1
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h9 := h2 h8
    -- One of the premise coincides with the conclusion.
    exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_606002854434189497198844561582 : ((((p5 → ((p3 ∧ ((p4 ∧ p1) → p5)) → (((p4 ∨ (p5 → (((False ∨ p1) ∨ False) ∧ (True ∧ (True → p2))))) → p2) ∨ p2))) ∧ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48761713518636505538115949705 : ((((p1 ∧ p3) ∨ ((((p1 → p1) ∨ p5) → p3) → (((False ∧ p4) → False) → ((True → True) ∧ (p1 ∧ p1))))) ∧ (p4 → (False ∨ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64929308645642057661516359951 : ((p2 ∨ (((((False → ((p4 ∨ p5) → (p2 → p4))) ∧ True) ∧ p1) ∨ (p4 ∧ p5)) ∨ (True → ((False → True) ∧ ((True → False) ∨ False))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115624086898652611821609304627 : (((p5 → ((p5 ∨ p1) ∨ (p4 ∨ p4))) ∧ (((((((True ∨ p5) → ((p4 → False) ∧ False)) ∨ p1) → p4) ∨ p5) ∨ p5) → False)) ∨ (p4 → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204436355164776121530576271243 : (((((False ∧ p1) ∨ p4) ∧ False) ∨ p3) ∨ (p4 ∨ ((p2 ∨ (((p2 ∨ True) ∨ (True → (True ∨ p5))) ∧ ((False ∨ p4) ∧ p1))) ∨ (False → p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208305080253088548695537280098 : (((p5 ∨ False) ∧ (p5 → (p4 ∧ p3))) → (p1 → (((p2 → ((False ∨ True) ∧ p1)) ∨ p3) → (((p4 → (p1 ∨ p1)) → p2) ∨ (False ∨ p4))))) := by
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
    let h5 := h1.left
    let h6 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h8 : p5 := by
        -- One of the premise coincides with the conclusion.
        exact h7
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h9 := h6 h8
      -- We need to get the left conjuct of h9 based on <expert-advice>.
      let h10 := h9.left
      -- One of the premise coincides with the conclusion.
      exact h10
    case inr h11 =>
      -- False on the left can always be used.
      apply False.elim h11
  case inr h12 =>
    -- Conjunctions on the left can always be decomposed.
    let h13 := h1.left
    let h14 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h15 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
      have h16 : p5 := by
        -- One of the premise coincides with the conclusion.
        exact h15
      -- We have shown the premise of h14, we can now drive its conclusion.
      let h17 := h14 h16
      -- We need to get the left conjuct of h17 based on <expert-advice>.
      let h18 := h17.left
      -- One of the premise coincides with the conclusion.
      exact h18
    case inr h19 =>
      -- False on the left can always be used.
      apply False.elim h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52244360455257887047872551748 : (((p5 ∧ (p3 ∨ ((((p3 → p5) → p4) → p5) ∨ (((p2 ∨ p3) → p4) ∧ p3)))) → (p4 ∧ (True ∧ ((p3 → (p4 → p1)) ∨ p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47884837308786393029782733513 : (((((((p3 → p5) ∧ ((p4 → True) ∨ p4)) ∧ (((True ∧ p3) ∨ (False → (p5 ∨ p3))) → p4)) → p1) ∨ (True → p4)) → (p3 → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55480547902722768010005893261 : (((((p2 → p4) → p2) ∨ (p4 → True)) → (p5 ∧ ((p3 ∧ (p4 ∨ (p1 ∨ (((p2 → False) → p4) → (p1 → True))))) ∧ (p2 ∧ p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112329888726633464222067814182 : (((p4 → ((p3 ∧ (False → ((p2 ∨ p3) → (p3 ∨ (False → ((False ∨ (True → p4)) → (p4 → (p1 ∨ p5)))))))) → False)) ∨ True) ∨ (p2 ∧ p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114046908376726989631849703097 : ((((((p5 ∨ (True ∧ (False ∨ ((p3 ∨ p4) → p1)))) ∧ p4) → ((p4 → p5) → False)) → (p2 ∨ p2)) ∨ (True ∨ (p2 ∨ True))) ∨ (p1 ∧ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157070461161675150546210203980 : (((False ∨ (False ∧ (((((p1 → p5) ∨ (p2 → p5)) ∨ p4) ∧ ((p4 ∧ p2) ∧ p2)) ∨ p1))) ∨ True) ∨ (p1 ∧ ((p5 ∨ True) ∧ (True ∨ p4)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165854933791885959620093961682 : (((False ∧ (p5 → p4)) ∨ ((p5 → p1) ∧ ((p3 → ((True ∨ (False ∨ p1)) → p3)) → p5))) ∨ (((p3 → (p2 → (p3 ∧ True))) ∧ False) → p3)) := by
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
theorem thm_5_vars_44686079470744555465410780523 : ((((p1 ∨ (p3 ∨ (p1 ∧ (p2 ∧ p4)))) → (False → (p1 ∧ ((((False ∧ p4) ∨ p4) ∧ True) ∧ (((p5 → p1) → p5) ∧ p4))))) → p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181257412748204164070410114957 : ((p4 ∧ ((True ∨ (((p5 ∨ (p3 ∨ (p5 ∧ p5))) → True) ∧ p1)) ∨ p4)) → ((((p1 ∨ p2) ∧ (p4 ∧ p1)) ∨ p1) ∨ ((True ∨ p3) ∨ False))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h8
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111764634349777356412909386075 : (((((p5 ∧ (((p1 ∨ p1) ∨ (p4 → False)) → p4)) ∧ ((((p2 ∨ p4) → (False → False)) ∨ p2) → False)) ∧ (True ∨ p5)) ∨ p3) ∨ (p3 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51851931403734757665141619729 : ((((p3 ∧ (((((p1 → True) ∨ p1) → p2) ∧ p2) → (p4 ∨ (False ∨ p2)))) ∧ p3) ∨ (((p1 ∨ p5) ∧ ((p4 → p2) ∧ p2)) → p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206184952232137721247144655127 : ((p5 ∧ (p2 ∨ ((p4 ∨ p4) ∧ p1))) ∨ (p5 ∨ ((p2 ∧ (((p5 → (False → p2)) ∧ (False ∨ False)) ∧ True)) → (p3 ∨ ((False → p1) ∧ p1))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- False on the left can always be used.
    apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46930867254335333033288391428 : (((((p5 ∧ p4) → (((p5 ∧ ((p2 ∧ p4) → ((p3 → p1) → False))) ∧ (p4 ∧ ((p2 ∧ p4) ∧ p3))) ∧ True)) ∨ True) ∨ (p5 → False)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_357107330559196114342289617730 : (p5 → ((p1 ∨ (p1 ∧ p2)) → (((((p3 ∧ p3) ∨ (False ∨ (p5 → p1))) ∧ (p3 ∨ (((p4 ∨ p4) ∧ p3) ∧ p4))) ∧ (True ∧ p3)) ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_563512855843814074409946120820 : (((p5 ∨ ((p2 ∨ p3) ∨ ((p2 → (((True ∨ (False → (p3 ∨ p4))) ∧ False) ∨ p4)) → ((p1 ∨ (p2 ∨ (True → True))) ∨ (True → False))))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_623941674174968319638954484299 : ((((p2 ∨ ((((p4 ∨ (((p3 ∧ True) ∧ p5) ∧ False)) → ((((p2 ∨ (p4 → False)) → p3) ∨ (p2 → True)) → p3)) ∧ p5) ∨ p4)) ∨ True) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_201117654268285696505862506956 : ((True → (False ∧ ((p3 → (p2 ∨ p4)) → p4))) → (p4 ∧ (False ∨ (p3 → (p2 ∧ (False ∨ (((p5 ∨ (True → (True ∧ True))) → p5) ∨ p5))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h5 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h5
  -- We need to get the left conjuct of h6 based on <expert-advice>.
  let h7 := h6.left
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_702900722060509998359143480377 : (((((True → (p2 → (p2 → p1))) → (False ∧ (p3 → p4))) ∨ ((True ∨ (p1 ∨ False)) ∧ (((p5 → True) ∨ ((p2 ∨ False) → False)) ∨ False))) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_72992042523729012652676576993 : (((((((False ∨ p5) → ((p1 ∨ (True → (((p5 → False) ∨ p4) ∧ True))) → ((False ∨ (p5 ∧ False)) ∨ p5))) → p5) → p5) → p4) ∨ p4) → p4) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h3 : ((((False ∨ p5) → ((p1 ∨ (True → (((p5 → False) ∨ p4) ∧ True))) → ((False ∨ (p5 ∧ False)) ∨ p5))) → p5) → p5) := by
      -- Implications on the right can always be decomposed.
      intro h4
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h5 : ((False ∨ p5) → ((p1 ∨ (True → (((p5 → False) ∨ p4) ∧ True))) → ((False ∨ (p5 ∧ False)) ∨ p5))) := by
        -- Implications on the right can always be decomposed.
        intro h6
        -- Implications on the right can always be decomposed.
        intro h7
        -- Disjunctions on the left can always be decomposed.
        cases h7
        case inl h8 =>
          -- Disjunctions on the left can always be decomposed.
          cases h6
          case inl h9 =>
            -- False on the left can always be used.
            apply False.elim h9
          case inr h10 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h10
        case inr h11 =>
          -- Disjunctions on the left can always be decomposed.
          cases h6
          case inl h12 =>
            -- False on the left can always be used.
            apply False.elim h12
          case inr h13 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h13
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h14 := h4 h5
      -- One of the premise coincides with the conclusion.
      exact h14
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h15 := h2 h3
    -- One of the premise coincides with the conclusion.
    exact h15
  case inr h16 =>
    -- One of the premise coincides with the conclusion.
    exact h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_622193975300153275848342892385 : ((((p2 ∧ (p1 ∧ ((p3 → (p4 → True)) → ((p3 → ((p5 → ((p2 ∧ p5) → p4)) ∧ False)) ∧ (True ∨ ((p4 ∧ False) ∧ p3)))))) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156773738961659260416410563681 : ((((p2 ∨ p4) → (((True → (((p4 ∨ p2) ∧ p2) ∨ (p4 ∧ (True → p3)))) → p2) ∨ p5)) ∧ p1) ∨ ((p3 → ((False → p4) ∧ p3)) ∧ True)) := by
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
  -- False on the left can always be used.
  apply False.elim h2
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137536047542581452088372171084 : ((p5 ∧ (p4 ∨ ((((p5 ∧ ((p4 → p5) ∧ p5)) → p4) → ((p1 → p5) ∨ ((False → False) ∧ p2))) ∨ (True → True)))) ∨ (p4 → (False → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167561325515745519454797853164 : (((((p1 ∧ False) ∨ ((p3 ∨ (((p1 ∨ p4) ∨ p5) ∨ p3)) → p4)) → False) ∨ (p4 ∧ p1)) → (((p1 → (True ∧ p1)) → False) → (p1 ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h4 : (p1 → (True ∧ p1)) := by
      -- Implications on the right can always be decomposed.
      intro h5
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- One of the premise coincides with the conclusion.
      exact h5
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h6 := h2 h4
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328746364207872058927561659688 : (True → ((p5 ∨ ((((False ∧ p2) → ((p4 → p2) ∨ p5)) ∨ p4) → False)) → (((False → (p2 → p2)) ∧ (False → p5)) ∧ ((p2 ∨ p1) ∨ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- False on the left can always be used.
  apply False.elim h3
  -- Implications on the right can always be decomposed.
  intro h5
  -- False on the left can always be used.
  apply False.elim h5
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h8 : (((False ∧ p2) → ((p4 → p2) ∨ p5)) ∨ p4) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h9
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- False on the left can always be used.
      apply False.elim h10
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h12 := h7 h8
    -- False on the left can always be used.
    apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118168065522065886349750411036 : ((False ∨ ((False ∨ p3) ∨ ((((p5 → p2) ∧ True) ∨ ((p3 ∨ ((False ∨ p2) → ((p1 ∨ (p5 → p2)) ∧ p4))) ∨ True)) ∨ p3))) ∨ (p4 ∨ p2)) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_716635631505753501881424771742 : (((((p4 ∧ p1) → (p2 ∧ p1)) ∧ (((((p3 ∨ p1) ∧ (True ∧ ((True → (p1 ∨ p2)) ∧ ((True → p4) ∨ p5)))) ∧ p1) ∧ p1) → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218284748040655464297213656523 : (((p3 ∨ p1) ∨ (p3 ∨ p4)) → ((p2 ∨ (((p3 ∧ p3) ∨ ((p2 ∨ (p2 ∧ p2)) → (p5 ∧ p3))) → (True ∧ ((p2 ∧ True) ∨ p1)))) ∨ True)) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347105314098624482090799857244 : (p3 → ((((False ∨ ((True → p5) ∨ (True → p2))) ∨ (p5 ∨ p2)) → (p4 ∨ False)) ∨ (True ∧ (((p2 → (p5 ∨ p1)) → (p5 → True)) ∧ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68980506727089660989006386421 : ((p4 → (p5 → ((p4 ∨ True) → (((p4 → ((False → (p3 ∧ p5)) ∧ p3)) ∧ ((p2 → (p4 ∧ (p1 ∧ (p1 ∧ p1)))) → p3)) ∨ p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_627730422494471705229357403419 : ((((((((p5 ∧ (((p1 → (p4 ∨ p1)) ∧ p2) ∧ p1)) → ((p4 ∧ True) ∧ False)) → p5) ∧ (((False ∧ p4) ∨ p1) → False)) ∧ True) → p5) ∨ p1) ∧ True) := by
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
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h6 : ((p5 ∧ (((p1 → (p4 ∨ p1)) ∧ p2) ∧ p1)) → ((p4 ∧ True) ∧ False)) := by
    -- Implications on the right can always be decomposed.
    intro h7
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Conjunctions on the left can always be decomposed.
    let h12 := h10.left
    let h13 := h10.right
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h14 : ((False ∧ p4) ∨ p1) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h11
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h15 := h5 h14
    -- False on the left can always be used.
    apply False.elim h15
    -- True on the right can always be proven directly.
    apply True.intro
    -- Conjunctions on the left can always be decomposed.
    let h16 := h7.left
    let h17 := h7.right
    -- Conjunctions on the left can always be decomposed.
    let h18 := h17.left
    let h19 := h17.right
    -- Conjunctions on the left can always be decomposed.
    let h20 := h18.left
    let h21 := h18.right
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h22 : ((False ∧ p4) ∨ p1) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h19
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h23 := h5 h22
    -- False on the left can always be used.
    apply False.elim h23
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h24 := h4 h6
  -- One of the premise coincides with the conclusion.
  exact h24
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68065336922635099487883995888 : ((p2 → (p1 ∨ (((p3 → False) ∨ (((p5 ∨ (p5 ∧ ((p2 ∨ (p1 → p4)) ∧ p5))) ∨ (p1 → (p5 → p5))) ∨ (True → p4))) ∨ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47499400568776654468370505294 : (((p1 ∨ (((p3 ∧ False) ∧ (((False ∧ p3) → (p2 ∧ p2)) → p2)) ∧ ((((False → (p3 → p2)) ∧ True) ∧ True) → p4))) ∨ (p5 ∧ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161794484765540435065983218243 : ((p5 ∨ ((((p3 ∧ (((p4 ∨ (False → (p3 → p3))) → (False ∧ p5)) ∧ False)) → p2) ∨ p1) → p3)) → ((False ∨ p5) ∨ (p3 ∨ (True → p1)))) := by
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
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h4 : (((p3 ∧ (((p4 ∨ (False → (p3 → p3))) → (False ∧ p5)) ∧ False)) → p2) ∨ p1) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h5
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- False on the left can always be used.
      apply False.elim h9
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h10 := h3 h4
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_667098474737185226995760292477 : ((((((p4 ∧ p2) ∧ p2) ∨ (p1 ∧ (((((True → (p5 → p2)) ∨ (False ∨ p3)) → p1) ∧ p3) ∧ (p4 → p1)))) ∧ (p3 → (p2 ∧ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_88245156239038544244152259400 : (((p1 ∨ ((p1 ∧ p2) ∨ p2)) ∧ (((p5 → False) ∨ False) ∧ ((p4 → (True ∨ p1)) → (((True ∨ True) ∧ (p1 ∨ p1)) ∧ (p3 ∧ False))))) → p3) := by
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
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h8 : (p4 → (True ∨ p1)) := by
        -- Implications on the right can always be decomposed.
        intro h9
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h10 := h6 h8
      -- We need to get the right conjuct of h10 based on <expert-advice>.
      let h11 := h10.right
      -- We need to get the left conjuct of h11 based on <expert-advice>.
      let h12 := h11.left
      -- One of the premise coincides with the conclusion.
      exact h12
    case inr h13 =>
      -- False on the left can always be used.
      apply False.elim h13
  case inr h14 =>
    -- Disjunctions on the left can always be decomposed.
    cases h14
    case inl h15 =>
      -- Conjunctions on the left can always be decomposed.
      let h16 := h15.left
      let h17 := h15.right
      -- Conjunctions on the left can always be decomposed.
      let h18 := h3.left
      let h19 := h3.right
      -- Disjunctions on the left can always be decomposed.
      cases h18
      case inl h20 =>
        -- We want to use the implication h19 based on <expert-advice>. So we show its premise.
        have h21 : (p4 → (True ∨ p1)) := by
          -- Implications on the right can always be decomposed.
          intro h22
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h19, we can now drive its conclusion.
        let h23 := h19 h21
        -- We need to get the right conjuct of h23 based on <expert-advice>.
        let h24 := h23.right
        -- We need to get the left conjuct of h24 based on <expert-advice>.
        let h25 := h24.left
        -- One of the premise coincides with the conclusion.
        exact h25
      case inr h26 =>
        -- False on the left can always be used.
        apply False.elim h26
    case inr h27 =>
      -- Conjunctions on the left can always be decomposed.
      let h28 := h3.left
      let h29 := h3.right
      -- Disjunctions on the left can always be decomposed.
      cases h28
      case inl h30 =>
        -- We want to use the implication h29 based on <expert-advice>. So we show its premise.
        have h31 : (p4 → (True ∨ p1)) := by
          -- Implications on the right can always be decomposed.
          intro h32
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h29, we can now drive its conclusion.
        let h33 := h29 h31
        -- We need to get the right conjuct of h33 based on <expert-advice>.
        let h34 := h33.right
        -- We need to get the left conjuct of h34 based on <expert-advice>.
        let h35 := h34.left
        -- One of the premise coincides with the conclusion.
        exact h35
      case inr h36 =>
        -- False on the left can always be used.
        apply False.elim h36



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67844518697925675341555755927 : ((p2 → ((p3 ∧ ((p4 ∨ (p3 ∧ p4)) ∨ ((p1 ∧ p2) → (True ∨ (((p5 → True) ∧ (False ∨ p2)) ∨ (True → False)))))) ∨ (p5 ∧ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_656784602526621788671808527787 : ((((((p3 ∨ ((p2 ∨ p4) ∧ p2)) → p3) → ((p4 ∨ (p3 ∨ (p3 → ((p5 ∨ (p5 ∧ (p4 ∧ p2))) → p5)))) ∧ p1)) ∨ (p3 → p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59839214143607041795194066181 : (((p3 ∧ p4) → ((((p5 → False) → (((p1 ∧ (p3 ∧ p1)) ∧ p3) ∧ p2)) → (p5 ∧ (((p1 ∧ p4) ∧ p2) ∧ (p3 ∧ True)))) ∧ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173233883023908942744099789785 : ((True → (((p4 ∧ ((p3 ∧ (p4 ∧ p3)) ∨ p4)) ∨ (p3 → p3)) ∧ (True ∨ True))) ∨ ((p2 ∧ (p2 ∧ p1)) ∧ ((p1 ∧ (p5 ∨ p5)) → p5))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_216762657488259271696189970332 : ((((p3 → p4) → p2) ∧ p1) → (p3 ∨ (((p3 ∨ (((p4 → p1) ∧ (((p5 ∧ p1) → p1) → p4)) ∧ (p5 → False))) → (p3 ∨ False)) ∨ True))) := by
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
theorem thm_5_vars_179187827094615964008674539083 : ((p3 ∧ ((((True → p3) ∧ p3) → (p3 ∧ p5)) ∨ ((p2 ∨ p1) ∨ p4))) ∨ ((True → p2) ∨ ((True ∧ (p2 ∨ True)) ∨ ((p4 ∨ p5) ∧ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114306791363592510226230895649 : ((((p2 ∨ (((p3 → (p1 ∧ p1)) ∧ p5) ∨ p2)) ∧ ((p1 ∨ (p4 → (p4 → p4))) ∨ p3)) ∧ ((p1 ∨ (p1 ∧ p1)) → p5)) ∨ (p5 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324419485165006136539626485650 : (p5 ∨ ((p2 ∨ ((False ∨ False) ∨ (p1 ∨ False))) → ((False ∨ (True ∨ (p4 → p3))) → ((p3 ∨ (p5 ∧ p5)) ∨ (p1 → ((False → p5) ∨ p2)))))) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h6 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h7
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h6
      case inr h8 =>
        -- Disjunctions on the left can always be decomposed.
        cases h8
        case inl h9 =>
          -- Disjunctions on the left can always be decomposed.
          cases h9
          case inl h10 =>
            -- False on the left can always be used.
            apply False.elim h10
          case inr h11 =>
            -- False on the left can always be used.
            apply False.elim h11
        case inr h12 =>
          -- Disjunctions on the left can always be decomposed.
          cases h12
          case inl h13 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h14
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Implications on the right can always be decomposed.
            intro h15
            -- False on the left can always be used.
            apply False.elim h15
          case inr h16 =>
            -- False on the left can always be used.
            apply False.elim h16
    case inr h17 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h18 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h19
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h18
      case inr h20 =>
        -- Disjunctions on the left can always be decomposed.
        cases h20
        case inl h21 =>
          -- Disjunctions on the left can always be decomposed.
          cases h21
          case inl h22 =>
            -- False on the left can always be used.
            apply False.elim h22
          case inr h23 =>
            -- False on the left can always be used.
            apply False.elim h23
        case inr h24 =>
          -- Disjunctions on the left can always be decomposed.
          cases h24
          case inl h25 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h26
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Implications on the right can always be decomposed.
            intro h27
            -- False on the left can always be used.
            apply False.elim h27
          case inr h28 =>
            -- False on the left can always be used.
            apply False.elim h28



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225694815636907955355598931755 : (((p3 → p1) ∧ p4) ∨ ((False ∧ ((True ∧ True) ∧ ((((p2 → False) ∨ p3) ∨ p1) ∨ p5))) ∨ ((False → (p2 → (p4 ∧ p2))) ∨ (p1 ∨ p5)))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245248208053713731840873973748 : ((p2 ∧ p1) ∨ (((p3 → False) ∧ (True ∧ (p5 → p2))) → ((p1 ∨ False) → ((((p1 → (p2 → p2)) → False) ∨ p3) ∨ ((p1 ∨ True) ∨ p2))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h8 =>
    -- False on the left can always be used.
    apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324284895193561141846571539420 : (p5 ∨ (((p1 → (((p1 ∨ p1) → p4) → p2)) ∧ p1) → ((((True ∧ (p4 ∨ (p2 → p5))) → (p2 ∨ (True → p4))) ∨ (True ∨ p2)) ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_775976840214882808754882891002 : (((False ∨ (p2 → (False ∧ ((True → (((p4 → (p3 ∨ True)) → p3) ∧ (p3 ∨ ((p4 ∧ False) → True)))) ∨ ((p2 ∧ False) → (True ∨ p4)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37862459151443116689612180529 : ((((p3 → ((p3 ∧ ((((p1 ∨ True) ∨ False) → (True ∨ ((True → p2) ∨ p5))) ∧ (p5 → (p5 → (p5 → True))))) → True)) → p5) ∧ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_693107136641841005434006142850 : ((((p3 ∧ ((((p5 → (True ∧ p1)) → (p2 ∨ p3)) ∨ (False ∨ p2)) → False)) ∧ (p1 → ((((p5 ∨ (p5 ∨ p2)) ∧ p4) → True) ∨ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172787961844742108428050069452 : (((False → p2) → ((True ∨ (p2 ∨ (p3 → (p1 → p1)))) → (p2 ∨ (p5 ∧ p2)))) ∨ (True ∧ ((((True ∨ p5) ∧ False) → (p3 ∨ p5)) ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
    -- False on the left can always be used.
    apply False.elim h3
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300151046874644257056480904510 : (False ∨ ((p2 ∨ ((((False ∨ p1) ∨ p3) ∧ (True ∧ True)) → (((((((p4 → p2) ∧ p2) → p4) ∨ False) ∧ p5) ∨ True) ∧ True))) ∨ (p5 ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- False on the left can always be used.
      apply False.elim h5
    case inr h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h3.left
      let h8 := h3.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h3.left
    let h11 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192566565775364883320565114231 : (((p3 ∨ ((p2 ∧ ((True ∨ p1) → True)) ∧ True)) ∨ p3) → ((True → (((False ∨ p3) ∨ p5) → (((False ∨ p3) → False) → p5))) ∨ (False → p1))) := by
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
      -- Implications on the right can always be decomposed.
      intro h4
      -- False on the left can always be used.
      apply False.elim h4
    case inr h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Conjunctions on the left can always be decomposed.
      let h8 := h6.left
      let h9 := h6.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- False on the left can always be used.
      apply False.elim h10
  case inr h11 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h12
    -- False on the left can always be used.
    apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115122214126281273668927447123 : (((((((p2 → True) ∧ True) ∨ p5) ∨ p2) ∧ (False ∨ (False → p3))) → ((p1 ∨ ((True ∧ ((p1 ∧ True) ∨ False)) ∨ p5)) ∨ p1)) ∨ (True ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63105712226701762223456892454 : ((p5 ∧ ((True → ((((False → p1) ∨ ((p2 ∧ True) ∨ p5)) → (False ∧ ((((False ∧ p3) → (p3 → p1)) → p1) ∧ False))) ∧ p4)) ∨ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64115858615535814111073607579 : ((False ∨ (((p4 ∧ ((p4 ∨ True) ∧ p5)) ∧ p2) ∨ ((((True ∧ p3) ∨ True) ∨ ((True ∧ p2) ∧ True)) → ((p2 ∧ True) → (False → p4))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112341251658708056123142979073 : (((p5 → ((((True → p5) → ((((p2 ∨ p3) ∨ False) ∨ (p2 → p4)) ∧ False)) ∧ (p1 ∧ (p2 → p2))) ∧ (True → p1))) ∨ p3) ∨ (p2 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54969988039421578622181665542 : (((((p5 → p1) → p2) → (p1 → p4)) ∧ ((p1 ∨ (p2 ∨ p5)) → ((p1 → (p3 ∧ ((p1 → p4) ∧ p4))) ∨ ((p2 ∧ True) ∨ p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135471480766927498670715386309 : (((((((False ∧ (True ∨ p1)) ∧ p1) ∨ ((p2 ∧ p1) ∧ p3)) → p1) → (p2 ∨ (False ∧ p1))) → ((p4 ∨ p1) ∧ p3)) ∨ ((False ∧ True) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_644282823115727385927129248757 : ((((False ∨ (((True ∨ (p2 ∨ p1)) → (p2 ∨ ((p3 ∨ ((True → p1) ∨ (((p2 → p4) ∧ p1) ∧ p1))) → p4))) ∨ (False ∧ False))) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



