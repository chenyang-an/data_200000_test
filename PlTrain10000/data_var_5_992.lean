variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64832709396412493701660589927 : ((p2 ∨ (((p1 ∨ ((False ∨ p2) ∧ p3)) ∨ (((p5 ∨ ((p3 ∨ False) ∧ ((False ∨ p1) → False))) ∨ True) ∧ ((p3 ∧ p1) → p2))) → p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205644780566893747782610886685 : (((p5 ∧ False) ∨ (p3 ∧ (True → p5))) ∨ (((False ∨ ((False ∧ (p5 ∨ p5)) ∧ ((p5 ∨ False) ∨ p5))) → True) ∧ ((p5 ∧ (p3 ∨ p2)) ∨ True))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_700706955792072704855981642447 : ((((((((p2 ∨ True) ∨ p3) ∨ (p1 ∧ p2)) ∧ False) ∧ p1) ∧ ((((p5 ∨ p4) ∧ p4) ∨ (((p1 ∧ p2) → (p3 ∨ p2)) ∧ p1)) ∨ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_702610999658871548158263037352 : (((((p2 ∨ ((True ∨ ((p3 → True) → p3)) ∨ p5)) → p5) ∨ ((p5 ∨ ((((p4 ∨ True) ∧ p3) ∧ (p1 ∨ False)) → (p4 → p1))) ∨ False)) ∨ p5) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h8 =>
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h9 =>
      -- False on the left can always be used.
      apply False.elim h9
  case inr h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h11 =>
      -- One of the premise coincides with the conclusion.
      exact h11
    case inr h12 =>
      -- False on the left can always be used.
      apply False.elim h12
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_330442719520577843486807893009 : (True → (p3 ∨ (((((p3 ∧ p4) ∧ False) ∧ (False → p3)) → True) → ((((p1 ∧ p3) → (p2 → False)) ∨ p2) ∨ (True ∨ ((p5 → p2) → False)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_182872793515703911901324705477 : (((p1 ∧ (p2 ∧ p4)) ∨ (p1 ∨ ((False ∧ (p5 ∧ p1)) → p2))) ∧ ((p2 ∨ (p2 → (((p4 ∨ (False ∨ p3)) → (True ∨ p3)) ∨ p3))) ∨ p3)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h5
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- False on the left can always be used.
      apply False.elim h8
    case inr h9 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49396839448805057158342427725 : (((((p1 ∨ (((p5 → (p5 ∧ False)) → ((p1 ∧ True) ∨ (False → p3))) → p5)) → ((False ∨ p5) ∨ p2)) ∧ p2) → ((p1 ∨ p3) ∨ True)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_138414174977501880018791789610 : ((p5 → ((True ∧ (p5 ∧ ((True ∨ p4) → (p4 ∧ (False ∧ (p3 → ((p3 ∧ True) → (p4 ∧ (p5 ∧ p4))))))))) ∨ p5)) ∨ ((False → p3) ∧ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193284760905738872884943151089 : ((((p5 ∧ True) ∨ False) ∨ ((p3 ∨ (p1 ∨ p1)) ∨ p5)) → ((((True → p4) ∨ (((p2 → p4) ∧ (p4 ∧ (p3 ∧ False))) → p1)) → p2) → p2)) := by
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
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h7 : ((True → p4) ∨ (((p2 → p4) ∧ (p4 ∧ (p3 ∧ False))) → p1)) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h8
        -- Conjunctions on the left can always be decomposed.
        let h9 := h8.left
        let h10 := h8.right
        -- Conjunctions on the left can always be decomposed.
        let h11 := h10.left
        let h12 := h10.right
        -- Conjunctions on the left can always be decomposed.
        let h13 := h12.left
        let h14 := h12.right
        -- False on the left can always be used.
        apply False.elim h14
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h15 := h2 h7
      -- One of the premise coincides with the conclusion.
      exact h15
    case inr h16 =>
      -- False on the left can always be used.
      apply False.elim h16
  case inr h17 =>
    -- Disjunctions on the left can always be decomposed.
    cases h17
    case inl h18 =>
      -- Disjunctions on the left can always be decomposed.
      cases h18
      case inl h19 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h20 : ((True → p4) ∨ (((p2 → p4) ∧ (p4 ∧ (p3 ∧ False))) → p1)) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h21
          -- Conjunctions on the left can always be decomposed.
          let h22 := h21.left
          let h23 := h21.right
          -- Conjunctions on the left can always be decomposed.
          let h24 := h23.left
          let h25 := h23.right
          -- Conjunctions on the left can always be decomposed.
          let h26 := h25.left
          let h27 := h25.right
          -- False on the left can always be used.
          apply False.elim h27
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h28 := h2 h20
        -- One of the premise coincides with the conclusion.
        exact h28
      case inr h29 =>
        -- Disjunctions on the left can always be decomposed.
        cases h29
        case inl h30 =>
          -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
          have h31 : ((True → p4) ∨ (((p2 → p4) ∧ (p4 ∧ (p3 ∧ False))) → p1)) := by
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h32
            -- Conjunctions on the left can always be decomposed.
            let h33 := h32.left
            let h34 := h32.right
            -- Conjunctions on the left can always be decomposed.
            let h35 := h34.left
            let h36 := h34.right
            -- Conjunctions on the left can always be decomposed.
            let h37 := h36.left
            let h38 := h36.right
            -- False on the left can always be used.
            apply False.elim h38
          -- We have shown the premise of h2, we can now drive its conclusion.
          let h39 := h2 h31
          -- One of the premise coincides with the conclusion.
          exact h39
        case inr h40 =>
          -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
          have h41 : ((True → p4) ∨ (((p2 → p4) ∧ (p4 ∧ (p3 ∧ False))) → p1)) := by
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h42
            -- Conjunctions on the left can always be decomposed.
            let h43 := h42.left
            let h44 := h42.right
            -- Conjunctions on the left can always be decomposed.
            let h45 := h44.left
            let h46 := h44.right
            -- Conjunctions on the left can always be decomposed.
            let h47 := h46.left
            let h48 := h46.right
            -- False on the left can always be used.
            apply False.elim h48
          -- We have shown the premise of h2, we can now drive its conclusion.
          let h49 := h2 h41
          -- One of the premise coincides with the conclusion.
          exact h49
    case inr h50 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h51 : ((True → p4) ∨ (((p2 → p4) ∧ (p4 ∧ (p3 ∧ False))) → p1)) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h52
        -- Conjunctions on the left can always be decomposed.
        let h53 := h52.left
        let h54 := h52.right
        -- Conjunctions on the left can always be decomposed.
        let h55 := h54.left
        let h56 := h54.right
        -- Conjunctions on the left can always be decomposed.
        let h57 := h56.left
        let h58 := h56.right
        -- False on the left can always be used.
        apply False.elim h58
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h59 := h2 h51
      -- One of the premise coincides with the conclusion.
      exact h59



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321234241947175367271331511269 : (p4 ∨ (p4 ∨ (((p5 ∧ True) → (((p3 ∨ p2) ∧ ((p5 → True) ∧ (True → (p5 → p2)))) ∨ (((False → p5) → (p3 → True)) → p5))) ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65271710017602131160896876419 : ((p3 ∨ ((p1 → ((((p4 ∨ (p2 → p1)) ∧ ((p2 ∨ p4) → p1)) ∨ ((((p4 ∧ p2) ∨ p5) ∧ (p3 → False)) ∧ p5)) ∨ p4)) → p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263158127391794614520142969052 : (True ∧ ((p4 ∧ ((((True ∧ (p3 → ((p1 ∨ ((True ∨ ((p3 ∧ False) ∧ True)) → False)) → False))) → p3) ∨ (p5 → p2)) ∨ True)) ∨ (p1 ∨ True))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_587702681101924017605881988397 : (((((((p5 → p1) → (((False → p3) ∧ ((True → ((p1 → (False ∧ True)) → False)) ∧ (p4 → False))) ∧ (p2 → p2))) → p2) ∨ p2) ∧ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248043880538358402936770063100 : ((p1 ∨ p5) ∨ ((p3 → ((True ∧ False) ∧ p3)) → ((((p5 → p3) ∧ (p1 ∧ (p1 ∧ p5))) ∧ ((p2 → (p3 ∧ (p5 → p3))) → True)) → p4))) := by
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
  let h5 := h3.left
  let h6 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h6.left
  let h8 := h6.right
  -- Conjunctions on the left can always be decomposed.
  let h9 := h8.left
  let h10 := h8.right
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h11 : p5 := by
    -- One of the premise coincides with the conclusion.
    exact h10
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h12 := h5 h11
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h13 : p3 := by
    -- One of the premise coincides with the conclusion.
    exact h12
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h14 := h1 h13
  -- We need to get the left conjuct of h14 based on <expert-advice>.
  let h15 := h14.left
  -- We need to get the right conjuct of h15 based on <expert-advice>.
  let h16 := h15.right
  -- False on the left can always be used.
  apply False.elim h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136246327437156967027957633225 : (((p5 ∧ ((p3 ∨ p1) ∨ (False ∨ p1))) ∨ ((((p3 → p3) ∧ True) → p4) ∨ ((p5 ∧ (p1 ∧ (p2 → True))) ∨ p2))) ∨ (True ∨ (False → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135740521033189123681919710761 : ((((p3 → (((False → (p4 → p1)) ∧ p4) → p5)) ∧ (p1 ∧ (p1 ∧ p2))) ∨ ((((p5 ∧ p5) → p4) ∧ p1) ∨ True)) ∨ (p5 ∨ (p4 → p3))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148717538780989714987300782849 : ((((p2 → p2) ∨ (p2 ∧ (False ∧ (p4 ∧ p4)))) → ((False ∧ True) ∧ ((p2 ∧ ((False ∨ p4) → p3)) ∨ p2))) ∨ ((p5 → (p5 ∧ p1)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_617496424477451122219602874545 : ((((((p5 ∧ ((p2 → True) ∨ p1)) → p2) ∧ (((p2 ∧ p1) ∨ (p3 ∧ True)) → (((p1 ∨ p4) → p1) ∨ (p4 ∨ (p5 → p2))))) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_318547281415778006795390454821 : (p4 ∨ ((((p1 ∧ ((((p4 → p5) → p4) ∧ p1) ∧ p4)) ∨ ((p4 ∨ (True ∧ (False ∨ p3))) ∨ (p1 ∨ (p5 → True)))) ∧ True) ∨ (True ∧ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_138367538439250968183519842720 : ((p4 → (((True ∧ ((p5 ∧ (p2 → p5)) ∨ (p5 ∧ p1))) ∧ (p3 ∧ p5)) ∨ (((True → (p1 ∨ p1)) ∧ False) → True))) ∨ ((p1 → False) ∧ p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_265775162519937640389580890872 : (True ∧ (p4 ∨ ((True ∧ (p1 ∧ ((p2 → (False → True)) → ((p3 ∨ (p5 ∨ True)) → (p5 ∨ False))))) ∨ (p3 → ((True → (p5 → p3)) ∨ False))))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173427421030982405239626611266 : ((p5 → (p3 ∧ ((((p4 ∧ ((p2 → True) ∧ True)) → p4) → False) ∨ (p1 ∨ p1)))) ∨ (p5 → (p1 ∨ ((p5 ∨ (p5 → p2)) ∧ (p5 ∧ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47498561829567783194569507784 : (((p1 ∨ (((((False ∨ (p1 → False)) → True) ∧ p4) → (((p4 → p4) ∨ p5) → (p1 → p1))) → (p1 ∧ (False ∨ p2)))) ∨ (p3 ∨ True)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219592099439653713919932957464 : ((True → (p5 ∧ (p3 → p5))) → (((p3 → (True ∨ (((p5 → (True ∧ p3)) ∨ False) ∨ p1))) → p4) ∨ ((((p4 → p4) ∧ p4) ∨ p4) → p5))) := by
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
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h6 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h7 := h1 h6
    -- We need to get the left conjuct of h7 based on <expert-advice>.
    let h8 := h7.left
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h10 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h11 := h1 h10
    -- We need to get the left conjuct of h11 based on <expert-advice>.
    let h12 := h11.left
    -- One of the premise coincides with the conclusion.
    exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158210187789734196923012771372 : ((((p5 ∧ p5) → p3) ∧ (False ∧ ((True → (p1 ∨ p4)) ∨ (((p5 ∧ p4) ∨ p3) ∨ (True → p1))))) ∨ (p2 ∨ (((False ∨ p2) ∧ p4) → p2))) := by
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
  cases h2
  case inl h4 =>
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113063536897919795811600033715 : (((p2 ∨ (False ∨ (((((p4 ∨ p5) ∨ False) ∨ False) ∨ (p2 → (((p4 ∧ ((True ∧ False) ∧ p1)) ∨ p1) ∧ True))) → p1))) → p1) ∨ (p3 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55561330853817338548900697555 : (((p4 ∧ ((p4 ∧ p1) ∨ (p4 → p2))) → ((False ∧ (((p2 ∧ (True ∧ p1)) → p5) → p2)) ∨ ((((p1 ∨ False) ∨ p1) ∧ False) ∨ p4))) ∨ p3) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354687457353394607575065881798 : (p5 → (((((p1 ∨ p5) ∧ ((((p3 → p1) ∨ False) ∨ True) → (((p2 ∨ p4) ∧ (p4 ∧ True)) ∨ (p5 → False)))) ∧ p4) ∨ (p5 ∨ p5)) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_699032841281034884545654051312 : ((((p1 ∨ (p5 ∨ ((((p5 ∨ p3) ∧ p2) ∨ True) ∧ (p4 → False)))) ∨ (((p5 → (p4 → p1)) ∨ (True ∨ (p2 ∨ (p4 ∨ p2)))) ∧ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_311110180570131540546223679278 : (p2 ∨ ((p2 → False) ∨ ((False ∧ (((p3 ∨ ((True ∧ (False → True)) → p1)) ∧ True) → ((p3 → p4) ∨ ((p1 ∧ (True ∧ True)) → p5)))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39690318670447656299317109329 : (((p4 ∨ ((p5 ∧ (p3 ∧ (p5 ∧ p3))) ∨ ((((((p3 ∧ False) ∧ p2) → p2) ∧ (((True → p3) ∧ False) ∧ p1)) ∨ False) → p3))) ∧ True) ∨ False) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- False on the left can always be used.
    apply False.elim h9
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_618568028088385052937466399157 : (((((True ∨ (p5 ∧ (p2 ∨ p4))) → (((p2 ∨ (((p1 ∨ True) ∧ p5) ∧ p5)) ∧ (((p2 ∧ p2) → p2) ∧ (p1 ∧ True))) ∨ p1)) ∨ True) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_589944292092837247391904024737 : (((((((((False ∨ True) ∧ (True ∨ (p5 → False))) ∨ (p1 → ((False ∧ False) → p4))) ∧ p4) ∨ (p5 ∧ ((True ∧ True) → p2))) → False) ∧ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303752819110765533466822973009 : (p1 ∨ (((((((True ∨ True) → p2) ∧ (p4 → p3)) ∧ (p4 → (((p5 ∧ p3) ∧ p5) ∧ (((p5 ∨ p4) → True) ∧ p3)))) → p2) ∨ True) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328515200673615535252123968580 : (True → (((((p2 ∧ p3) → p5) ∨ (((p4 ∨ p3) → p5) ∨ ((p1 ∨ p4) → p5))) → p2) ∨ (((False → True) ∧ ((p4 → False) → False)) → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245098812844628239126900751855 : ((p2 ∧ True) ∨ (((((((p5 ∧ p4) ∨ (p5 ∨ (True ∧ p2))) ∨ True) ∨ (p1 → p1)) ∨ (p4 ∨ ((p2 ∧ (True → True)) ∨ False))) ∨ p3) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_608710996483217422564134758099 : (((((((((p1 ∨ ((p4 → p1) ∨ p4)) → p5) ∨ p4) ∨ ((((True ∧ p1) ∧ p5) ∧ (p3 ∨ p1)) → False)) → (p2 ∨ p1)) ∨ False) ∨ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57507070555357378100327203497 : (((p3 → (p4 ∧ p1)) ∨ (False ∨ ((p5 → (p5 → (((p1 ∨ p1) → ((p4 ∧ p5) ∨ (True ∧ p4))) ∨ p5))) ∧ ((p2 ∧ p5) ∧ p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137447587382137503460324789125 : ((p4 ∧ ((p4 → (((False ∧ p1) ∧ True) ∧ p1)) ∨ ((p2 ∨ (True → ((False ∧ p1) ∨ ((False → p3) ∧ p2)))) ∧ True))) ∨ (False ∨ (p5 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62689062533627681051030206160 : ((p4 ∧ (((((((((False → True) ∧ p1) ∧ (p3 → ((True → (p4 ∧ True)) ∨ False))) → p2) ∧ True) ∧ p2) ∨ (p2 → p5)) ∨ False) → p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49009773803771362899703113558 : (((((((p3 ∨ True) ∧ p4) → (p5 ∨ (p4 ∧ (p1 → (((p4 ∧ (p4 → p4)) → True) ∨ True))))) ∨ p3) → False) ∨ ((p4 → p4) ∨ p5)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_563158293133658951665515407367 : (((p5 ∨ (((p4 ∨ (p5 → p2)) ∨ (True → p3)) → ((False ∨ (p3 ∨ (((((p3 → p1) → p1) ∨ p3) → (p5 ∨ p1)) → p1))) ∨ True))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_3901547944126397820829260379 : (False ∨ (((((p2 ∧ True) → (p1 ∧ p4)) ∧ ((p5 ∨ p2) ∨ ((False → ((False → p3) ∨ True)) ∧ ((p1 ∨ p2) → p2)))) ∨ True) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47136966418223897938111584895 : (((((((p3 ∧ ((p5 → True) → ((False → p1) ∧ p2))) ∨ True) ∨ False) ∨ (p2 ∧ True)) ∧ ((p2 ∨ (True ∧ p1)) → p5)) ∨ (p3 ∨ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350006945212745830921587651829 : (p4 → (((False ∨ (p3 ∧ (p3 ∧ (((p2 → (p5 ∧ p2)) ∧ (True ∨ p1)) ∧ ((p2 ∧ ((False ∨ p4) → (p2 ∨ p2))) ∧ True))))) ∨ p1) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301396159407207480860445714253 : (False ∨ ((p3 ∨ (p3 ∨ (p2 ∨ p5))) ∨ ((p1 ∨ (p1 → ((p2 ∨ p3) → ((((p4 ∧ p4) ∧ p5) ∧ True) → (p4 ∨ p4))))) ∧ (False → p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h10 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h9
  case inr h11 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h9
  -- Implications on the right can always be decomposed.
  intro h12
  -- False on the left can always be used.
  apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49196906286605200969021903011 : (((((p5 ∨ False) ∧ p2) ∨ (((p2 ∨ (((p1 → p3) ∧ (p3 ∨ (p5 ∨ False))) ∨ True)) ∨ (p2 → p4)) ∨ p1)) ∨ ((p2 ∧ False) → p1)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_165698631763601473068591878371 : (((p2 → (((p3 ∨ p4) ∨ False) → False)) → (True → (p5 ∨ (True ∧ ((p1 → p5) ∧ False))))) ∨ ((p2 ∧ p5) → ((p1 ∨ True) ∧ (p3 → True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64936610077984093899318178128 : ((p2 ∨ (((p1 ∧ p2) → (((p1 ∨ (p3 ∨ (True ∨ p5))) → True) ∧ p1)) ∧ (p1 ∧ ((True → p2) ∧ (((p5 → p1) ∨ p2) → False))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350140360747167301155176388182 : (p4 → (((p1 ∧ ((True → ((True ∨ p1) ∨ ((p3 ∨ p2) → False))) ∨ p5)) ∧ (p3 ∧ (p5 ∧ ((p1 ∨ (p2 ∧ p4)) → (p1 ∨ False))))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50345578713781660084780960242 : ((((((p3 ∧ p2) ∨ p2) → (p3 ∧ p5)) → (((p1 ∨ True) ∧ (((p3 ∨ True) → p3) ∧ p1)) → False)) ∨ (((p1 ∨ False) ∨ p1) → p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116519981792799348075763798681 : (((p5 ∧ p2) ∧ ((((p4 → p4) → ((((p3 ∧ (((False ∧ (p1 ∧ False)) → p3) ∨ False)) ∨ p3) ∨ True) ∨ False)) ∧ p5) ∨ p5)) ∨ (True ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178890733022705154793630601250 : (((True ∨ False) ∧ (p1 ∧ (((p2 ∨ p1) ∨ (p1 ∧ (False ∧ False))) ∨ p1))) ∨ ((p2 → ((False ∧ False) → (False ∧ p4))) → ((p1 → p3) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_693325889294034854772384056055 : ((((True → ((p5 → p1) ∨ (((p3 ∨ p2) ∨ p4) ∨ ((p1 ∧ p5) ∧ p4)))) ∧ ((p3 ∨ ((p4 ∨ p3) ∨ p3)) ∨ (p2 ∧ (p2 → True)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48702532466864970581832715925 : ((((((p1 ∧ True) ∨ (p1 ∨ p4)) → p1) ∨ ((p1 → ((p4 ∨ (p2 ∨ (p4 ∧ (p2 ∧ p1)))) ∨ p5)) → False)) ∧ (p2 ∨ (True → p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_15194544202162953429991723702 : (((True → ((p5 ∨ (p5 ∧ p1)) ∧ ((((p2 → ((((p2 → p3) ∨ p5) → p2) ∨ True)) → (p3 ∧ True)) ∧ p5) ∨ p4))) ∨ (False → p2)) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_690560349728911299196365214016 : ((((((((((p5 → False) → True) ∧ True) ∨ (True ∨ p3)) → (False ∧ True)) ∧ p3) ∨ p3) → (((p5 ∧ False) ∨ ((p1 ∨ p3) ∨ p3)) ∨ True)) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218878256912669931559683675072 : ((p2 ∧ (False → (p2 ∨ p4))) → (p3 ∨ ((((p4 ∧ (False → (((False ∨ (True → (p4 → p3))) ∨ (p1 ∨ p5)) ∨ p3))) → p3) ∨ p5) ∨ True))) := by
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
theorem thm_5_vars_147096726494743558675297150540 : ((((p5 → (True ∨ p2)) ∧ (((p4 ∧ (p2 ∨ p2)) ∧ ((p2 ∧ (p5 ∧ False)) ∧ (p3 ∧ p3))) ∨ p2)) ∧ True) ∨ ((True ∧ p3) → (False → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39435028065673357379644981697 : (((p5 ∧ (((((p3 ∨ p4) → (p1 ∧ (((((True → (p4 → p2)) → p5) → p5) → p1) → p5))) ∧ (p2 ∧ p4)) ∧ p3) ∨ p5)) ∧ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_938190058757959624385897602243 : ((((p4 → (((p4 ∧ p1) → True) → p3)) ∧ (p3 ∧ ((p5 → (((True ∧ p2) ∧ p3) ∧ (((p2 → True) ∨ (p4 ∨ p4)) → True))) ∧ True))) → p3) ∧ True) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- One of the premise coincides with the conclusion.
  exact h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199855395233269323555761262841 : (((False ∨ ((p1 → p3) ∨ p3)) ∧ (False ∨ p4)) → (((p5 → p4) → (False ∧ p2)) → ((((((True ∨ p1) ∧ p3) → p1) → False) → p1) ∨ p2))) := by
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
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h8 =>
        -- False on the left can always be used.
        apply False.elim h8
      case inr h9 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h10 : (p5 → p4) := by
          -- Implications on the right can always be decomposed.
          intro h11
          -- One of the premise coincides with the conclusion.
          exact h9
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h12 := h2 h10
        -- We need to get the left conjuct of h12 based on <expert-advice>.
        let h13 := h12.left
        -- False on the left can always be used.
        apply False.elim h13
    case inr h14 =>
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h15 =>
        -- False on the left can always be used.
        apply False.elim h15
      case inr h16 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h17 : (p5 → p4) := by
          -- Implications on the right can always be decomposed.
          intro h18
          -- One of the premise coincides with the conclusion.
          exact h16
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h19 := h2 h17
        -- We need to get the left conjuct of h19 based on <expert-advice>.
        let h20 := h19.left
        -- False on the left can always be used.
        apply False.elim h20



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_357253196883557108274804050261 : (p5 → ((False ∧ p3) ∨ (((p2 ∧ (((((p5 ∧ p2) ∨ p2) ∧ p4) → (p1 ∨ False)) ∨ p4)) ∨ ((p4 ∧ p1) → (p1 ∨ True))) ∧ (p4 → True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Implications on the right can always be decomposed.
  intro h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51189158746313969820138090983 : (((((p1 ∨ (p5 ∧ (False ∧ True))) ∨ ((p5 → (p1 ∧ False)) ∧ p3)) ∨ ((True ∧ p4) ∧ p5)) ∨ (p1 ∨ (p3 ∨ (p2 ∨ (False → p5))))) ∨ p3) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_339714320403089704532683970007 : (p1 → (p3 ∨ (p2 → (False ∨ ((False ∨ (((p5 ∨ ((p2 ∨ p5) → p1)) ∧ True) → (p4 ∧ p4))) ∨ ((((p5 → p1) ∧ p3) ∨ p3) → p1)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h7 =>
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56273551474236801846142337434 : (((p4 → ((p2 ∨ p1) ∨ False)) ∨ ((p3 → (p2 ∧ (p1 ∧ ((True ∧ ((p5 ∨ False) → p4)) ∨ (((False ∨ p4) ∨ True) ∨ p4))))) ∨ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50017375468155151749932935171 : (((((((p4 → p4) ∨ p1) ∧ False) ∨ p3) → ((p3 → (p2 ∨ False)) ∨ (((p5 → True) ∨ p2) → p2))) ∧ (((p1 → p1) ∨ p2) ∧ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_151969630146816334594984442494 : ((((p5 ∨ p1) ∧ ((True → p3) ∧ (p4 ∧ ((p3 → p2) → p5)))) ∨ ((True → p1) → ((p4 ∧ p4) ∨ False))) → (p2 → (False ∨ (p1 ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h5.left
      let h8 := h5.right
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
      -- Conjunctions on the left can always be decomposed.
      let h12 := h5.left
      let h13 := h5.right
      -- Conjunctions on the left can always be decomposed.
      let h14 := h13.left
      let h15 := h13.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h11
  case inr h16 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_176437131658389306184238146223 : ((((((True → p3) → p1) ∨ True) → (p5 ∨ False)) ∨ (False → (True → p1))) ∧ ((p1 → p2) → (((p1 ∧ p4) ∧ True) → ((p3 → p3) ∨ p2)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h9
  -- One of the premise coincides with the conclusion.
  exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63893618096613173865411453612 : ((False ∨ ((((p1 → p5) ∨ ((((True → False) → p4) ∧ (p5 ∧ p3)) ∨ ((False ∨ False) ∨ ((p1 ∨ True) → p5)))) ∨ (p2 ∧ False)) ∧ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_221737663475967732733693320398 : (((False ∧ p5) → True) ∧ ((((((p2 → (True → p5)) → (((p4 → p3) ∧ p5) → (p4 ∨ p4))) → p4) → p5) ∧ p1) ∨ (False → (p2 → p4)))) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56032687968462129879961987169 : ((((p1 ∨ (p2 ∨ p2)) ∨ p1) ∨ (((p3 ∧ (False ∧ ((p5 ∧ False) ∧ (((False ∧ p4) → p5) → ((False ∧ p4) → p4))))) ∨ p5) → p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156624382950452355048896620709 : (((((((False → p4) ∧ (p4 ∨ (p5 → (True ∧ True)))) ∧ (p2 ∨ p2)) ∧ (p4 ∧ False)) ∨ p3) ∧ False) ∨ ((False ∨ ((True ∧ False) ∨ True)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305904330037681609703900222860 : (p1 ∨ (((True ∨ ((p5 ∧ p5) ∨ p2)) ∨ p2) → ((p5 ∧ (p1 ∧ p4)) ∨ (True ∨ ((((p5 ∨ ((True → p1) → p1)) ∨ p1) ∧ p1) ∧ p4))))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h4 =>
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h5 =>
        -- Conjunctions on the left can always be decomposed.
        let h6 := h5.left
        let h7 := h5.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h8 =>
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219639510265723936640921454241 : ((False → ((p5 ∧ True) → False)) → (p2 → (((((((p1 ∨ (False → True)) ∧ (p2 → ((True ∨ p1) ∧ False))) → p3) ∨ p4) → p1) → p1) ∨ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : ((((p1 ∨ (False → True)) ∧ (p2 → ((True ∨ p1) ∧ False))) → p3) ∨ p4) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
      have h9 : p2 := by
        -- One of the premise coincides with the conclusion.
        exact h2
      -- We have shown the premise of h7, we can now drive its conclusion.
      let h10 := h7 h9
      -- We need to get the right conjuct of h10 based on <expert-advice>.
      let h11 := h10.right
      -- False on the left can always be used.
      apply False.elim h11
    case inr h12 =>
      -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
      have h13 : p2 := by
        -- One of the premise coincides with the conclusion.
        exact h2
      -- We have shown the premise of h7, we can now drive its conclusion.
      let h14 := h7 h13
      -- We need to get the right conjuct of h14 based on <expert-advice>.
      let h15 := h14.right
      -- False on the left can always be used.
      apply False.elim h15
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h16 := h3 h4
  -- One of the premise coincides with the conclusion.
  exact h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148962237694490484649625533341 : ((((p2 ∨ False) ∨ p4) ∧ ((((True ∧ False) → p5) ∨ (p5 → ((p1 ∧ (False → p1)) ∨ p2))) → (p5 ∨ p4))) ∨ (False ∨ (True ∨ (p3 ∨ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_787683762587708286653902303 : (((p1 ∨ p3) → ((((((True ∨ (p4 ∧ (p4 ∨ p3))) → ((p2 ∨ p5) ∨ p4)) ∧ ((True ∧ p1) → p2)) ∨ True) ∨ p5) ∨ False)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56671838670329030373293743360 : ((((p1 → p1) ∧ p5) ∧ ((p4 ∨ p3) ∨ (((((((((p3 → False) → False) → p4) → (p2 ∧ True)) ∨ False) ∧ p2) ∨ p3) → False) → p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215294301847052768248731366409 : ((p1 ∧ ((True ∧ p3) ∨ p4)) ∨ ((((True ∧ p1) ∧ p2) ∧ ((True → (p5 ∧ p4)) ∨ p5)) → (((p4 → (p4 ∨ p1)) → (True ∧ False)) → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h9 =>
    -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
    have h10 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h9, we can now drive its conclusion.
    let h11 := h9 h10
    -- We need to get the right conjuct of h11 based on <expert-advice>.
    let h12 := h11.right
    -- One of the premise coincides with the conclusion.
    exact h12
  case inr h13 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h14 : (p4 → (p4 ∨ p1)) := by
      -- Implications on the right can always be decomposed.
      intro h15
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h15
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h16 := h2 h14
    -- We need to get the right conjuct of h16 based on <expert-advice>.
    let h17 := h16.right
    -- False on the left can always be used.
    apply False.elim h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190870112710198945578366479837 : (((((p2 ∧ p1) ∨ p4) ∨ (p3 ∨ True)) → (p3 ∧ p1)) ∨ (((True ∨ (p5 ∨ (True ∨ p5))) ∨ p4) ∨ ((True ∨ p1) → (True → (p2 ∧ False))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114545554696849319769200180356 : (((((((True → True) → (p3 ∨ p4)) ∨ ((p3 → p3) → p4)) → (p5 ∨ p1)) ∧ p3) ∧ (p5 ∨ ((p2 ∧ (True ∨ False)) → p3))) ∨ (True ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_600163757475184455364671506801 : (((((True → p3) → ((((p3 ∨ ((p5 ∨ p2) ∧ ((p4 → p3) ∧ True))) → ((((True ∨ p1) → p5) ∨ p3) ∧ p3)) ∨ p3) ∧ p5)) ∧ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319087199573588013863155903470 : (p4 ∨ (((((True → p3) → (p1 → p3)) ∧ (False ∨ ((p2 ∨ True) ∨ (p1 ∧ p2)))) ∧ ((p1 ∨ True) → False)) → (p2 → (True ∧ (p5 ∨ False))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  let h5 := h3.left
  let h6 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h7 =>
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
        have h11 : (p1 ∨ True) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h4, we can now drive its conclusion.
        let h12 := h4 h11
        -- False on the left can always be used.
        apply False.elim h12
      case inr h13 =>
        -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
        have h14 : (p1 ∨ True) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h4, we can now drive its conclusion.
        let h15 := h4 h14
        -- False on the left can always be used.
        apply False.elim h15
    case inr h16 =>
      -- Conjunctions on the left can always be decomposed.
      let h17 := h16.left
      let h18 := h16.right
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h19 : (p1 ∨ True) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h17
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h20 := h4 h19
      -- False on the left can always be used.
      apply False.elim h20



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_687227654471137348233454976746 : (((((((p1 → p5) ∨ ((p5 ∧ p5) ∨ (p4 → ((p4 → p2) ∨ p1)))) ∧ p1) ∧ p4) ∧ ((p2 ∧ True) ∧ ((p2 → p1) ∨ (p1 → p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300397949444399768352574718255 : (False ∨ (((p5 ∧ p4) → (((True → True) → ((False ∨ p4) → p3)) ∨ (((p1 ∨ p1) ∨ p1) ∨ ((p3 → p5) ∨ p3)))) ∨ ((p3 → False) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h4
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159642435165867476513184193895 : (((((p1 → True) ∨ (((((p2 ∨ p1) ∨ p2) ∨ p5) → (p5 ∨ (p1 ∨ p2))) ∧ p1)) ∨ False) ∨ False) → (p1 → (((p1 → p2) ∨ True) ∨ p5))) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h5 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
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
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h9 =>
      -- False on the left can always be used.
      apply False.elim h9
  case inr h10 =>
    -- False on the left can always be used.
    apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_721917972223641034548780677828 : ((((p5 ∨ (True ∧ (p4 → p4))) → ((p5 ∨ False) ∨ (p3 → ((((False ∧ ((True ∨ True) ∨ p5)) ∨ (p4 ∨ True)) → p1) ∨ (False ∨ p1))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_688595887104680823696807054004 : ((((p3 ∨ ((p1 ∨ (((p5 ∨ p1) → p4) → p1)) ∨ (((p5 ∧ p5) ∨ True) ∧ p3))) ∧ (p4 ∧ ((((p1 ∧ True) ∨ True) ∧ p3) ∨ True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61837809742993076722967729580 : ((p2 ∧ (((((((p4 ∨ ((True ∧ (p3 → (p4 ∨ p3))) ∧ (p1 → p2))) ∨ (p3 → p5)) ∨ True) ∧ (p2 → p3)) ∧ p1) ∨ p1) → p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49437291323858875230202565891 : (((((((((p2 ∧ ((p1 ∨ True) ∨ p4)) ∨ p3) ∧ p3) → ((p1 → p1) ∨ p4)) ∧ p3) → (p3 → p3)) ∨ p2) → ((True → p2) ∧ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41999991171745573370669236625 : ((((p1 → p2) ∧ (((p3 → p4) → (p5 ∨ ((p1 → (p2 ∨ p3)) → p2))) ∧ (False ∨ (p1 ∧ ((p2 → (p5 → p1)) ∧ p2))))) ∨ True) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148677932384598508652927097771 : (((((p1 ∧ (p1 ∨ p3)) ∧ p4) ∧ (p1 ∨ p1)) ∨ (True ∧ ((p2 ∧ p4) → (((False ∨ p2) ∨ p3) ∨ True)))) ∨ (((p1 ∨ False) ∨ False) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149932376845537337410869421079 : ((p3 ∨ ((True ∧ ((False → p5) ∨ p3)) → (p2 ∧ (p1 ∧ ((p2 ∧ ((p5 ∨ (p1 ∨ True)) ∨ p4)) → True))))) ∨ (False ∨ (True ∨ (p5 ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219495142864089500472129527466 : ((p5 ∨ ((p2 ∧ p5) ∨ p4)) → ((((p5 ∧ p5) ∨ p4) ∧ (((p3 ∧ (p4 ∨ (True ∧ (True ∧ p2)))) → True) → ((p4 ∨ p3) ∨ p5))) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h2
    -- One of the premise coincides with the conclusion.
    exact h2
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h7
      -- One of the premise coincides with the conclusion.
      exact h7
      -- Implications on the right can always be decomposed.
      intro h8
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h9 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h9
      -- Implications on the right can always be decomposed.
      intro h10
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147779165619258629498450683344 : ((((p5 → True) ∨ (True → (p1 ∨ (((p1 → p3) ∧ (p5 → (((p4 ∧ p1) ∧ p4) ∨ p1))) ∨ p1)))) → p2) ∨ (p2 ∨ (False ∨ (p5 → p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_124936990242065503640799935512 : ((((p2 ∨ False) ∨ (p2 → p4)) → (((True → (((p1 ∧ p2) ∧ (p2 → p1)) ∧ p1)) → (True ∨ ((p2 → p1) ∨ p3))) ∧ p4)) → (p1 ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_352850142870096772268521505105 : (p4 → ((p4 → p4) → (((p5 ∨ (p5 ∧ True)) → (p4 ∧ ((((False ∨ (p1 ∨ p4)) → ((p2 → p3) ∧ (p5 ∧ False))) ∨ p2) ∧ p3))) ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67705391890271785315531157236 : ((p1 → (p5 → (False ∧ (p1 → (((((True ∧ ((((False → True) → p4) ∧ (p4 ∧ p5)) ∧ p4)) ∧ p2) ∨ (p3 → p4)) → p3) → p2))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347612034353251649238690178641 : (p3 → (((True → False) ∨ (p4 ∨ p1)) ∨ ((False → (False ∧ p5)) → ((p5 ∨ p4) ∨ (((p5 ∨ (p2 → False)) ∧ (p5 ∧ p3)) ∨ (False ∨ True)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191693281046196230454519785629 : ((p5 ∧ (p5 → ((p1 ∨ False) ∨ ((p4 ∧ False) ∨ p5)))) ∨ (((p3 ∨ (p3 ∧ ((p3 → p1) → True))) ∧ (p1 → (p2 ∧ (p5 → p3)))) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



