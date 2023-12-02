variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193473660226277342369352556089 : (((p3 ∧ p3) ∨ (((True ∨ (p3 ∨ True)) → p2) ∨ False)) → (p2 ∨ ((p2 → (False ∨ (p4 → (p1 ∧ ((p5 ∨ True) ∨ p2))))) ∨ (True ∨ False)))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- False on the left can always be used.
      apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249231193015739441340650895248 : ((p4 ∨ p4) ∨ ((((p3 ∨ False) ∧ p5) → (((((False ∧ p2) ∨ (p5 ∧ (False → (p1 → True)))) ∧ p4) ∨ p5) ∨ ((p4 → False) ∧ p5))) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230327195756537701636487798937 : (((p2 ∨ True) ∧ p3) → (((p1 ∨ (p1 → (p4 ∨ p4))) ∧ (p1 ∨ (True ∧ (True ∧ ((p1 → p3) → ((p4 ∧ p5) ∧ (p1 ∨ p4))))))) ∨ True)) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_8187356773201942178891204002 : ((((True → ((False ∨ (False ∧ (True → ((p5 → (p5 → (p3 → False))) ∧ p5)))) ∧ ((((p4 → True) ∨ p2) → p3) → p1))) ∨ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309720431228991363005348054058 : (p2 ∨ ((p2 ∨ ((p1 ∨ (((((p2 → p3) ∨ (p5 → ((p1 → (False ∧ p1)) → p2))) ∧ p4) → p2) → p1)) ∨ p2)) → (p3 → (p5 ∨ p3)))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h2
      case inr h7 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h2
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117733309863418629958059964073 : ((p3 ∧ (p5 → (True ∧ (((p5 ∨ p3) ∨ True) ∧ (p1 ∨ ((((p5 ∧ (p2 ∨ True)) ∧ False) ∨ ((p1 ∨ p5) → False)) ∧ p1)))))) ∨ (False → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_620999795525196653727306086774 : (((((True → p4) → ((((p4 ∧ p2) ∨ p3) ∨ p3) → ((((True ∧ False) ∨ (p5 ∨ (p5 → (p3 ∨ False)))) ∨ (p2 ∧ p3)) → p2))) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60106165000940839382738053994 : (((p3 ∨ p2) → ((((p2 ∨ (p2 → p3)) ∨ (True ∨ p3)) ∧ False) ∨ ((p5 ∧ p4) ∨ (((p5 ∨ p2) ∧ (False ∧ (p1 ∧ p1))) ∨ True)))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51491924208313448804330827511 : ((((p4 ∧ (p3 → (p3 ∨ False))) ∨ ((((p1 → (p1 → (True → False))) ∧ p2) ∧ p3) ∧ True)) → ((p5 ∨ (p2 ∧ p1)) ∨ (p3 ∨ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245424248174493709524585707289 : ((p2 ∧ p4) ∨ ((((((((p2 ∧ p5) → (p5 ∨ p1)) ∧ False) ∧ p1) ∨ p2) ∨ p1) ∧ False) ∨ ((False ∧ ((p1 ∧ (True ∧ False)) → False)) → p5))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191644013253185498239704511714 : ((p4 ∧ ((p1 ∨ (p5 ∧ p1)) ∧ (p4 ∧ (p2 → True)))) ∨ (((p2 → ((p2 → True) → True)) ∨ p2) ∨ ((False ∨ ((False → True) ∨ p4)) → False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118736575421550615511876577479 : ((p5 ∨ ((((p4 ∨ p2) ∨ p1) ∨ ((p4 → (False ∨ p4)) ∨ p2)) ∧ ((p2 → ((True ∧ True) ∧ (p3 ∨ True))) ∨ (True → True)))) ∨ (p5 ∨ p4)) := by
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
  intro h1
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
theorem thm_5_vars_260255541879190177316977193551 : ((p2 → p3) → ((p1 ∨ p2) ∨ ((True → False) ∨ ((((False → (p1 ∨ (p4 ∧ True))) → (p3 ∨ p2)) → p4) ∨ (True ∨ (p2 ∧ (p4 → p1))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
theorem thm_5_vars_152812236427149670777173268914 : (((p1 ∨ p2) → (p5 ∨ (True → ((p3 ∨ ((p4 ∨ ((True ∧ p2) ∨ p5)) ∧ (p4 ∨ p1))) ∧ (p5 ∨ True))))) → (((True ∧ p2) → p1) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_86082369923621437501595750585 : (((p5 ∨ (p3 ∨ (p3 ∨ (True ∧ ((True ∨ p2) ∧ False))))) ∧ (((p2 → p4) ∨ (p5 ∨ p2)) ∧ (p3 ∧ (((p1 ∧ True) ∨ True) → False)))) → False) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h8 := h6.left
      let h9 := h6.right
      -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
      have h10 : ((p1 ∧ True) ∨ True) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h9, we can now drive its conclusion.
      let h11 := h9 h10
      -- False on the left can always be used.
      apply False.elim h11
    case inr h12 =>
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- Conjunctions on the left can always be decomposed.
        let h14 := h6.left
        let h15 := h6.right
        -- We want to use the implication h15 based on <expert-advice>. So we show its premise.
        have h16 : ((p1 ∧ True) ∨ True) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h15, we can now drive its conclusion.
        let h17 := h15 h16
        -- False on the left can always be used.
        apply False.elim h17
      case inr h18 =>
        -- Conjunctions on the left can always be decomposed.
        let h19 := h6.left
        let h20 := h6.right
        -- We want to use the implication h20 based on <expert-advice>. So we show its premise.
        have h21 : ((p1 ∧ True) ∨ True) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h20, we can now drive its conclusion.
        let h22 := h20 h21
        -- False on the left can always be used.
        apply False.elim h22
  case inr h23 =>
    -- Disjunctions on the left can always be decomposed.
    cases h23
    case inl h24 =>
      -- Conjunctions on the left can always be decomposed.
      let h25 := h3.left
      let h26 := h3.right
      -- Disjunctions on the left can always be decomposed.
      cases h25
      case inl h27 =>
        -- Conjunctions on the left can always be decomposed.
        let h28 := h26.left
        let h29 := h26.right
        -- We want to use the implication h29 based on <expert-advice>. So we show its premise.
        have h30 : ((p1 ∧ True) ∨ True) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h29, we can now drive its conclusion.
        let h31 := h29 h30
        -- False on the left can always be used.
        apply False.elim h31
      case inr h32 =>
        -- Disjunctions on the left can always be decomposed.
        cases h32
        case inl h33 =>
          -- Conjunctions on the left can always be decomposed.
          let h34 := h26.left
          let h35 := h26.right
          -- We want to use the implication h35 based on <expert-advice>. So we show its premise.
          have h36 : ((p1 ∧ True) ∨ True) := by
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h35, we can now drive its conclusion.
          let h37 := h35 h36
          -- False on the left can always be used.
          apply False.elim h37
        case inr h38 =>
          -- Conjunctions on the left can always be decomposed.
          let h39 := h26.left
          let h40 := h26.right
          -- We want to use the implication h40 based on <expert-advice>. So we show its premise.
          have h41 : ((p1 ∧ True) ∨ True) := by
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h40, we can now drive its conclusion.
          let h42 := h40 h41
          -- False on the left can always be used.
          apply False.elim h42
    case inr h43 =>
      -- Disjunctions on the left can always be decomposed.
      cases h43
      case inl h44 =>
        -- Conjunctions on the left can always be decomposed.
        let h45 := h3.left
        let h46 := h3.right
        -- Disjunctions on the left can always be decomposed.
        cases h45
        case inl h47 =>
          -- Conjunctions on the left can always be decomposed.
          let h48 := h46.left
          let h49 := h46.right
          -- We want to use the implication h49 based on <expert-advice>. So we show its premise.
          have h50 : ((p1 ∧ True) ∨ True) := by
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h49, we can now drive its conclusion.
          let h51 := h49 h50
          -- False on the left can always be used.
          apply False.elim h51
        case inr h52 =>
          -- Disjunctions on the left can always be decomposed.
          cases h52
          case inl h53 =>
            -- Conjunctions on the left can always be decomposed.
            let h54 := h46.left
            let h55 := h46.right
            -- We want to use the implication h55 based on <expert-advice>. So we show its premise.
            have h56 : ((p1 ∧ True) ∨ True) := by
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h55, we can now drive its conclusion.
            let h57 := h55 h56
            -- False on the left can always be used.
            apply False.elim h57
          case inr h58 =>
            -- Conjunctions on the left can always be decomposed.
            let h59 := h46.left
            let h60 := h46.right
            -- We want to use the implication h60 based on <expert-advice>. So we show its premise.
            have h61 : ((p1 ∧ True) ∨ True) := by
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h60, we can now drive its conclusion.
            let h62 := h60 h61
            -- False on the left can always be used.
            apply False.elim h62
      case inr h63 =>
        -- Conjunctions on the left can always be decomposed.
        let h64 := h63.left
        let h65 := h63.right
        -- Conjunctions on the left can always be decomposed.
        let h66 := h65.left
        let h67 := h65.right
        -- Disjunctions on the left can always be decomposed.
        cases h66
        case inl h68 =>
          -- False on the left can always be used.
          apply False.elim h67
        case inr h69 =>
          -- False on the left can always be used.
          apply False.elim h67



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62367483184664448411212744075 : ((p3 ∧ (((p3 ∧ ((p5 ∨ ((True ∨ p2) → True)) ∧ ((p2 → (p1 ∧ p2)) ∨ p1))) ∧ False) ∨ (((p1 ∨ p4) → p3) ∨ (False ∧ True)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_141296839144732568276188650384 : (((p1 ∧ (True → (p5 ∧ False))) ∧ ((p4 ∧ p5) → (False → ((p3 ∨ (p3 → p3)) ∨ (p4 → (p4 → (False ∨ False))))))) → ((p1 ∧ True) ∧ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h4
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h6 := h1.left
  let h7 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
  have h10 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h9, we can now drive its conclusion.
  let h11 := h9 h10
  -- We need to get the left conjuct of h11 based on <expert-advice>.
  let h12 := h11.left
  -- One of the premise coincides with the conclusion.
  exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156931694383511943469309038735 : (((((p2 ∧ (((p3 ∨ ((p1 ∧ p3) → p2)) ∧ p1) → p3)) → (False ∨ p1)) ∧ (False ∨ p2)) ∨ p1) ∨ (False ∨ ((p5 ∧ False) → (p4 ∨ p4)))) := by
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
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_689582088658688048205470002670 : ((((((p4 ∧ p4) ∧ (p3 → (p2 ∧ p3))) ∧ (((False ∧ True) ∧ p2) ∨ (p1 ∧ True))) ∨ (((p2 ∧ (p1 ∨ False)) → (True ∧ p5)) → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112249572059605706160332377122 : (((p3 ∨ (p4 → (((p5 → ((((p1 ∨ p4) ∧ p5) ∨ ((p5 ∨ (p3 ∨ p2)) → p1)) ∧ (p2 ∧ p4))) ∨ p1) ∨ False))) ∨ p5) ∨ (p5 → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111967457806524516235980794952 : ((((((p1 ∨ (True → False)) ∨ p2) → p5) ∧ (((p2 → True) ∨ p4) → ((p4 ∨ False) ∨ ((p2 ∧ False) ∨ (p4 ∧ p4))))) ∨ p1) ∨ (p3 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305307545130900503619087240271 : (p1 ∨ ((((True ∨ p2) → p5) → (False ∨ ((p1 → (True ∨ p2)) → ((True ∧ (p2 ∧ p2)) ∨ p3)))) ∨ (((p3 → True) ∧ p2) ∨ (True ∨ p4)))) := by
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
theorem thm_5_vars_196438336012596039639761029744 : ((False → (((p4 ∨ True) → p4) → (p4 ∨ p1))) ∧ (((p2 → (False → p5)) → ((((False ∨ ((p1 → True) ∨ p1)) → p4) ∨ True) → p1)) → p1)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : (p2 → (False → p5)) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- Implications on the right can always be decomposed.
    intro h6
    -- False on the left can always be used.
    apply False.elim h6
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h7 := h3 h4
  -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
  have h8 : (((False ∨ ((p1 → True) ∨ p1)) → p4) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h7, we can now drive its conclusion.
  let h9 := h7 h8
  -- One of the premise coincides with the conclusion.
  exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117240933446786683913365781774 : ((True ∧ (False ∨ ((((p5 ∨ ((((True → p4) ∨ p5) → ((((p1 → p2) ∨ p3) → p4) ∧ p5)) ∨ True)) ∧ p4) ∧ p2) ∧ p5))) ∨ (p4 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_801454786963712225342163977035 : (((p2 → (((p1 ∧ p3) → (p2 ∨ (((p5 ∧ p2) ∧ p2) → p3))) → ((((True ∧ p5) ∨ p2) → p3) ∨ (p4 ∨ ((p4 ∧ False) ∨ True))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_739086063085414725391124568910 : ((((p3 ∧ p4) ∨ (True → (p3 ∧ (((p5 ∨ (p4 ∧ p2)) ∨ p4) ∨ (p5 → (((False ∨ ((True ∧ p5) ∧ True)) → p4) → (p2 ∧ True))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_721258608905125075168576195948 : (((((p3 ∨ p1) → (p3 → False)) → ((p3 → (p1 ∧ ((p1 ∨ ((p4 → p5) → (((p5 ∨ p3) ∧ p4) ∧ p3))) ∧ (p1 ∧ p5)))) ∨ p5)) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : (p3 ∨ p1) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h5 : p3 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h6 := h4 h5
  -- False on the left can always be used.
  apply False.elim h6
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h7 : (p3 ∨ p1) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h8 := h1 h7
  -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
  have h9 : p3 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h8, we can now drive its conclusion.
  let h10 := h8 h9
  -- False on the left can always be used.
  apply False.elim h10
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h11 : (p3 ∨ p1) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h12 := h1 h11
  -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
  have h13 : p3 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h12, we can now drive its conclusion.
  let h14 := h12 h13
  -- False on the left can always be used.
  apply False.elim h14
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h15 : (p3 ∨ p1) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h16 := h1 h15
  -- We want to use the implication h16 based on <expert-advice>. So we show its premise.
  have h17 : p3 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h16, we can now drive its conclusion.
  let h18 := h16 h17
  -- False on the left can always be used.
  apply False.elim h18
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310288541455189701453687854171 : (p2 ∨ ((((p1 → (((p3 → p2) ∧ p3) → False)) → p3) ∧ p1) ∨ ((((True ∧ (((True ∨ p2) ∨ False) ∧ (True ∧ p5))) ∧ p5) → True) ∨ p3))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_247905144708870510799319156009 : ((p1 ∨ p3) ∨ (((False ∧ (((p1 → ((p3 → (p4 ∧ p3)) → p4)) → p1) ∨ p3)) ∧ ((True ∨ p5) ∧ (False ∨ (p2 ∧ p5)))) ∨ (p3 → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_645026732959701887781376952975 : ((((p3 ∨ ((((p2 ∧ (False → p3)) ∧ (p4 → (((p3 ∨ (((p3 ∨ p5) → True) → (p3 ∧ p3))) ∧ p2) ∧ p3))) → p4) ∧ p5)) → p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319187018289506425783386072649 : (p4 ∨ ((p5 ∨ (((p1 → ((False → (False ∧ p2)) → (p2 ∧ (p3 ∧ (p1 ∧ p2))))) → p4) ∨ p5)) ∨ (p3 → (((True → p1) → p1) ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190728519714884755432788357013 : ((((p4 → p3) ∧ ((p2 ∧ p5) ∨ p3)) ∧ (p1 ∧ p5)) ∨ ((True ∧ (p2 ∨ p2)) ∨ (p5 → ((p5 ∧ (p5 ∧ ((False ∧ p5) ∨ p1))) ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_613850703124297707912310469499 : ((((((False ∨ (((((True ∧ p4) → p3) → p1) ∨ (((p3 ∧ (p2 ∨ p3)) ∨ p5) ∨ True)) ∨ p5)) ∧ p4) ∨ (p3 → (True → p4))) ∨ True) ∨ False) ∧ True) := by
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
theorem thm_5_vars_217077683610083268312124246964 : ((((p5 → p2) ∧ p4) ∨ False) → ((((((p1 ∨ p5) → False) → (p2 ∨ p1)) ∨ p1) ∨ (((True → (p1 ∨ False)) ∧ p3) → (p1 → False))) ∨ p4)) := by
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
    exact h4
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53144969411697401598559780819 : ((((p5 → ((((p4 → False) → True) ∨ (False → False)) → p4)) ∧ True) ∨ (((p4 → ((p5 ∧ (p5 ∨ False)) ∨ p2)) ∨ p2) → (True ∨ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_18769556475070754764548695677 : ((((p1 ∨ ((p5 ∨ (p2 ∧ p2)) ∧ (((p2 → p3) ∧ (True → (False → p4))) → p3))) ∨ True) ∨ (((p4 ∨ (p3 → True)) ∨ p5) ∨ True)) ∧ True) := by
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
theorem thm_5_vars_141972098794301090564042218864 : (((p2 ∨ True) → ((True → (((p3 ∧ (p4 ∨ (p4 → (((p4 ∧ p1) → p2) ∧ p1)))) ∨ (p4 → p1)) ∧ False)) ∨ p4)) → ((p4 → True) → p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : (p2 ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h6 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h7 := h5 h6
    -- We need to get the right conjuct of h7 based on <expert-advice>.
    let h8 := h7.right
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- One of the premise coincides with the conclusion.
    exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_252628539979558731189451126380 : ((p5 → p4) ∨ ((((((True ∧ (p5 ∧ (True → (True → ((p3 ∧ (True ∧ p5)) ∨ (p1 ∧ p2)))))) → (True → True)) → p2) ∧ p5) ∧ True) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317059166133061560787909761043 : (p3 ∨ (p4 → ((p1 ∧ (p5 → ((p2 ∨ (p3 ∨ p2)) ∧ p5))) ∨ ((((p4 ∨ (True ∧ p4)) ∧ p2) ∨ False) → ((p3 ∧ (True → p5)) → p3))))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h9 =>
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- One of the premise coincides with the conclusion.
      exact h4
  case inr h13 =>
    -- False on the left can always be used.
    apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322480867335591454731811326211 : (p5 ∨ (((p5 → True) ∧ (False ∨ (((p1 ∧ ((p4 ∧ p2) ∨ (p2 → (p3 ∧ (False ∧ ((True → p5) → True)))))) ∧ (p4 ∧ p5)) ∧ False))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117044505722039968512681334457 : (((p4 ∨ True) → (((True ∨ (p4 → (p1 ∧ p5))) → (p2 → (((p2 ∧ (((p4 ∨ p4) → True) → p2)) ∧ True) ∧ p4))) → False)) ∨ (p2 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206384252729170088619468749900 : ((p3 ∨ (((p4 ∨ p5) → p5) ∧ False)) ∨ (p4 ∨ ((((True ∧ (p3 → (False ∨ p2))) ∨ True) ∨ (p5 ∧ p5)) ∨ ((p1 ∨ p2) ∨ (True ∨ p5))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299444491002718693678994193540 : (False ∨ ((p2 ∨ ((((((True → p2) → True) ∨ (True → (False ∧ True))) ∧ (p5 → (((p4 ∨ False) ∨ False) ∨ (True ∨ p2)))) → p1) ∧ p4)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_182108933637212561982017376888 : (((p3 ∨ ((p1 ∧ (p1 ∧ (p1 ∨ (p2 ∨ p4)))) ∨ True)) ∨ p5) ∧ (p1 → ((((p5 ∨ p4) ∨ (p2 → ((False → p3) ∧ False))) ∧ p3) ∨ p1))) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68199425136164096458518689764 : ((p3 → (((p1 → p4) → (p5 ∧ ((((p5 ∨ ((p1 → p5) ∨ (p1 → (p3 ∧ (p2 → p1))))) ∨ (p1 ∨ p3)) → p2) ∨ p2))) ∨ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55386422404964221592468803286 : (((((p2 ∨ p5) → (p1 ∧ p5)) ∧ p4) → (((p1 ∧ (True ∨ p1)) ∧ ((((p5 ∧ (p5 ∨ p5)) → True) → p1) ∧ p4)) ∧ (p5 ∨ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_785582208859400914273441868984 : (((p4 ∨ ((p5 → ((p3 ∧ True) ∧ ((p1 ∧ ((p2 ∨ ((p1 ∨ ((True → p1) ∨ ((p2 → False) ∨ p3))) → p1)) ∨ p2)) ∨ p2))) ∨ True)) ∨ False) ∧ True) := by
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
theorem thm_5_vars_158643997286555582106151943915 : ((p1 ∧ (((((p5 → True) ∧ p1) ∨ (p5 ∨ (p1 → False))) ∨ (p2 ∧ p1)) → ((p5 → p4) ∨ p5))) ∨ ((p2 → (p3 → (p1 ∨ False))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63072444312539556421801311051 : ((p5 ∧ ((((False ∧ p5) ∨ ((p3 ∨ p1) ∧ (p2 ∧ ((p1 ∧ p3) ∧ (((((p4 ∧ p2) ∨ p4) ∧ p4) ∨ p5) ∨ p1))))) ∧ p2) ∨ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110865409801114213730069260921 : (((((((((p4 ∧ p2) → (p4 ∧ False)) → ((p5 → ((p2 → p2) ∧ (p4 ∨ p1))) ∨ p1)) ∧ p4) ∨ False) → False) → False) ∧ p3) ∨ (False → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42988218733155610352039869665 : (((p5 → (p2 ∧ (((p1 ∨ (p3 ∨ (((p2 ∨ True) ∧ (p2 → p3)) → p3))) → p3) ∧ ((p2 ∧ True) ∨ ((True → p3) ∧ p1))))) ∨ True) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149422454370037002663601048647 : ((True ∧ ((p2 ∧ p3) ∨ (((((((p4 → ((p2 → True) → True)) ∧ p3) ∧ True) → p3) → p1) → p1) → p2))) ∨ (False ∨ (p4 → (True ∧ p4)))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_759151979741668480158195221112 : (((p2 ∧ ((p3 → ((p1 → p4) ∧ (((p1 ∨ p5) → (((p5 ∧ (False ∧ (p3 → True))) ∨ p5) ∧ (p1 → p3))) ∨ p2))) ∧ (False ∨ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200084290994373805661085704892 : ((((p3 ∨ p3) ∨ p5) ∧ (True → (True ∧ False))) → (p2 ∨ ((p3 → (p4 ∧ (((True ∧ ((False ∧ p5) ∧ (p4 ∨ p1))) ∨ p2) ∧ False))) ∧ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h6 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h7 := h3 h6
      -- We need to get the right conjuct of h7 based on <expert-advice>.
      let h8 := h7.right
      -- False on the left can always be used.
      apply False.elim h8
    case inr h9 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h10 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h11 := h3 h10
      -- We need to get the right conjuct of h11 based on <expert-advice>.
      let h12 := h11.right
      -- False on the left can always be used.
      apply False.elim h12
  case inr h13 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h14 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h15 := h3 h14
    -- We need to get the right conjuct of h15 based on <expert-advice>.
    let h16 := h15.right
    -- False on the left can always be used.
    apply False.elim h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_355850114641279247957346967905 : (p5 → (((p3 ∧ (((((((p3 ∨ True) ∧ False) ∨ p3) ∨ p2) ∧ ((True ∨ p1) → p2)) ∧ p3) ∨ p3)) ∨ (p1 → p2)) ∨ (p1 → (p4 ∨ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_28064982059941555873929457463 : (((p4 → p3) → ((p1 → ((((((p3 → True) ∧ False) → (p1 → p3)) ∨ p1) → False) ∧ True)) ∨ (True ∧ ((p5 → (p1 ∨ p3)) → True)))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341757286974028310196071818272 : (p2 → ((p1 ∨ (p4 ∧ (p5 ∨ ((p2 → (True ∧ p5)) → ((((False → (p4 → (p3 → p2))) ∧ False) ∨ p3) → (p1 ∨ p4)))))) ∨ (True ∨ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_612564435375737013251265167880 : (((((((((p1 ∨ ((False ∨ (True ∨ p3)) ∨ (p4 ∧ False))) → True) ∧ True) ∧ (p4 ∧ (p3 → (p2 ∧ p4)))) → False) ∨ (p1 ∨ p1)) ∨ True) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_213274220999405901539480404027 : ((((True → False) → p3) ∧ p1) ∨ ((p2 → ((p3 ∨ p5) ∨ (p5 ∧ p1))) ∨ ((((p5 ∧ (p3 ∨ False)) ∧ p2) ∨ ((True ∨ p3) ∨ p2)) ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_860149958091395777639345484819 : ((((((True ∨ p1) ∧ ((((p2 ∨ (p3 → p5)) → p1) ∨ False) ∨ (p3 ∧ (p5 ∨ ((p1 → p5) → (p2 → True)))))) ∨ (False ∨ True)) → False) → p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((True ∨ p1) ∧ ((((p2 ∨ (p3 → p5)) → p1) ∨ False) ∨ (p3 ∧ (p5 ∨ ((p1 → p5) → (p2 → True)))))) ∨ (False ∨ True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_943664298820324990084244531134 : ((((False ∨ (True → (p1 ∧ p2))) ∧ ((p4 → ((p4 → (p2 → ((False ∧ False) ∨ (p1 ∧ p4)))) ∧ p2)) ∨ ((p1 → (True → p3)) ∧ p3))) → p1) ∧ True) := by
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
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h7 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h8 := h5 h7
      -- We need to get the left conjuct of h8 based on <expert-advice>.
      let h9 := h8.left
      -- One of the premise coincides with the conclusion.
      exact h9
    case inr h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h13 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h14 := h5 h13
      -- We need to get the left conjuct of h14 based on <expert-advice>.
      let h15 := h14.left
      -- One of the premise coincides with the conclusion.
      exact h15
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53612121381026682032712492514 : (((((p2 ∧ True) ∨ (p5 ∨ (p5 ∧ False))) ∨ (p3 → True)) ∧ (p5 ∧ (((p1 ∧ (p2 ∧ p3)) ∧ ((p2 → (p4 ∧ False)) ∨ True)) → True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147466186528413314510491257624 : (((False ∧ (((False ∧ ((False ∧ p2) → p5)) ∧ (((True ∨ p3) → p2) → ((p1 ∨ True) ∨ p3))) ∧ p1)) ∨ p1) ∨ (p1 → ((p1 ∨ p4) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60590571947675756755865248467 : ((True ∧ ((p5 ∧ ((p3 ∨ p1) → ((p3 → p4) ∨ (((p3 → p5) ∧ (p5 ∧ (True ∨ (p4 ∧ p1)))) ∧ ((False ∧ p5) → p2))))) → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_706365009775864146848299507754 : ((((True ∨ (p2 ∧ ((p4 ∨ (p5 ∧ p2)) → False))) ∧ (((((p4 → p1) ∧ (((p5 → False) → p4) ∨ True)) ∨ (False ∧ False)) → p5) ∨ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308905379762909921766693245904 : (p2 ∨ ((((p4 ∧ (((True ∨ (p1 ∧ ((p3 → ((p5 → p5) ∨ p4)) ∨ False))) → p3) → False)) ∧ (True ∨ p5)) ∧ ((False → p3) → p3)) → p2)) := by
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
  let h6 := h4.left
  let h7 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h8 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h9 : (False → p3) := by
      -- Implications on the right can always be decomposed.
      intro h10
      -- False on the left can always be used.
      apply False.elim h10
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h11 := h3 h9
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h12 : ((True ∨ (p1 ∧ ((p3 → ((p5 → p5) ∨ p4)) ∨ False))) → p3) := by
      -- Implications on the right can always be decomposed.
      intro h13
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h14 =>
        -- One of the premise coincides with the conclusion.
        exact h11
      case inr h15 =>
        -- Conjunctions on the left can always be decomposed.
        let h16 := h15.left
        let h17 := h15.right
        -- Disjunctions on the left can always be decomposed.
        cases h17
        case inl h18 =>
          -- One of the premise coincides with the conclusion.
          exact h11
        case inr h19 =>
          -- False on the left can always be used.
          apply False.elim h19
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h20 := h7 h12
    -- False on the left can always be used.
    apply False.elim h20
  case inr h21 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h22 : (False → p3) := by
      -- Implications on the right can always be decomposed.
      intro h23
      -- False on the left can always be used.
      apply False.elim h23
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h24 := h3 h22
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h25 : ((True ∨ (p1 ∧ ((p3 → ((p5 → p5) ∨ p4)) ∨ False))) → p3) := by
      -- Implications on the right can always be decomposed.
      intro h26
      -- Disjunctions on the left can always be decomposed.
      cases h26
      case inl h27 =>
        -- One of the premise coincides with the conclusion.
        exact h24
      case inr h28 =>
        -- Conjunctions on the left can always be decomposed.
        let h29 := h28.left
        let h30 := h28.right
        -- Disjunctions on the left can always be decomposed.
        cases h30
        case inl h31 =>
          -- One of the premise coincides with the conclusion.
          exact h24
        case inr h32 =>
          -- False on the left can always be used.
          apply False.elim h32
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h33 := h7 h25
    -- False on the left can always be used.
    apply False.elim h33



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147862815856427497892069498604 : (((p1 → ((p4 ∧ False) → (p5 → ((p5 ∨ True) → ((False ∧ (((p4 ∧ True) → p1) → p1)) → p4))))) → p5) ∨ (p4 → (p4 ∨ (p3 ∧ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_153157360653244926002484445997 : ((p5 ∧ (((p4 ∨ ((((p4 → p3) ∨ (False ∨ True)) ∨ True) → True)) ∨ (p5 → (False ∧ True))) ∧ (p5 ∨ False))) → (p3 → ((p1 ∨ p2) ∨ p3))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h2
      case inr h10 =>
        -- False on the left can always be used.
        apply False.elim h10
    case inr h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h2
      case inr h13 =>
        -- False on the left can always be used.
        apply False.elim h13
  case inr h14 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h15 =>
      -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
      have h16 : p5 := by
        -- One of the premise coincides with the conclusion.
        exact h15
      -- We have shown the premise of h14, we can now drive its conclusion.
      let h17 := h14 h16
      -- We need to get the left conjuct of h17 based on <expert-advice>.
      let h18 := h17.left
      -- False on the left can always be used.
      apply False.elim h18
    case inr h19 =>
      -- False on the left can always be used.
      apply False.elim h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51214804292948861749595128607 : ((((p3 ∨ (True ∧ ((p3 → False) ∨ (p3 → p1)))) → (((True → (p4 ∨ p3)) ∨ p3) ∧ p5)) ∨ (p5 → ((p3 ∨ (False → p5)) ∨ True))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41074870006642290504404776952 : ((((p1 → ((((p4 ∨ True) → (p3 ∨ (p2 ∧ (p2 → p4)))) → (True ∨ ((False ∧ p2) → p2))) ∨ (p5 ∧ True))) → (p3 ∧ p2)) ∨ True) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41753191657741189095278147185 : (((((p5 ∧ (p5 → p2)) ∨ p4) ∨ (True ∧ (((((p4 ∧ p5) ∧ p3) ∨ p4) ∨ (p4 → ((True → p4) ∨ (False → True)))) ∨ p2))) ∨ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199682359197176502719683683832 : ((((p5 ∧ False) → (p5 ∧ (p3 ∨ p5))) → False) → ((False ∧ (p4 ∨ ((False ∧ p1) ∧ (p3 ∧ (p1 → p5))))) ∨ ((p2 ∧ (True ∧ p1)) ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p5 ∧ False) → (p5 ∧ (p3 ∨ p5))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- False on the left can always be used.
    apply False.elim h5
    -- Conjunctions on the left can always be decomposed.
    let h6 := h3.left
    let h7 := h3.right
    -- False on the left can always be used.
    apply False.elim h7
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h8 := h1 h2
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174717441076549549476353334866 : (((p4 → (True ∨ p3)) ∨ ((p5 ∧ (p1 ∨ p1)) ∧ ((p1 ∨ (p2 ∨ False)) ∨ p3))) → (((p2 → False) ∨ (p1 ∧ (p5 ∧ p4))) ∨ (True ∨ p5))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h9 =>
        -- Disjunctions on the left can always be decomposed.
        cases h9
        case inl h10 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h11 =>
          -- Disjunctions on the left can always be decomposed.
          cases h11
          case inl h12 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h13 =>
            -- False on the left can always be used.
            apply False.elim h13
      case inr h14 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h15 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h16 =>
        -- Disjunctions on the left can always be decomposed.
        cases h16
        case inl h17 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h18 =>
          -- Disjunctions on the left can always be decomposed.
          cases h18
          case inl h19 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h20 =>
            -- False on the left can always be used.
            apply False.elim h20
      case inr h21 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173745419286724392915853585225 : ((((False ∨ ((p3 ∨ (p1 ∧ p1)) ∧ p2)) ∨ (p2 ∨ (p1 ∨ (False → p3)))) ∨ p4) → (((p2 ∨ True) ∧ ((p3 → (False ∧ p4)) ∨ p2)) ∨ True)) := by
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
        -- False on the left can always be used.
        apply False.elim h4
      case inr h5 =>
        -- Conjunctions on the left can always be decomposed.
        let h6 := h5.left
        let h7 := h5.right
        -- Disjunctions on the left can always be decomposed.
        cases h6
        case inl h8 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h9 =>
          -- Conjunctions on the left can always be decomposed.
          let h10 := h9.left
          let h11 := h9.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
    case inr h12 =>
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h14 =>
        -- Disjunctions on the left can always be decomposed.
        cases h14
        case inl h15 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h16 =>
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
theorem thm_5_vars_355610838810885349063545243312 : (p5 → (((p4 → p5) → (((False → ((False → ((p2 ∧ p3) ∨ (p5 ∨ ((p5 ∨ False) ∨ (p4 → p3))))) → p5)) ∨ False) → p2)) ∨ (p5 ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136298455334464723330332517320 : (((p1 → ((p3 ∨ p1) ∨ (True → True))) → ((p5 ∧ (p1 → True)) ∧ (False ∧ ((p4 ∨ ((False → p3) ∧ True)) ∧ p1)))) ∨ ((p1 → False) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119254443744200116825241563782 : ((p2 → (p3 ∨ (p1 ∨ ((p1 → False) ∨ ((True → p1) ∨ ((False ∨ True) ∨ (((False → p4) ∧ ((p2 ∨ p1) → p4)) ∧ p4))))))) ∨ (p4 → False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_114436951163481765250719658091 : (((p3 ∨ ((False ∧ ((p4 → p2) → (((p1 ∧ True) ∨ p5) ∧ p3))) ∧ (p4 ∧ (p3 ∧ p4)))) ∨ ((p5 ∧ p5) → (p2 → True))) ∨ (p1 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136498586909326572020474447802 : ((((p1 → True) → False) ∧ ((p5 → True) → (((False ∧ False) ∨ p5) ∨ (p5 → ((p4 ∧ False) ∧ (p5 ∨ (False ∧ p2))))))) ∨ (p4 ∨ (True ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_626768489186976360168196667184 : ((((p5 → ((p1 → ((p3 ∧ False) ∨ (((p5 → (p4 ∨ (((p4 ∨ p3) ∨ (True ∨ True)) → p1))) ∧ p2) → p3))) → (p2 ∧ p2))) ∨ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52530997636539697879821643001 : (((((p2 ∨ (p5 ∧ (p2 ∧ True))) ∨ (((True → p4) ∧ False) ∧ False)) ∨ False) ∨ ((True ∨ p3) → (((True → True) ∧ (p4 → p4)) ∨ p1))) ∨ p1) := by
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
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
    -- Implications on the right can always be decomposed.
    intro h4
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h6
    -- True on the right can always be proven directly.
    apply True.intro
    -- Implications on the right can always be decomposed.
    intro h7
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46989183292016336849058239400 : ((((((p5 ∨ ((p3 → p3) → (False → ((p5 → p3) ∧ p4)))) ∧ p1) ∨ (p3 ∨ (p4 ∧ ((p4 ∧ False) → p2)))) → p3) ∨ (p5 ∧ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47493404907829284754666351364 : (((False ∨ (p1 → ((((p3 ∧ (((p5 ∨ False) → p1) ∨ (p1 ∧ (True ∨ p5)))) ∧ p1) → (p1 ∧ (p4 ∧ True))) ∨ p2))) ∨ (True ∨ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_327009143712213185269015571183 : (True → (((False ∨ ((((p3 ∨ p5) → True) → (p3 → ((p2 ∨ (p2 ∧ p3)) ∧ p2))) ∧ True)) ∨ (p2 ∨ ((p5 ∧ p2) → (p3 → p5)))) ∨ False)) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199804084516879701458974499666 : ((((p1 ∧ (p2 → False)) ∨ p3) ∧ (p1 ∧ p2)) → (p2 ∧ (p5 ∨ (((False ∨ ((True → p4) → (((p4 ∧ p2) → p4) ∧ p2))) → False) ∨ p1)))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h3.left
    let h8 := h3.right
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h3.left
    let h11 := h3.right
    -- One of the premise coincides with the conclusion.
    exact h11
  -- Conjunctions on the left can always be decomposed.
  let h12 := h1.left
  let h13 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h12
  case inl h14 =>
    -- Conjunctions on the left can always be decomposed.
    let h15 := h14.left
    let h16 := h14.right
    -- Conjunctions on the left can always be decomposed.
    let h17 := h13.left
    let h18 := h13.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h17
  case inr h19 =>
    -- Conjunctions on the left can always be decomposed.
    let h20 := h13.left
    let h21 := h13.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h20



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_783159531586560213394981313558 : (((p3 ∨ ((((p1 → (((((p1 ∨ p3) → (False ∧ p2)) ∨ (p5 → p1)) ∨ (False ∨ p3)) ∨ False)) → p2) ∧ p2) ∨ ((p1 ∨ p3) → True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_108169640605305891385491277195 : (((p1 → p4) → (((p3 ∧ p2) ∨ (True → ((p3 ∨ True) ∧ p3))) → ((((p5 ∧ False) ∧ p1) → (p2 ∨ (True ∧ True))) ∧ p3))) ∧ (False → p5)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- False on the left can always be used.
  apply False.elim h7
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- One of the premise coincides with the conclusion.
    exact h9
  case inr h11 =>
    -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
    have h12 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h11, we can now drive its conclusion.
    let h13 := h11 h12
    -- We need to get the right conjuct of h13 based on <expert-advice>.
    let h14 := h13.right
    -- One of the premise coincides with the conclusion.
    exact h14
  -- Implications on the right can always be decomposed.
  intro h15
  -- False on the left can always be used.
  apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157165637248545569704978085548 : (((((((p1 ∧ False) ∨ (((p1 → (p1 ∨ False)) ∧ True) ∧ (p4 ∧ p1))) ∨ p1) ∧ p4) → False) → p4) ∨ ((True ∨ False) ∨ ((p2 ∨ p2) ∧ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_893599073411172038699121854185 : ((((((p2 → p4) → p5) ∧ (((((p4 ∧ (p2 ∨ (p3 ∨ p3))) → True) ∧ False) → p2) ∧ (True ∨ (p1 → p4)))) ∧ (p2 ∧ (p5 ∨ p4))) → p5) ∧ True) := by
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
  let h6 := h5.left
  let h7 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h3.left
    let h10 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- One of the premise coincides with the conclusion.
      exact h11
    case inr h12 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h13 : (p2 → p4) := by
        -- Implications on the right can always be decomposed.
        intro h14
        -- One of the premise coincides with the conclusion.
        exact h12
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h15 := h4 h13
      -- One of the premise coincides with the conclusion.
      exact h15
  case inr h16 =>
    -- Conjunctions on the left can always be decomposed.
    let h17 := h3.left
    let h18 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h18
    case inl h19 =>
      -- One of the premise coincides with the conclusion.
      exact h19
    case inr h20 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h21 : (p2 → p4) := by
        -- Implications on the right can always be decomposed.
        intro h22
        -- One of the premise coincides with the conclusion.
        exact h20
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h23 := h4 h21
      -- One of the premise coincides with the conclusion.
      exact h23
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118476319726792170849262068732 : ((p3 ∨ ((((False → (p1 ∨ ((((p4 ∨ p5) ∧ p2) ∨ False) → (p1 → (p4 ∧ p3))))) → p3) ∨ (p2 ∧ p2)) ∧ (False ∨ p2))) ∨ (p2 → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_647955247601363345502721131115 : ((((((p1 ∨ (p5 ∨ ((p4 ∧ (True → ((p3 → p1) ∨ p5))) ∧ (p1 ∧ (True ∨ (p3 ∨ p2)))))) ∨ (p5 → True)) ∧ True) ∧ (p2 ∧ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_913791910149530474248784202472 : ((((((p5 ∨ (p5 ∧ (((p4 ∧ (p3 ∧ p2)) → p3) → (p5 → True)))) → False) ∧ p5) ∧ (((((p2 ∧ p5) ∨ p3) → p3) ∧ p1) ∨ p3)) → False) ∧ True) := by
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
  cases h3
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h9 : (p5 ∨ (p5 ∧ (((p4 ∧ (p3 ∧ p2)) → p3) → (p5 → True)))) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h5
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h10 := h4 h9
    -- False on the left can always be used.
    apply False.elim h10
  case inr h11 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h12 : (p5 ∨ (p5 ∧ (((p4 ∧ (p3 ∧ p2)) → p3) → (p5 → True)))) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h5
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h13 := h4 h12
    -- False on the left can always be used.
    apply False.elim h13
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_254413829986247882310531704858 : ((p2 ∧ p5) → (((False ∧ p3) ∧ (((((p5 ∧ p2) ∧ p1) → p5) ∧ True) ∧ False)) ∨ ((p1 ∧ p1) ∨ ((((True → True) ∧ p3) ∧ p3) ∨ p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44620911436752298407314685011 : (((((p1 → (p3 ∨ (True ∨ p2))) ∨ False) ∧ (((p1 ∧ p4) ∨ ((True ∧ p3) ∨ p3)) ∨ ((p3 ∨ (p4 → (p3 ∧ p1))) ∧ True))) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172719854065172050113294355076 : (((p5 ∨ p4) ∨ ((p3 ∨ (p3 → p2)) ∨ ((((p5 → p1) ∨ p5) ∧ p1) ∨ p3))) ∨ ((p5 → (((p2 ∨ (True → p4)) ∨ p2) ∨ p5)) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_909021218883946685896816596047 : ((((((p1 → False) ∨ (p2 → ((False ∨ (p2 ∨ True)) ∨ (p4 → False)))) → ((p2 ∨ p1) ∧ False)) ∧ ((False → (p2 ∧ p1)) → (p3 → p5))) → p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : ((p1 → False) ∨ (p2 → ((False ∨ (p2 ∨ True)) ∨ (p4 → False)))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h4
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- False on the left can always be used.
  apply False.elim h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_88291725131304701019580549198 : (((p1 → (p5 ∧ (p2 → True))) ∧ ((((p2 → p5) → ((p5 → True) ∧ p4)) ∧ (p5 ∨ ((((True → True) ∨ p4) ∨ p3) ∧ p1))) ∧ p1)) → p5) := by
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
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h12 =>
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h14 : p1 := by
          -- One of the premise coincides with the conclusion.
          exact h5
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h15 := h2 h14
        -- We need to get the left conjuct of h15 based on <expert-advice>.
        let h16 := h15.left
        -- One of the premise coincides with the conclusion.
        exact h16
      case inr h17 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h18 : p1 := by
          -- One of the premise coincides with the conclusion.
          exact h5
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h19 := h2 h18
        -- We need to get the left conjuct of h19 based on <expert-advice>.
        let h20 := h19.left
        -- One of the premise coincides with the conclusion.
        exact h20
    case inr h21 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h22 : p1 := by
        -- One of the premise coincides with the conclusion.
        exact h5
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h23 := h2 h22
      -- We need to get the left conjuct of h23 based on <expert-advice>.
      let h24 := h23.left
      -- One of the premise coincides with the conclusion.
      exact h24



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317744170036321862614527467259 : (p4 ∨ (((((p5 ∧ (((p5 ∨ True) ∨ True) ∨ ((p4 ∨ p4) ∨ True))) ∧ (p4 ∨ (p1 → False))) → p3) ∧ (((p5 ∧ p2) ∨ False) → False)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148239319048507223867692704258 : ((((((p1 ∨ (p5 ∨ p2)) ∧ (p3 ∧ (p4 ∨ p3))) → False) → ((p2 → p3) → p4)) ∨ ((p5 ∨ False) → p2)) ∨ ((True → (p4 → False)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_774533508541462356732909524906 : (((False ∨ ((((False ∧ False) → (p1 ∨ (p3 ∧ ((p1 → (p1 → True)) ∧ p5)))) ∧ p3) → (((True ∧ (p1 → p5)) ∨ (p1 → p5)) → p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



