variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_738139751197398726501175458965 : ((((False ∧ p1) ∨ (p3 ∨ ((p2 ∨ p2) ∨ (((((((p2 ∨ True) ∨ (p2 ∧ p5)) ∨ p3) → p2) → (p4 ∧ p5)) ∨ (p3 → p3)) → True)))) ∨ p5) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_151499515513512419026301119543 : ((((p2 → (p1 ∨ (p1 ∨ True))) ∨ (p4 ∨ ((p2 ∧ ((False → p2) ∨ p3)) → (p4 → p5)))) ∨ (p5 → True)) → (p1 ∨ ((p4 ∨ True) ∨ True))) := by
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
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h6 =>
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
theorem thm_5_vars_313548099934571518995017291807 : (p3 ∨ ((((p4 → False) ∧ ((((p1 ∨ p4) ∧ True) ∨ p4) ∧ ((p3 ∨ (p2 ∧ p3)) ∨ (False ∧ p1)))) ∧ (((p2 → p3) ∨ p1) ∧ p5)) → p1)) := by
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
  let h6 := h5.left
  let h7 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h12 =>
        -- Disjunctions on the left can always be decomposed.
        cases h12
        case inl h13 =>
          -- Conjunctions on the left can always be decomposed.
          let h14 := h3.left
          let h15 := h3.right
          -- Disjunctions on the left can always be decomposed.
          cases h14
          case inl h16 =>
            -- One of the premise coincides with the conclusion.
            exact h11
          case inr h17 =>
            -- One of the premise coincides with the conclusion.
            exact h17
        case inr h18 =>
          -- Conjunctions on the left can always be decomposed.
          let h19 := h18.left
          let h20 := h18.right
          -- Conjunctions on the left can always be decomposed.
          let h21 := h3.left
          let h22 := h3.right
          -- Disjunctions on the left can always be decomposed.
          cases h21
          case inl h23 =>
            -- One of the premise coincides with the conclusion.
            exact h11
          case inr h24 =>
            -- One of the premise coincides with the conclusion.
            exact h24
      case inr h25 =>
        -- Conjunctions on the left can always be decomposed.
        let h26 := h25.left
        let h27 := h25.right
        -- False on the left can always be used.
        apply False.elim h26
    case inr h28 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h29 =>
        -- Disjunctions on the left can always be decomposed.
        cases h29
        case inl h30 =>
          -- Conjunctions on the left can always be decomposed.
          let h31 := h3.left
          let h32 := h3.right
          -- Disjunctions on the left can always be decomposed.
          cases h31
          case inl h33 =>
            -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
            have h34 : p4 := by
              -- One of the premise coincides with the conclusion.
              exact h28
            -- We have shown the premise of h4, we can now drive its conclusion.
            let h35 := h4 h34
            -- False on the left can always be used.
            apply False.elim h35
          case inr h36 =>
            -- One of the premise coincides with the conclusion.
            exact h36
        case inr h37 =>
          -- Conjunctions on the left can always be decomposed.
          let h38 := h37.left
          let h39 := h37.right
          -- Conjunctions on the left can always be decomposed.
          let h40 := h3.left
          let h41 := h3.right
          -- Disjunctions on the left can always be decomposed.
          cases h40
          case inl h42 =>
            -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
            have h43 : p4 := by
              -- One of the premise coincides with the conclusion.
              exact h28
            -- We have shown the premise of h4, we can now drive its conclusion.
            let h44 := h4 h43
            -- False on the left can always be used.
            apply False.elim h44
          case inr h45 =>
            -- One of the premise coincides with the conclusion.
            exact h45
      case inr h46 =>
        -- Conjunctions on the left can always be decomposed.
        let h47 := h46.left
        let h48 := h46.right
        -- False on the left can always be used.
        apply False.elim h47
  case inr h49 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h50 =>
      -- Disjunctions on the left can always be decomposed.
      cases h50
      case inl h51 =>
        -- Conjunctions on the left can always be decomposed.
        let h52 := h3.left
        let h53 := h3.right
        -- Disjunctions on the left can always be decomposed.
        cases h52
        case inl h54 =>
          -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
          have h55 : p4 := by
            -- One of the premise coincides with the conclusion.
            exact h49
          -- We have shown the premise of h4, we can now drive its conclusion.
          let h56 := h4 h55
          -- False on the left can always be used.
          apply False.elim h56
        case inr h57 =>
          -- One of the premise coincides with the conclusion.
          exact h57
      case inr h58 =>
        -- Conjunctions on the left can always be decomposed.
        let h59 := h58.left
        let h60 := h58.right
        -- Conjunctions on the left can always be decomposed.
        let h61 := h3.left
        let h62 := h3.right
        -- Disjunctions on the left can always be decomposed.
        cases h61
        case inl h63 =>
          -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
          have h64 : p4 := by
            -- One of the premise coincides with the conclusion.
            exact h49
          -- We have shown the premise of h4, we can now drive its conclusion.
          let h65 := h4 h64
          -- False on the left can always be used.
          apply False.elim h65
        case inr h66 =>
          -- One of the premise coincides with the conclusion.
          exact h66
    case inr h67 =>
      -- Conjunctions on the left can always be decomposed.
      let h68 := h67.left
      let h69 := h67.right
      -- False on the left can always be used.
      apply False.elim h68



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_688304783700522486894184964973 : (((((p4 ∧ True) → (p2 ∨ (p5 ∧ (False ∧ ((p1 ∨ False) ∨ ((p3 ∨ p5) ∨ p3)))))) ∧ (p4 ∧ ((p2 ∨ (p5 ∧ (p5 → p2))) → True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65108681654294351053028524423 : ((p2 ∨ (p4 ∨ (((((p1 ∨ False) → p4) ∧ p5) ∧ p3) → ((p2 ∧ True) → (((p2 ∨ (p4 ∧ p1)) → (p1 ∧ (p4 → p1))) ∨ p2))))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  let h5 := h1.left
  let h6 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168994464844187173870621200209 : ((p1 → ((((False ∨ ((p5 ∧ ((p5 ∧ p2) ∨ True)) ∧ (p1 → p2))) ∨ p4) ∨ False) → p5)) → ((p5 ∧ p2) ∨ ((False ∨ (p3 → False)) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41731455057979013293187564504 : (((((p3 → False) ∨ (False ∧ True)) ∧ ((((p1 ∨ True) ∨ p3) ∧ p4) ∨ (p1 ∨ ((p4 → (p3 ∧ (p4 → (p2 ∨ True)))) ∨ p3)))) ∨ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_98821470394204025064217279474 : ((True → ((True ∧ ((False ∧ ((True → p1) → p1)) ∨ (p4 → (((p4 ∨ (p2 ∧ False)) ∧ ((p3 ∧ (p1 ∨ False)) ∧ p5)) ∨ True)))) ∧ p3)) → p3) := by
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
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_716659716784259621406977551979 : (((((False ∨ p3) → (True ∨ p2)) ∧ (((p2 ∧ (((p4 ∧ (p4 → p5)) → (p5 ∨ p2)) → p3)) ∨ ((p5 ∧ False) ∨ False)) ∨ (True → True))) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- False on the left can always be used.
    apply False.elim h2
  case inr h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174516248521393900736920712685 : (((p5 ∨ (((p2 ∧ p3) ∨ p2) ∨ False)) ∨ ((p5 ∨ (p3 ∧ p1)) → (p2 → p1))) → (p4 → (((p4 ∧ p2) ∨ (p1 ∧ p4)) ∨ (p1 ∨ p4)))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Disjunctions on the left can always be decomposed.
        cases h6
        case inl h7 =>
          -- Conjunctions on the left can always be decomposed.
          let h8 := h7.left
          let h9 := h7.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h2
        case inr h10 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h2
      case inr h11 =>
        -- False on the left can always be used.
        apply False.elim h11
  case inr h12 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_88940667236674073802832095130 : (((False → (True → (p1 ∧ True))) → (((((p3 → True) ∧ (p2 → (True → ((True → (p2 ∧ (p3 → False))) ∧ False)))) ∧ p3) ∧ p1) ∧ True)) → p3) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (False → (True → (p1 ∧ True))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- False on the left can always be used.
    apply False.elim h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h2
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- We need to get the left conjuct of h6 based on <expert-advice>.
  let h7 := h6.left
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137400925341539997141831323938 : ((p3 ∧ (p1 ∨ ((((((((p1 → p1) ∧ p1) ∨ (True ∨ p4)) ∨ (p1 → (p1 ∨ False))) ∨ p3) → p3) ∨ p5) ∨ p2))) ∨ ((True ∨ p4) ∧ True)) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192522932445256689502851315934 : ((((p4 ∨ p2) → (((p1 → p4) → p1) ∧ True)) ∨ p1) → ((((p1 → False) ∨ (True ∧ True)) ∨ (p1 → ((p3 ∨ False) ∨ True))) ∨ (False ∧ p4))) := by
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
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
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
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300384870264345437253806312118 : (False ∨ ((((((p2 ∨ p1) ∧ p4) ∨ (p5 → p1)) ∨ p5) ∧ (p2 ∧ ((p1 → p3) → (((p5 → p3) ∧ p2) ∨ p1)))) ∨ (False → (p1 ∧ p5)))) := by
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
theorem thm_5_vars_311048283570792195457851014634 : (p2 ∨ ((p5 ∧ False) ∨ (((p4 ∧ ((p3 ∨ (True ∧ ((((p2 ∧ ((p1 ∨ True) → p4)) ∧ p3) ∧ (p4 ∧ p3)) → p4))) → p1)) ∨ False) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112918467242753533517432644210 : ((((p2 → False) ∨ (((False → p3) ∧ (True → (p5 → p2))) → ((False → ((True ∧ ((p4 ∧ p1) ∧ p4)) ∨ p5)) → True))) → False) ∨ (False → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64682292618200340776945491137 : ((p1 ∨ (p4 ∨ ((p1 ∧ ((p5 ∧ (p1 ∨ p3)) ∨ ((p1 ∧ p3) → (((True → (p3 ∧ p5)) → p5) ∨ (True → True))))) ∨ (p2 → p2)))) ∨ p2) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37113574908818451259338462515 : ((((((p4 ∧ (False ∧ p4)) → (((False → p3) ∨ (False ∨ (False → (p4 ∧ ((p2 ∧ p5) ∧ (True ∨ True)))))) ∧ p3)) → False) ∧ False) ∧ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197828434684344301939813866119 : (((p2 ∧ (p1 ∨ p2)) ∨ (p3 ∨ (p4 ∨ p3))) ∨ (((((p4 → (p4 ∨ p2)) ∧ (p2 → p4)) ∨ (p3 ∨ p4)) ∧ (p3 ∧ (False ∧ True))) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248840486659850440518046837014 : ((p3 ∨ p4) ∨ ((p1 → p5) → (((p4 → (((p4 ∨ (p5 → (((p5 ∧ False) ∧ p4) → p4))) ∨ p2) → (p1 ∨ True))) ∨ (p3 → True)) ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_346908048177648694052001364424 : (p3 → ((((p5 → (True ∨ (p5 ∨ ((False ∨ p4) ∨ True)))) → False) ∧ (((True ∧ p5) → p2) ∨ True)) ∨ (((p5 ∨ (p4 ∨ p1)) → False) ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_626072043914809519295083503009 : ((((p2 → (False ∨ (((True ∧ (p3 → False)) ∨ (p1 → (((p5 ∨ p5) ∨ p5) ∨ (p5 → (((False → p5) → p4) → p5))))) → False))) ∨ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231476063810843431130178258339 : (((p3 → False) ∨ p5) → ((p3 ∧ (((p5 → (p3 ∨ ((p3 → p1) ∧ ((p3 ∨ p3) → p2)))) ∨ (p5 → False)) ∧ (p5 ∧ p4))) ∨ (False → p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61273727840143901471738468910 : ((False ∧ (p2 ∨ (p2 → (True ∧ (p3 ∧ ((True ∧ (p3 ∧ (p3 → (False ∧ (p4 ∧ (p5 ∧ ((True ∨ (p4 ∧ p2)) ∧ p4))))))) ∨ False)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_737873491405281161732840944255 : ((((True ∧ p2) ∨ (((((((p3 ∨ False) ∨ (p1 → (p1 ∨ (p3 ∧ p4)))) → p1) ∧ ((p1 ∧ True) → (False ∨ p4))) ∧ p3) → p4) ∨ p3)) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h6 : ((p3 ∨ False) ∨ (p1 → (p1 ∨ (p3 ∧ p4)))) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h7 := h4 h6
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h8 : (p1 ∧ True) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h7
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h9 := h5 h8
  -- Disjunctions on the left can always be decomposed.
  cases h9
  case inl h10 =>
    -- False on the left can always be used.
    apply False.elim h10
  case inr h11 =>
    -- One of the premise coincides with the conclusion.
    exact h11
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_720400696611595194575495902269 : ((((((p1 → True) → p3) ∨ p2) → (p4 → (((True ∨ p3) ∨ p4) → (((False ∨ False) ∨ (False → ((p1 ∨ p5) → (p5 ∨ p4)))) ∨ p4)))) ∨ p2) ∧ True) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
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
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h2
      case inr h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h2
  case inr h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h13 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354860362104486016274388171263 : (p5 → (((p4 ∨ p4) → ((((((p3 ∨ ((p4 → p5) ∨ ((p1 → (p5 ∧ p4)) ∧ p2))) ∨ True) → (p2 ∨ p1)) ∧ p3) ∧ p3) ∨ p5)) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47832564030303525261030900581 : (((((p5 ∧ p5) ∨ (p2 ∨ ((((False ∨ False) ∨ (p4 → p2)) → ((p2 → True) ∧ p4)) ∨ (p1 → (p4 → False))))) → p1) → (True → p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37582780007979397758916633839 : ((((p2 → ((((p3 ∨ ((p2 ∧ p2) ∨ p1)) ∧ ((p2 → ((False ∧ p5) → p5)) ∧ p1)) → ((p5 ∧ p4) ∧ p2)) ∨ False)) ∨ True) ∧ True) ∨ p1) := by
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
theorem thm_5_vars_46250504947504361213986862012 : ((((((p2 → (((((p5 ∨ (p1 ∨ p5)) → ((p3 → p3) ∧ p2)) ∧ True) ∨ p3) ∨ p4)) ∧ p5) ∨ p4) → (p1 ∨ p2)) ∧ (False ∧ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192921478937326598704410189055 : ((((p2 ∨ ((p2 ∨ False) ∨ False)) ∨ False) ∨ (False → p1)) → (p2 → ((p3 ∧ p3) ∨ ((((False ∨ p2) ∧ True) ∨ (p2 → (p1 ∨ p2))) ∨ p2)))) := by
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
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h5
      case inr h6 =>
        -- Disjunctions on the left can always be decomposed.
        cases h6
        case inl h7 =>
          -- Disjunctions on the left can always be decomposed.
          cases h7
          case inl h8 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h8
          case inr h9 =>
            -- False on the left can always be used.
            apply False.elim h9
        case inr h10 =>
          -- False on the left can always be used.
          apply False.elim h10
    case inr h11 =>
      -- False on the left can always be used.
      apply False.elim h11
  case inr h12 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47304047510056354840673268031 : ((((p4 → (p1 ∧ p1)) ∧ ((p4 → ((p3 ∧ ((p2 ∧ True) ∨ (p1 → ((p5 ∧ True) ∨ (p4 ∨ p4))))) ∧ True)) → p2)) ∨ (p4 → True)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164668192084964092655904583344 : ((((((p2 ∨ ((((p4 ∨ p3) ∧ p1) ∧ p5) ∨ (p1 → p5))) ∨ p4) ∧ p1) ∧ False) ∨ p1) ∨ (((p2 ∧ p2) ∧ (p5 → (p5 ∧ p4))) → p2)) := by
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
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165379058016964253621909803253 : ((((((p2 → (False ∧ p4)) ∨ p4) ∧ p1) ∧ (p4 → (p2 → p5))) ∨ ((p1 → True) ∧ p2)) ∨ (((p5 → True) ∧ True) → (p4 → (p4 ∨ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245342779160717558347923835950 : ((p2 ∧ p3) ∨ (((((True ∧ p3) → p1) ∨ (((p1 → (False ∧ p4)) ∨ True) ∨ (False ∨ ((p4 ∧ p5) ∧ (p3 → p1))))) ∨ (False → p4)) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46240817926432917289286766142 : (((((True ∧ p1) ∨ (((p2 → p3) → p1) ∧ (p5 ∨ (((p2 ∧ (True → p2)) → (True → p4)) ∨ p1)))) ∨ (p3 → p2)) ∧ (p1 ∨ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_608061537986177127066393011602 : (((((((((((p1 → (p4 ∨ (p4 → (p4 ∨ (p2 ∨ False))))) ∨ p1) ∧ p2) ∨ (p3 → (p2 → True))) ∧ p1) ∨ True) ∧ False) ∨ p3) ∨ True) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_149927465340222297774033166635 : ((p3 ∨ ((p3 ∨ ((True → (p4 ∧ False)) ∧ ((False ∧ True) ∧ p1))) ∨ (False ∨ (((False ∧ p3) ∨ p5) ∧ p2)))) ∨ ((p4 ∧ False) → (p5 ∨ False))) := by
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
theorem thm_5_vars_57929948826179881438166376519 : (((True → (p5 ∨ False)) → ((p5 → ((((p4 → True) → (((p4 ∧ p5) → ((p2 ∨ False) ∧ False)) ∨ True)) ∨ True) ∨ (p2 ∧ p1))) ∧ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_804437241279270973240856346658 : (((p3 → ((p4 → ((((True → p1) ∧ (False ∨ p2)) ∨ p3) ∧ p5)) → (((p1 → p2) → (p5 → ((p4 → (p2 ∨ p5)) → p5))) ∨ p3))) ∨ p3) ∧ True) := by
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
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_352402944233694905116178320872 : (p4 → (((p4 → p1) → p2) ∨ (p1 → (((p2 → (p2 → (True → (p3 ∧ (p5 ∧ False))))) → (False ∨ (p2 → ((True ∧ p1) ∨ p5)))) ∨ p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356018648088285745710520227162 : (p5 → ((((False → (p2 ∧ (p2 ∨ p5))) ∨ ((p2 → True) ∧ ((p4 → (p4 → p5)) ∨ (p2 → p3)))) → p2) ∨ ((p5 ∨ (False ∨ p5)) ∧ True))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193049194147652272371405928229 : (((False → ((p2 → (False ∧ p3)) ∧ p1)) → (p4 ∨ False)) → ((p4 → (True → ((True ∨ (((p5 ∨ p4) ∨ p5) ∨ p2)) ∧ (p2 ∨ p2)))) → p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : (False → ((p2 → (False ∧ p3)) ∧ p1)) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- False on the left can always be used.
    apply False.elim h4
    -- False on the left can always be used.
    apply False.elim h4
    -- False on the left can always be used.
    apply False.elim h4
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h3
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h7 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h8 : p4 := by
      -- One of the premise coincides with the conclusion.
      exact h7
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h9 := h2 h8
    -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
    have h10 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h9, we can now drive its conclusion.
    let h11 := h9 h10
    -- We need to get the right conjuct of h11 based on <expert-advice>.
    let h12 := h11.right
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h13 =>
      -- One of the premise coincides with the conclusion.
      exact h13
    case inr h14 =>
      -- One of the premise coincides with the conclusion.
      exact h14
  case inr h15 =>
    -- False on the left can always be used.
    apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356262704994874159826659134693 : (p5 → (((((True ∨ p5) ∧ p3) ∨ p1) ∨ ((p2 → (((p1 ∧ p4) ∨ p5) ∧ True)) ∧ p1)) ∨ (p5 ∨ (False ∨ (p5 ∧ (False ∨ (p5 → p5))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186294714397752306109209189614 : (((((p4 ∨ p1) → ((p1 ∧ p5) ∨ (p1 ∧ p2))) → p2) → p5) → (((p4 ∨ (False ∨ p4)) ∧ (p5 → ((True ∨ p4) → False))) → (p3 ∧ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h6 : (((p4 ∨ p1) → ((p1 ∧ p5) ∨ (p1 ∧ p2))) → p2) := by
      -- Implications on the right can always be decomposed.
      intro h7
      -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
      have h8 : (p4 ∨ p1) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h5
      -- We have shown the premise of h7, we can now drive its conclusion.
      let h9 := h7 h8
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Conjunctions on the left can always be decomposed.
        let h11 := h10.left
        let h12 := h10.right
        -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
        have h13 : p5 := by
          -- One of the premise coincides with the conclusion.
          exact h12
        -- We have shown the premise of h4, we can now drive its conclusion.
        let h14 := h4 h13
        -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
        have h15 : (True ∨ p4) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h14, we can now drive its conclusion.
        let h16 := h14 h15
        -- False on the left can always be used.
        apply False.elim h16
      case inr h17 =>
        -- Conjunctions on the left can always be decomposed.
        let h18 := h17.left
        let h19 := h17.right
        -- One of the premise coincides with the conclusion.
        exact h19
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h20 := h1 h6
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h21 : p5 := by
      -- One of the premise coincides with the conclusion.
      exact h20
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h22 := h4 h21
    -- We want to use the implication h22 based on <expert-advice>. So we show its premise.
    have h23 : (True ∨ p4) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h22, we can now drive its conclusion.
    let h24 := h22 h23
    -- False on the left can always be used.
    apply False.elim h24
  case inr h25 =>
    -- Disjunctions on the left can always be decomposed.
    cases h25
    case inl h26 =>
      -- False on the left can always be used.
      apply False.elim h26
    case inr h27 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h28 : (((p4 ∨ p1) → ((p1 ∧ p5) ∨ (p1 ∧ p2))) → p2) := by
        -- Implications on the right can always be decomposed.
        intro h29
        -- We want to use the implication h29 based on <expert-advice>. So we show its premise.
        have h30 : (p4 ∨ p1) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h27
        -- We have shown the premise of h29, we can now drive its conclusion.
        let h31 := h29 h30
        -- Disjunctions on the left can always be decomposed.
        cases h31
        case inl h32 =>
          -- Conjunctions on the left can always be decomposed.
          let h33 := h32.left
          let h34 := h32.right
          -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
          have h35 : p5 := by
            -- One of the premise coincides with the conclusion.
            exact h34
          -- We have shown the premise of h4, we can now drive its conclusion.
          let h36 := h4 h35
          -- We want to use the implication h36 based on <expert-advice>. So we show its premise.
          have h37 : (True ∨ p4) := by
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h36, we can now drive its conclusion.
          let h38 := h36 h37
          -- False on the left can always be used.
          apply False.elim h38
        case inr h39 =>
          -- Conjunctions on the left can always be decomposed.
          let h40 := h39.left
          let h41 := h39.right
          -- One of the premise coincides with the conclusion.
          exact h41
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h42 := h1 h28
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h43 : p5 := by
        -- One of the premise coincides with the conclusion.
        exact h42
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h44 := h4 h43
      -- We want to use the implication h44 based on <expert-advice>. So we show its premise.
      have h45 : (True ∨ p4) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h44, we can now drive its conclusion.
      let h46 := h44 h45
      -- False on the left can always be used.
      apply False.elim h46
  -- Conjunctions on the left can always be decomposed.
  let h47 := h2.left
  let h48 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h47
  case inl h49 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h50 : (((p4 ∨ p1) → ((p1 ∧ p5) ∨ (p1 ∧ p2))) → p2) := by
      -- Implications on the right can always be decomposed.
      intro h51
      -- We want to use the implication h51 based on <expert-advice>. So we show its premise.
      have h52 : (p4 ∨ p1) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h49
      -- We have shown the premise of h51, we can now drive its conclusion.
      let h53 := h51 h52
      -- Disjunctions on the left can always be decomposed.
      cases h53
      case inl h54 =>
        -- Conjunctions on the left can always be decomposed.
        let h55 := h54.left
        let h56 := h54.right
        -- We want to use the implication h48 based on <expert-advice>. So we show its premise.
        have h57 : p5 := by
          -- One of the premise coincides with the conclusion.
          exact h56
        -- We have shown the premise of h48, we can now drive its conclusion.
        let h58 := h48 h57
        -- We want to use the implication h58 based on <expert-advice>. So we show its premise.
        have h59 : (True ∨ p4) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h58, we can now drive its conclusion.
        let h60 := h58 h59
        -- False on the left can always be used.
        apply False.elim h60
      case inr h61 =>
        -- Conjunctions on the left can always be decomposed.
        let h62 := h61.left
        let h63 := h61.right
        -- One of the premise coincides with the conclusion.
        exact h63
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h64 := h1 h50
    -- We want to use the implication h48 based on <expert-advice>. So we show its premise.
    have h65 : p5 := by
      -- One of the premise coincides with the conclusion.
      exact h64
    -- We have shown the premise of h48, we can now drive its conclusion.
    let h66 := h48 h65
    -- We want to use the implication h66 based on <expert-advice>. So we show its premise.
    have h67 : (True ∨ p4) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h66, we can now drive its conclusion.
    let h68 := h66 h67
    -- False on the left can always be used.
    apply False.elim h68
  case inr h69 =>
    -- Disjunctions on the left can always be decomposed.
    cases h69
    case inl h70 =>
      -- False on the left can always be used.
      apply False.elim h70
    case inr h71 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h72 : (((p4 ∨ p1) → ((p1 ∧ p5) ∨ (p1 ∧ p2))) → p2) := by
        -- Implications on the right can always be decomposed.
        intro h73
        -- We want to use the implication h73 based on <expert-advice>. So we show its premise.
        have h74 : (p4 ∨ p1) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h71
        -- We have shown the premise of h73, we can now drive its conclusion.
        let h75 := h73 h74
        -- Disjunctions on the left can always be decomposed.
        cases h75
        case inl h76 =>
          -- Conjunctions on the left can always be decomposed.
          let h77 := h76.left
          let h78 := h76.right
          -- We want to use the implication h48 based on <expert-advice>. So we show its premise.
          have h79 : p5 := by
            -- One of the premise coincides with the conclusion.
            exact h78
          -- We have shown the premise of h48, we can now drive its conclusion.
          let h80 := h48 h79
          -- We want to use the implication h80 based on <expert-advice>. So we show its premise.
          have h81 : (True ∨ p4) := by
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h80, we can now drive its conclusion.
          let h82 := h80 h81
          -- False on the left can always be used.
          apply False.elim h82
        case inr h83 =>
          -- Conjunctions on the left can always be decomposed.
          let h84 := h83.left
          let h85 := h83.right
          -- One of the premise coincides with the conclusion.
          exact h85
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h86 := h1 h72
      -- We want to use the implication h48 based on <expert-advice>. So we show its premise.
      have h87 : p5 := by
        -- One of the premise coincides with the conclusion.
        exact h86
      -- We have shown the premise of h48, we can now drive its conclusion.
      let h88 := h48 h87
      -- We want to use the implication h88 based on <expert-advice>. So we show its premise.
      have h89 : (True ∨ p4) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h88, we can now drive its conclusion.
      let h90 := h88 h89
      -- False on the left can always be used.
      apply False.elim h90



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_657275969276994451527873895445 : (((((True ∧ p4) ∧ ((p2 ∧ (p4 → p2)) ∧ (((p1 → (p3 → True)) ∧ True) ∧ (p1 ∧ (True → (p1 ∨ (p4 ∨ True))))))) ∨ (p2 ∨ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193118211569247793100114820892 : (((((p1 ∧ p1) ∧ p1) ∨ p4) ∨ ((p1 ∨ False) → p1)) → (p4 → (p3 → ((p2 ∧ ((p1 → (((p3 ∧ p1) ∨ p1) ∧ p5)) ∧ p1)) ∨ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Conjunctions on the left can always be decomposed.
      let h8 := h6.left
      let h9 := h6.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h10
  case inr h11 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43301788697233817941457300362 : (((((((p4 → ((p5 ∨ ((True ∨ ((p1 ∧ (p3 → p2)) ∨ p2)) → (False ∧ (p5 → p5)))) ∧ p2)) → p2) ∨ p4) ∨ p2) ∨ p3) → p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_881528352793099925113720721775 : ((((((p4 → True) ∧ (((p2 ∧ ((((((True → p1) ∧ p4) ∨ p5) ∨ True) ∨ True) ∧ (p4 ∧ p3))) ∨ p4) ∨ True)) → False) ∨ (p1 ∧ False)) → p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h3 : ((p4 → True) ∧ (((p2 ∧ ((((((True → p1) ∧ p4) ∨ p5) ∨ True) ∨ True) ∧ (p4 ∧ p3))) ∨ p4) ∨ True)) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h4
      -- True on the right can always be proven directly.
      apply True.intro
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h5 := h2 h3
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- False on the left can always be used.
    apply False.elim h8
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_84851447933970540055281293032 : (((p2 → (False → (((p4 → p4) ∧ (p2 ∨ (False ∨ (p4 → True)))) → p3))) ∧ (p3 ∧ (((((p2 ∧ p3) ∨ False) → p1) ∧ p1) → p1))) → p3) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313012935311571583006385783988 : (p3 ∨ ((((p4 ∧ ((p5 ∨ p2) ∨ p1)) → (p5 ∧ (((((p5 ∨ True) ∧ p2) ∨ (p3 ∧ False)) ∧ p3) ∨ (p4 ∨ (False ∧ p3))))) ∨ True) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_153242281999279525681382015852 : ((False ∨ ((((((((p1 ∧ True) → (True → (True ∧ p3))) ∧ p2) → p1) ∨ (p4 ∧ p1)) ∨ p2) → p4) ∨ p1)) → (p3 ∨ (False → (p1 ∧ p1)))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h5
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- False on the left can always be used.
      apply False.elim h5
      -- False on the left can always be used.
      apply False.elim h5
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h7
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- False on the left can always be used.
      apply False.elim h7
      -- False on the left can always be used.
      apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44355330820220176511219870153 : ((((p5 → (((p3 ∨ p3) → p2) → (False ∨ ((p1 ∨ (True → p3)) ∧ (p1 ∨ True))))) → (True ∧ (p3 ∧ (p5 → (True ∧ True))))) → p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_877824742432657394696492368246 : (((((True → (p3 ∧ False)) ∧ (((p3 ∨ (((p5 → False) ∧ p1) ∨ (p1 → p2))) → ((p3 → p5) → False)) ∧ (p2 → p3))) ∧ (p3 ∨ p3)) → p2) ∧ True) := by
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
  cases h3
  case inl h8 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h9 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h10 := h4 h9
    -- We need to get the right conjuct of h10 based on <expert-advice>.
    let h11 := h10.right
    -- False on the left can always be used.
    apply False.elim h11
  case inr h12 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h13 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h14 := h4 h13
    -- We need to get the right conjuct of h14 based on <expert-advice>.
    let h15 := h14.right
    -- False on the left can always be used.
    apply False.elim h15
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248713012532532434459155199724 : ((p3 ∨ p2) ∨ (((p3 ∧ p1) ∨ p3) ∨ ((False → ((p3 → p4) ∧ (p5 → p1))) ∨ (p5 ∨ (False ∧ ((p4 → p5) → ((False → True) ∨ p1))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111592339525162847437961557632 : ((((True → (((((True ∨ p2) → ((p1 ∨ ((p1 ∨ False) ∧ p3)) → (p4 → p2))) ∨ (True → p2)) ∨ p2) ∧ p1)) ∧ p1) ∨ True) ∨ (True ∧ p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345410198167633521808081103527 : (p3 → ((((((p3 → False) ∨ (((p5 → False) ∧ p2) ∨ p4)) ∨ p4) → (((False → ((p2 ∧ True) ∧ p3)) ∧ p4) ∨ (False → p1))) → p2) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_125580224403446582007969605580 : (((p3 → p2) ∧ (((False → (True ∨ p4)) → False) ∧ ((((p1 ∨ ((True ∨ p3) ∨ (p5 ∨ True))) ∧ p1) ∧ (p1 ∧ True)) ∨ False))) → (p3 ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h7.left
    let h10 := h7.right
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h8.left
      let h13 := h8.right
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h14 : (False → (True ∨ p4)) := by
        -- Implications on the right can always be decomposed.
        intro h15
        -- False on the left can always be used.
        apply False.elim h15
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h16 := h4 h14
      -- False on the left can always be used.
      apply False.elim h16
    case inr h17 =>
      -- Disjunctions on the left can always be decomposed.
      cases h17
      case inl h18 =>
        -- Disjunctions on the left can always be decomposed.
        cases h18
        case inl h19 =>
          -- Conjunctions on the left can always be decomposed.
          let h20 := h8.left
          let h21 := h8.right
          -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
          have h22 : (False → (True ∨ p4)) := by
            -- Implications on the right can always be decomposed.
            intro h23
            -- False on the left can always be used.
            apply False.elim h23
          -- We have shown the premise of h4, we can now drive its conclusion.
          let h24 := h4 h22
          -- False on the left can always be used.
          apply False.elim h24
        case inr h25 =>
          -- Conjunctions on the left can always be decomposed.
          let h26 := h8.left
          let h27 := h8.right
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h25
      case inr h28 =>
        -- Disjunctions on the left can always be decomposed.
        cases h28
        case inl h29 =>
          -- Conjunctions on the left can always be decomposed.
          let h30 := h8.left
          let h31 := h8.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h29
        case inr h32 =>
          -- Conjunctions on the left can always be decomposed.
          let h33 := h8.left
          let h34 := h8.right
          -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
          have h35 : (False → (True ∨ p4)) := by
            -- Implications on the right can always be decomposed.
            intro h36
            -- False on the left can always be used.
            apply False.elim h36
          -- We have shown the premise of h4, we can now drive its conclusion.
          let h37 := h4 h35
          -- False on the left can always be used.
          apply False.elim h37
  case inr h38 =>
    -- False on the left can always be used.
    apply False.elim h38



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173649265922706526498299948028 : (((((((p1 ∧ p4) → (p1 → (p4 → (False ∨ p3)))) ∨ p2) → p1) ∧ p2) ∨ p1) → ((False ∨ ((p5 → (True → p1)) ∨ (False → False))) → p1)) := by
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
        -- Conjunctions on the left can always be decomposed.
        let h7 := h6.left
        let h8 := h6.right
        -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
        have h9 : (((p1 ∧ p4) → (p1 → (p4 → (False ∨ p3)))) ∨ p2) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h8
        -- We have shown the premise of h7, we can now drive its conclusion.
        let h10 := h7 h9
        -- One of the premise coincides with the conclusion.
        exact h10
      case inr h11 =>
        -- One of the premise coincides with the conclusion.
        exact h11
    case inr h12 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h13 =>
        -- Conjunctions on the left can always be decomposed.
        let h14 := h13.left
        let h15 := h13.right
        -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
        have h16 : (((p1 ∧ p4) → (p1 → (p4 → (False ∨ p3)))) ∨ p2) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h15
        -- We have shown the premise of h14, we can now drive its conclusion.
        let h17 := h14 h16
        -- One of the premise coincides with the conclusion.
        exact h17
      case inr h18 =>
        -- One of the premise coincides with the conclusion.
        exact h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38226262148025511267225825284 : ((((p5 ∧ ((p4 ∧ p1) ∧ ((p3 ∨ p5) ∨ ((p5 ∨ p4) ∨ (((p5 ∨ (p1 ∧ p4)) ∧ p2) → p5))))) → ((p2 → False) ∨ True)) ∧ True) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  let h6 := h4.left
  let h7 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h8 =>
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
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
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
    case inr h15 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199475629686167293762899878390 : (((p2 ∨ ((p3 ∨ (p5 → True)) → p2)) ∨ False) → (((p3 ∨ (p5 ∧ p2)) → (False ∨ (((p2 → False) → ((p2 → p4) ∧ p2)) ∧ True))) ∧ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h4 =>
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h5 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Implications on the right can always be decomposed.
        intro h6
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Implications on the right can always be decomposed.
        intro h7
        -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
        have h8 : p2 := by
          -- One of the premise coincides with the conclusion.
          exact h7
        -- We have shown the premise of h6, we can now drive its conclusion.
        let h9 := h6 h8
        -- False on the left can always be used.
        apply False.elim h9
        -- One of the premise coincides with the conclusion.
        exact h5
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Implications on the right can always be decomposed.
        intro h11
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Implications on the right can always be decomposed.
        intro h12
        -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
        have h13 : p2 := by
          -- One of the premise coincides with the conclusion.
          exact h12
        -- We have shown the premise of h11, we can now drive its conclusion.
        let h14 := h11 h13
        -- False on the left can always be used.
        apply False.elim h14
        -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
        have h15 : (p3 ∨ (p5 → True)) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h3
        -- We have shown the premise of h10, we can now drive its conclusion.
        let h16 := h10 h15
        -- One of the premise coincides with the conclusion.
        exact h16
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h17 =>
      -- False on the left can always be used.
      apply False.elim h17
  case inr h18 =>
    -- Conjunctions on the left can always be decomposed.
    let h19 := h18.left
    let h20 := h18.right
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h21 =>
      -- Disjunctions on the left can always be decomposed.
      cases h21
      case inl h22 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Implications on the right can always be decomposed.
        intro h23
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Implications on the right can always be decomposed.
        intro h24
        -- We want to use the implication h23 based on <expert-advice>. So we show its premise.
        have h25 : p2 := by
          -- One of the premise coincides with the conclusion.
          exact h24
        -- We have shown the premise of h23, we can now drive its conclusion.
        let h26 := h23 h25
        -- False on the left can always be used.
        apply False.elim h26
        -- One of the premise coincides with the conclusion.
        exact h22
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h27 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Implications on the right can always be decomposed.
        intro h28
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Implications on the right can always be decomposed.
        intro h29
        -- We want to use the implication h28 based on <expert-advice>. So we show its premise.
        have h30 : p2 := by
          -- One of the premise coincides with the conclusion.
          exact h29
        -- We have shown the premise of h28, we can now drive its conclusion.
        let h31 := h28 h30
        -- False on the left can always be used.
        apply False.elim h31
        -- One of the premise coincides with the conclusion.
        exact h20
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h32 =>
      -- False on the left can always be used.
      apply False.elim h32
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h33 =>
    -- Disjunctions on the left can always be decomposed.
    cases h33
    case inl h34 =>
      -- One of the premise coincides with the conclusion.
      exact h34
    case inr h35 =>
      -- We want to use the implication h35 based on <expert-advice>. So we show its premise.
      have h36 : (p3 ∨ (p5 → True)) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h37
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h35, we can now drive its conclusion.
      let h38 := h35 h36
      -- One of the premise coincides with the conclusion.
      exact h38
  case inr h39 =>
    -- False on the left can always be used.
    apply False.elim h39



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_614027913274990062217514466517 : ((((((p5 → p4) ∧ (p5 ∧ (False ∧ ((p1 ∧ (p3 ∨ ((False ∨ p1) → p5))) ∨ (True → (p2 ∨ p4)))))) ∨ (p1 → (True ∨ p3))) ∨ p3) ∨ p2) ∧ True) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_358674915705528428569024045332 : (p5 → (p4 → ((True ∧ p3) ∨ ((((p4 → (p1 → (False ∨ (((p1 ∧ p5) → p3) → (p2 ∨ p2))))) ∨ ((True → p2) ∧ p5)) ∨ p5) ∧ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309278471511709672921981706373 : (p2 ∨ ((p2 ∨ ((p5 ∨ (((p4 ∨ (p3 ∨ ((True → True) ∨ ((p1 → p1) ∨ ((p2 ∧ False) ∨ p2))))) → p2) ∨ True)) ∨ True)) ∧ (p3 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158336876443547487270836277455 : (((p1 ∧ p5) ∧ ((p5 ∧ (((p3 ∨ (True ∧ False)) ∨ p1) ∨ (((True ∧ True) → p5) ∨ p2))) ∧ p4)) ∨ (False → (p2 ∨ (p5 ∧ (p2 → p1))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_456916279639215472075791782158 : ((((p1 → ((p4 ∧ p1) → ((p5 ∨ (p2 ∨ ((p3 ∧ p2) ∨ ((True → p4) ∨ p5)))) ∧ True))) ∧ (p5 → (p4 ∨ (p5 → (True ∧ p5))))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h5
  -- One of the premise coincides with the conclusion.
  exact h3
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h6
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h7
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h7
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179250954070522967195422347058 : ((p5 ∧ ((True ∧ p2) ∧ (p1 ∧ (((p3 ∧ False) ∨ (True ∧ p5)) ∨ True)))) ∨ ((((False ∨ p5) ∨ p4) ∧ (p3 ∧ p5)) → (p1 → (p5 → p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- False on the left can always be used.
      apply False.elim h7
    case inr h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h5.left
      let h10 := h5.right
      -- One of the premise coincides with the conclusion.
      exact h9
  case inr h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h5.left
    let h13 := h5.right
    -- One of the premise coincides with the conclusion.
    exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_85432865880430073155807139506 : (((p2 ∧ ((p2 → ((p1 ∧ p2) ∧ p1)) ∧ (p3 ∧ (p5 ∨ p5)))) ∧ (((True ∧ p1) → ((p5 ∨ p3) ∧ (p1 ∨ (True ∧ False)))) → True)) → p1) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h8 := h7.left
  let h9 := h7.right
  -- Disjunctions on the left can always be decomposed.
  cases h9
  case inl h10 =>
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h11 : p2 := by
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h12 := h6 h11
    -- We need to get the right conjuct of h12 based on <expert-advice>.
    let h13 := h12.right
    -- One of the premise coincides with the conclusion.
    exact h13
  case inr h14 =>
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h15 : p2 := by
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h16 := h6 h15
    -- We need to get the right conjuct of h16 based on <expert-advice>.
    let h17 := h16.right
    -- One of the premise coincides with the conclusion.
    exact h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48936783243438449184543844245 : ((((((True → ((p2 ∨ p2) ∧ True)) ∨ (p4 ∧ (False ∨ p2))) → ((p4 ∧ p5) → (p4 → (p3 ∨ p2)))) ∧ p5) ∨ (p4 → (p2 ∨ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347597256808720632020014099785 : (p3 → ((((p1 → p4) → p2) ∨ p1) ∨ ((((p2 → p1) ∧ (((p5 ∨ False) ∨ (False ∧ p4)) ∨ True)) ∧ (p5 ∨ p5)) ∨ ((p3 ∨ p4) ∨ False)))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308681741726800291437231977514 : (p2 ∨ ((False ∨ (((((p5 → (p5 → True)) ∨ True) ∧ ((p2 ∨ p4) ∨ False)) ∨ (p5 → p3)) ∨ (((p4 ∧ p1) → p4) → (False → p1)))) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_85409587428939567024913965557 : ((((False ∧ p1) ∨ ((True → (False ∨ False)) ∧ (p1 → (p4 ∨ p5)))) ∧ (p4 ∨ (((((p5 → (p1 → p2)) ∧ True) ∧ p1) ∧ p5) ∨ p2))) → False) := by
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
    -- False on the left can always be used.
    apply False.elim h5
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h10 =>
      -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
      have h11 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h8, we can now drive its conclusion.
      let h12 := h8 h11
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- False on the left can always be used.
        apply False.elim h13
      case inr h14 =>
        -- False on the left can always be used.
        apply False.elim h14
    case inr h15 =>
      -- Disjunctions on the left can always be decomposed.
      cases h15
      case inl h16 =>
        -- Conjunctions on the left can always be decomposed.
        let h17 := h16.left
        let h18 := h16.right
        -- Conjunctions on the left can always be decomposed.
        let h19 := h17.left
        let h20 := h17.right
        -- Conjunctions on the left can always be decomposed.
        let h21 := h19.left
        let h22 := h19.right
        -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
        have h23 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h8, we can now drive its conclusion.
        let h24 := h8 h23
        -- Disjunctions on the left can always be decomposed.
        cases h24
        case inl h25 =>
          -- False on the left can always be used.
          apply False.elim h25
        case inr h26 =>
          -- False on the left can always be used.
          apply False.elim h26
      case inr h27 =>
        -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
        have h28 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h8, we can now drive its conclusion.
        let h29 := h8 h28
        -- Disjunctions on the left can always be decomposed.
        cases h29
        case inl h30 =>
          -- False on the left can always be used.
          apply False.elim h30
        case inr h31 =>
          -- False on the left can always be used.
          apply False.elim h31



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_593333932519788351933069231091 : (((((((((((True → p5) → ((p1 ∧ p2) → p4)) ∧ ((p1 → True) ∧ p4)) ∨ p1) ∨ p5) ∨ False) ∨ p2) → (p5 ∨ (False → True))) ∧ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168873105529408321821727499909 : ((p4 ∨ ((((True → ((p2 ∨ True) ∧ p1)) ∧ p1) → p2) → (((p1 → p3) → True) ∧ p2))) → (p1 ∨ ((((p4 ∨ True) ∨ False) ∧ p2) → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115550632612757055575670009165 : ((((((p3 ∧ p5) → p4) ∨ p1) ∧ p4) ∧ ((p4 ∧ (p1 ∨ ((p1 ∧ (p1 ∧ True)) ∨ (p2 ∨ ((True → p3) ∨ p5))))) ∨ p4)) ∨ (p5 → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342904330381188366343500831726 : (p2 → (((p5 ∨ True) → ((True ∧ p1) → False)) → (((p4 ∧ p2) → (p1 ∨ ((p1 ∧ p2) ∧ False))) ∨ ((((p5 ∧ p4) ∧ True) → True) → p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52504658169878691628280803430 : (((((((p2 ∧ (p2 → p4)) ∨ p5) ∨ (p4 ∧ (p3 ∨ p5))) → p3) ∧ p1) ∨ (((p1 → False) → True) → ((p3 ∨ p2) ∨ (p1 → True)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206484653734673156485713972604 : ((p5 ∨ ((p1 ∧ (p4 ∧ False)) ∨ p4)) ∨ (((((p4 ∨ p2) ∧ (p3 ∨ (p5 ∧ p3))) ∨ (p3 → p1)) → (p1 ∨ p2)) → (False → (False → p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179238474470222318397379536011 : ((p5 ∧ (((p4 → p3) ∨ ((((p2 → p2) ∧ p2) → p1) → p5)) ∨ p2)) ∨ (p4 → ((True ∧ (True ∧ (True ∨ ((p1 → p4) ∧ p3)))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148002890351919868806665283148 : (((((((False ∧ True) → (p5 → p3)) → ((p3 ∧ True) ∨ (p4 ∧ True))) ∨ p1) ∧ (p1 ∨ p2)) ∨ (True ∧ True)) ∨ ((p5 → (p1 ∨ p2)) ∧ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_739289597678642936848914313609 : ((((p4 ∧ p3) ∨ ((p1 → ((p3 → p4) ∨ (p4 ∧ ((False ∨ ((p3 → (((p3 ∧ False) ∧ (p4 ∨ p3)) ∧ p2)) → p5)) ∨ p1)))) ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246508425955491898824098329090 : ((p5 ∧ p1) ∨ ((((p5 ∨ ((p4 ∧ ((p4 ∧ p5) → True)) ∨ p1)) ∧ p1) → (p4 → ((p3 ∧ p3) ∨ ((p5 → True) ∨ p1)))) ∨ (False → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165591247481221018191592237655 : ((((((True ∧ (p4 → p2)) ∨ False) → False) ∧ p4) → (p3 ∨ (p5 ∧ ((p1 ∧ True) ∧ p3)))) ∨ (((False ∧ p4) ∧ p1) → (p5 → (p3 ∨ p1)))) := by
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
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198349795284821620176852830150 : ((p2 ∧ ((True ∨ p5) → (True → (p3 ∨ False)))) ∨ (((True → (((((p3 ∧ p3) ∧ False) ∧ p1) ∨ p2) ∨ (p1 ∨ p2))) → True) ∨ (p1 ∧ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60922046987245574694236575007 : ((False ∧ ((((((p4 → True) ∧ p2) ∧ ((p3 ∨ p2) ∧ (False ∨ p2))) ∨ (p2 → (p5 ∨ p4))) → ((p5 ∧ (p2 ∧ p2)) ∧ p2)) ∧ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185852702524402945877687540329 : (((((p4 → p5) → (((False ∧ p2) ∨ True) ∨ p3)) ∨ p2) ∧ p5) → ((((((p1 ∨ p4) ∧ True) ∧ p4) ∧ False) ∨ (p3 ∨ True)) ∨ (p1 ∧ False))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_458818502912029655466746705310 : ((((p4 → (((p2 → p1) ∧ (p1 → (p3 → p2))) ∧ ((p5 ∧ ((p5 → p1) → p1)) ∨ p3))) ∨ (p1 → ((p3 ∨ (p2 → True)) ∨ p2))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328529843899757057706954324813 : (True → (((p4 → p1) → (p1 ∨ (((p3 ∨ p2) ∧ True) → ((p3 ∨ (p5 ∨ p1)) ∧ p5)))) ∨ (((p3 → (p2 ∨ (p5 → p5))) ∨ p5) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_229412582112012015532436291599 : ((p1 → (p4 ∨ p5)) ∨ (((p5 ∨ p5) ∨ (p5 ∧ p1)) ∨ ((p4 ∧ ((p4 ∧ (p4 ∧ p5)) → p2)) ∨ (p5 ∨ (p3 ∨ (True → (True ∨ p4))))))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_751136946636342220067654910922 : (((True ∧ ((p3 ∧ (True → True)) ∧ (((p4 ∧ (p5 ∧ ((p1 ∨ p3) → p3))) → True) → ((((p5 ∨ True) → (p1 ∨ True)) → p4) ∨ False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232405573960357555658728999591 : (((p5 → p5) → False) → ((((p4 ∨ ((p3 ∧ (p3 ∧ p2)) ∧ p2)) ∧ (p5 ∨ (p2 → p4))) ∧ p4) ∧ ((p1 ∧ (p4 → p5)) ∨ (p5 ∧ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p5 → p5) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- False on the left can always be used.
  apply False.elim h4
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h5 : (p5 → p5) := by
    -- Implications on the right can always be decomposed.
    intro h6
    -- One of the premise coincides with the conclusion.
    exact h6
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h7 := h1 h5
  -- False on the left can always be used.
  apply False.elim h7
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h8 : (p5 → p5) := by
    -- Implications on the right can always be decomposed.
    intro h9
    -- One of the premise coincides with the conclusion.
    exact h9
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h10 := h1 h8
  -- False on the left can always be used.
  apply False.elim h10
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h11 : (p5 → p5) := by
    -- Implications on the right can always be decomposed.
    intro h12
    -- One of the premise coincides with the conclusion.
    exact h12
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h13 := h1 h11
  -- False on the left can always be used.
  apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171674444938846795562983223569 : (((False ∨ ((True → (p4 ∨ (((p5 ∨ p4) ∧ p4) ∧ False))) ∨ (p4 ∨ True))) ∨ p2) ∨ ((False ∧ (True → ((p1 → p5) → p5))) ∧ (True ∨ p4))) := by
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
theorem thm_5_vars_863343986329206445789690780858 : ((((((p5 ∨ ((True ∧ (p3 ∨ (True ∨ (p3 ∧ False)))) → p2)) ∧ (p4 → p1)) → ((p1 ∨ ((False ∨ (p3 ∨ False)) ∧ True)) ∨ True)) → p5) → p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p5 ∨ ((True ∧ (p3 ∨ (True ∨ (p3 ∧ False)))) → p2)) ∧ (p4 → p1)) → ((p1 ∨ ((False ∨ (p3 ∨ False)) ∧ True)) ∨ True)) := by
    -- Implications on the right can always be decomposed.
    intro h3
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
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h8 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h8
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52914268670386194542828641613 : (((p4 → ((p3 ∧ (((p1 ∧ p4) ∧ False) ∨ (p1 → (True → p5)))) → p2)) → (False ∧ ((((True ∨ True) → p2) → p1) → (p1 → p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149909521939308281112391982805 : ((p3 ∨ ((p1 → ((((p1 ∧ (((False ∧ p2) → p2) ∨ p3)) ∨ ((p4 → p3) ∨ True)) ∨ p1) → False)) ∧ True)) ∨ (((p5 → True) ∨ True) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310610356751492459741440717661 : (p2 ∨ ((((True ∨ p4) ∧ p1) ∨ p3) ∨ (((((((p1 → True) ∧ True) → p5) ∧ p4) → (True → p1)) ∨ False) ∨ ((p5 ∨ True) ∨ (p2 ∧ p3))))) := by
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
theorem thm_5_vars_147297392223227066191424503475 : (((((((True ∨ p4) ∧ ((p2 → p2) ∧ (p2 ∧ (p1 → p1)))) ∧ ((p1 ∧ p4) → p3)) → p1) → p1) ∨ False) ∨ (p3 → (False ∨ (p3 → p3)))) := by
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
theorem thm_5_vars_63924716659658263501246944488 : ((False ∨ (((((p1 ∨ (((False ∧ True) → (False → ((p2 → p3) ∧ (p2 → p1)))) ∨ True)) ∨ (p4 → (p2 ∨ p5))) → p1) ∨ False) ∨ True)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65420644209690933033643711764 : ((p3 ∨ (((p3 → True) → p2) ∨ (p5 ∧ ((p2 ∧ p1) ∧ (p4 ∨ ((p3 ∧ False) → ((((True → p5) ∨ (p4 ∨ p1)) ∨ p1) ∨ False))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147633813001588599429380014017 : (((((p4 ∧ ((False ∨ (True ∧ p2)) → p1)) → (True ∨ ((p4 ∧ (False ∧ p5)) → (False ∨ p4)))) → p5) → p2) ∨ (True → (True ∨ (p3 ∨ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



