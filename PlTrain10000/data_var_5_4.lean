variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_728974167767695447815623042 : ((((True ∨ (False ∨ p3)) ∧ True) ∧ ((((False → (True → (p1 ∨ p2))) → (p5 ∨ ((p4 ∧ (p5 ∨ p1)) → False))) → False) ∧ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_731685398069463882705475220840 : ((((p2 → (True ∨ p5)) → (((False → (p1 → p5)) ∨ False) ∧ (p4 ∧ ((p3 ∨ ((p5 ∧ True) ∧ ((p2 ∧ False) ∨ p2))) ∧ (p3 ∧ p5))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167895009797367747158922758617 : (((((p1 ∨ p3) ∨ (False → (False ∨ p3))) ∨ True) ∧ ((p5 ∧ p3) ∧ (True ∨ (p2 ∧ p2)))) → ((p3 ∨ False) ∧ ((p1 ∨ p1) ∨ (p5 ∧ p5)))) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Conjunctions on the left can always be decomposed.
        let h7 := h3.left
        let h8 := h3.right
        -- Conjunctions on the left can always be decomposed.
        let h9 := h7.left
        let h10 := h7.right
        -- Disjunctions on the left can always be decomposed.
        cases h8
        case inl h11 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h10
        case inr h12 =>
          -- Conjunctions on the left can always be decomposed.
          let h13 := h12.left
          let h14 := h12.right
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h10
      case inr h15 =>
        -- Conjunctions on the left can always be decomposed.
        let h16 := h3.left
        let h17 := h3.right
        -- Conjunctions on the left can always be decomposed.
        let h18 := h16.left
        let h19 := h16.right
        -- Disjunctions on the left can always be decomposed.
        cases h17
        case inl h20 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h19
        case inr h21 =>
          -- Conjunctions on the left can always be decomposed.
          let h22 := h21.left
          let h23 := h21.right
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h19
    case inr h24 =>
      -- Conjunctions on the left can always be decomposed.
      let h25 := h3.left
      let h26 := h3.right
      -- Conjunctions on the left can always be decomposed.
      let h27 := h25.left
      let h28 := h25.right
      -- Disjunctions on the left can always be decomposed.
      cases h26
      case inl h29 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h28
      case inr h30 =>
        -- Conjunctions on the left can always be decomposed.
        let h31 := h30.left
        let h32 := h30.right
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h28
  case inr h33 =>
    -- Conjunctions on the left can always be decomposed.
    let h34 := h3.left
    let h35 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h36 := h34.left
    let h37 := h34.right
    -- Disjunctions on the left can always be decomposed.
    cases h35
    case inl h38 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h37
    case inr h39 =>
      -- Conjunctions on the left can always be decomposed.
      let h40 := h39.left
      let h41 := h39.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h37
  -- Conjunctions on the left can always be decomposed.
  let h42 := h1.left
  let h43 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h42
  case inl h44 =>
    -- Disjunctions on the left can always be decomposed.
    cases h44
    case inl h45 =>
      -- Disjunctions on the left can always be decomposed.
      cases h45
      case inl h46 =>
        -- Conjunctions on the left can always be decomposed.
        let h47 := h43.left
        let h48 := h43.right
        -- Conjunctions on the left can always be decomposed.
        let h49 := h47.left
        let h50 := h47.right
        -- Disjunctions on the left can always be decomposed.
        cases h48
        case inl h51 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h46
        case inr h52 =>
          -- Conjunctions on the left can always be decomposed.
          let h53 := h52.left
          let h54 := h52.right
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h46
      case inr h55 =>
        -- Conjunctions on the left can always be decomposed.
        let h56 := h43.left
        let h57 := h43.right
        -- Conjunctions on the left can always be decomposed.
        let h58 := h56.left
        let h59 := h56.right
        -- Disjunctions on the left can always be decomposed.
        cases h57
        case inl h60 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- One of the premise coincides with the conclusion.
          exact h58
          -- One of the premise coincides with the conclusion.
          exact h58
        case inr h61 =>
          -- Conjunctions on the left can always be decomposed.
          let h62 := h61.left
          let h63 := h61.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- One of the premise coincides with the conclusion.
          exact h58
          -- One of the premise coincides with the conclusion.
          exact h58
    case inr h64 =>
      -- Conjunctions on the left can always be decomposed.
      let h65 := h43.left
      let h66 := h43.right
      -- Conjunctions on the left can always be decomposed.
      let h67 := h65.left
      let h68 := h65.right
      -- Disjunctions on the left can always be decomposed.
      cases h66
      case inl h69 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h67
        -- One of the premise coincides with the conclusion.
        exact h67
      case inr h70 =>
        -- Conjunctions on the left can always be decomposed.
        let h71 := h70.left
        let h72 := h70.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h67
        -- One of the premise coincides with the conclusion.
        exact h67
  case inr h73 =>
    -- Conjunctions on the left can always be decomposed.
    let h74 := h43.left
    let h75 := h43.right
    -- Conjunctions on the left can always be decomposed.
    let h76 := h74.left
    let h77 := h74.right
    -- Disjunctions on the left can always be decomposed.
    cases h75
    case inl h78 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h76
      -- One of the premise coincides with the conclusion.
      exact h76
    case inr h79 =>
      -- Conjunctions on the left can always be decomposed.
      let h80 := h79.left
      let h81 := h79.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h76
      -- One of the premise coincides with the conclusion.
      exact h76



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_252933910566516237653111721057 : ((True ∧ p2) → ((((p1 ∧ ((p5 ∧ (p5 ∧ ((p1 ∨ (p4 → p5)) ∧ p4))) ∧ (False ∨ ((p1 → p3) ∨ True)))) ∧ p3) ∨ (p2 → True)) ∨ True)) := by
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
theorem thm_5_vars_137839324233623327078673801659 : ((p3 ∨ (((p2 ∧ p5) ∧ ((p4 ∧ p1) ∧ ((p4 → p1) ∧ (p4 → False)))) → ((False ∧ p3) ∧ (False ∧ (False ∧ p3))))) ∨ ((p1 ∨ p1) ∨ p4)) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h3.left
  let h7 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- Conjunctions on the left can always be decomposed.
  let h10 := h7.left
  let h11 := h7.right
  -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
  have h12 : p4 := by
    -- One of the premise coincides with the conclusion.
    exact h8
  -- We have shown the premise of h11, we can now drive its conclusion.
  let h13 := h11 h12
  -- False on the left can always be used.
  apply False.elim h13
  -- Conjunctions on the left can always be decomposed.
  let h14 := h1.left
  let h15 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h16 := h14.left
  let h17 := h14.right
  -- Conjunctions on the left can always be decomposed.
  let h18 := h15.left
  let h19 := h15.right
  -- Conjunctions on the left can always be decomposed.
  let h20 := h18.left
  let h21 := h18.right
  -- Conjunctions on the left can always be decomposed.
  let h22 := h19.left
  let h23 := h19.right
  -- We want to use the implication h23 based on <expert-advice>. So we show its premise.
  have h24 : p4 := by
    -- One of the premise coincides with the conclusion.
    exact h20
  -- We have shown the premise of h23, we can now drive its conclusion.
  let h25 := h23 h24
  -- False on the left can always be used.
  apply False.elim h25
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h26 := h1.left
  let h27 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h28 := h26.left
  let h29 := h26.right
  -- Conjunctions on the left can always be decomposed.
  let h30 := h27.left
  let h31 := h27.right
  -- Conjunctions on the left can always be decomposed.
  let h32 := h30.left
  let h33 := h30.right
  -- Conjunctions on the left can always be decomposed.
  let h34 := h31.left
  let h35 := h31.right
  -- We want to use the implication h35 based on <expert-advice>. So we show its premise.
  have h36 : p4 := by
    -- One of the premise coincides with the conclusion.
    exact h32
  -- We have shown the premise of h35, we can now drive its conclusion.
  let h37 := h35 h36
  -- False on the left can always be used.
  apply False.elim h37
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h38 := h1.left
  let h39 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h40 := h38.left
  let h41 := h38.right
  -- Conjunctions on the left can always be decomposed.
  let h42 := h39.left
  let h43 := h39.right
  -- Conjunctions on the left can always be decomposed.
  let h44 := h42.left
  let h45 := h42.right
  -- Conjunctions on the left can always be decomposed.
  let h46 := h43.left
  let h47 := h43.right
  -- We want to use the implication h47 based on <expert-advice>. So we show its premise.
  have h48 : p4 := by
    -- One of the premise coincides with the conclusion.
    exact h44
  -- We have shown the premise of h47, we can now drive its conclusion.
  let h49 := h47 h48
  -- False on the left can always be used.
  apply False.elim h49
  -- Conjunctions on the left can always be decomposed.
  let h50 := h1.left
  let h51 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h52 := h50.left
  let h53 := h50.right
  -- Conjunctions on the left can always be decomposed.
  let h54 := h51.left
  let h55 := h51.right
  -- Conjunctions on the left can always be decomposed.
  let h56 := h54.left
  let h57 := h54.right
  -- Conjunctions on the left can always be decomposed.
  let h58 := h55.left
  let h59 := h55.right
  -- We want to use the implication h59 based on <expert-advice>. So we show its premise.
  have h60 : p4 := by
    -- One of the premise coincides with the conclusion.
    exact h56
  -- We have shown the premise of h59, we can now drive its conclusion.
  let h61 := h59 h60
  -- False on the left can always be used.
  apply False.elim h61



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309934326743618297012266643296 : (p2 ∨ ((True ∧ ((p3 → (((p4 ∧ False) → (False ∧ (p1 ∨ (p4 → p3)))) → p4)) ∧ (p4 ∧ p2))) ∨ (((p4 ∧ p3) ∨ False) ∨ (p4 → p4)))) := by
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
theorem thm_5_vars_259762461227272428035444063644 : ((p1 → p2) → ((((p4 ∨ (p4 → False)) ∨ p5) → p4) → ((True → p1) → ((p3 → ((p1 → (p5 → p2)) ∧ (p2 ∨ p2))) ∨ (True → False))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h5
  -- Implications on the right can always be decomposed.
  intro h6
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h7 : p1 := by
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h8 := h1 h7
  -- One of the premise coincides with the conclusion.
  exact h8
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h9 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h10 := h3 h9
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h11 : p1 := by
    -- One of the premise coincides with the conclusion.
    exact h10
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h12 := h1 h11
  -- One of the premise coincides with the conclusion.
  exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345644769056661364287038213372 : (p3 → ((p3 ∧ ((p1 ∨ True) ∧ ((((True ∧ ((p5 ∨ p4) ∨ p1)) ∨ False) ∨ (p3 ∨ (p2 ∨ (p3 ∧ (p3 ∨ (True ∧ p3)))))) → p1))) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134356321796797117824992048488 : (((False ∨ ((((False ∧ p3) ∨ p4) → (True ∨ (((p1 → False) ∨ False) ∧ (((p2 ∨ True) ∧ True) ∨ p2)))) → False)) ∨ False) ∨ (p5 → (True ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_140554212641596860015185117673 : ((((p4 → (((p2 ∧ p1) ∧ p1) ∧ (p4 ∨ True))) ∨ (False ∨ ((p4 ∧ False) → p1))) ∨ (p3 → ((p3 → p5) → True))) → (p5 → (False ∨ p5))) := by
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
      -- One of the premise coincides with the conclusion.
      exact h2
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
        exact h2
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_212737008498537111015564285256 : ((p1 → ((True ∧ True) ∧ True)) ∧ (p1 → ((((p1 → False) ∧ (p1 → p3)) → (False ∧ (p5 ∨ p5))) ∨ (((False → True) → (p5 → False)) → p2)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h6 : p1 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h7 := h4 h6
  -- False on the left can always be used.
  apply False.elim h7
  -- Conjunctions on the left can always be decomposed.
  let h8 := h3.left
  let h9 := h3.right
  -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
  have h10 : p1 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h8, we can now drive its conclusion.
  let h11 := h8 h10
  -- False on the left can always be used.
  apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119458058205782373285763540391 : ((p4 → (((p5 ∨ p1) → True) ∧ ((p1 → ((p2 → (p3 ∨ (((True ∧ p1) ∧ (p5 ∧ p4)) ∨ p1))) ∧ (p3 ∨ p2))) ∧ p4))) ∨ (p5 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135025741225604250105805446348 : (((p3 → (True → ((True ∧ (p1 ∧ ((False → p3) ∨ ((p4 ∧ p4) → ((False → False) ∧ False))))) ∨ p2))) ∧ (p4 ∨ p4)) ∨ (True ∧ (p2 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_562710674756577056091738022226 : (((p5 ∨ ((((p4 ∧ ((p1 → True) → ((False ∨ (p4 → p5)) → p4))) ∨ False) ∧ ((p3 ∨ p2) ∧ p3)) ∨ (((False ∨ False) ∨ p3) → True))) ∧ True) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51314305563114485183249542388 : (((p4 ∨ ((p2 → ((((True ∨ True) ∨ (p3 ∨ (False ∧ p2))) ∧ False) ∨ (p2 ∧ p5))) ∨ True)) ∨ ((p2 ∧ (True → False)) → (p3 → p3))) ∨ p5) := by
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
theorem thm_5_vars_139124510031112099323717303395 : (((((((p4 → p1) ∧ (p3 → p2)) ∨ (p5 → p3)) ∨ (False ∨ (p2 → p1))) ∧ ((True ∨ (p5 ∧ p3)) ∨ True)) ∨ p2) → ((p4 ∨ p3) ∨ True)) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Conjunctions on the left can always be decomposed.
        let h7 := h6.left
        let h8 := h6.right
        -- Disjunctions on the left can always be decomposed.
        cases h4
        case inl h9 =>
          -- Disjunctions on the left can always be decomposed.
          cases h9
          case inl h10 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h11 =>
            -- Conjunctions on the left can always be decomposed.
            let h12 := h11.left
            let h13 := h11.right
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
        cases h4
        case inl h16 =>
          -- Disjunctions on the left can always be decomposed.
          cases h16
          case inl h17 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h18 =>
            -- Conjunctions on the left can always be decomposed.
            let h19 := h18.left
            let h20 := h18.right
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
        case inr h21 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
    case inr h22 =>
      -- Disjunctions on the left can always be decomposed.
      cases h22
      case inl h23 =>
        -- False on the left can always be used.
        apply False.elim h23
      case inr h24 =>
        -- Disjunctions on the left can always be decomposed.
        cases h4
        case inl h25 =>
          -- Disjunctions on the left can always be decomposed.
          cases h25
          case inl h26 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h27 =>
            -- Conjunctions on the left can always be decomposed.
            let h28 := h27.left
            let h29 := h27.right
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
        case inr h30 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
  case inr h31 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148966824115855385960327693256 : ((((p5 → p5) ∨ p2) ∧ (p5 ∧ (True → (p3 ∨ (((p5 ∧ (False → p4)) ∨ ((p1 ∨ p3) ∨ p5)) ∨ True))))) ∨ (((p2 ∧ p3) ∧ p5) → p3)) := by
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
theorem thm_5_vars_670808527057102422885595712650 : ((((p1 ∧ (((True → ((p4 ∨ True) → (p1 ∧ p1))) → True) → ((p3 ∧ (p5 ∨ (p1 → False))) ∨ (p3 ∧ p5)))) ∨ (False ∨ (True ∧ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225685682087167505164644479769 : (((p3 → False) ∧ False) ∨ ((((p3 → p1) ∧ (((p2 ∨ (True ∨ (p4 → (p1 → True)))) → ((False → (False → p2)) ∨ False)) → p2)) ∨ p3) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158397071719410050312933220101 : (((p4 → p2) ∧ (True → (p3 ∧ ((p4 ∧ (p3 ∧ ((True ∨ ((p4 → True) ∧ p5)) → p5))) ∨ p5)))) ∨ ((True ∨ (p4 ∨ (p5 ∨ p5))) ∧ True)) := by
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
theorem thm_5_vars_46881789804125274572722428632 : ((((((p5 ∧ p5) ∨ ((p3 ∧ p1) ∧ ((p1 ∨ ((((p4 ∨ p5) ∧ p5) → True) → (False → p2))) ∧ p4))) ∧ False) ∨ True) ∨ (p2 → True)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158073935854742038104429982846 : ((((p2 → (p5 → (p1 ∧ p5))) → p5) → ((p4 ∨ (p3 ∧ ((True → p1) ∧ p3))) → (p2 ∨ p5))) ∨ ((p5 ∨ p1) ∨ (p4 ∨ (p4 → p4)))) := by
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
theorem thm_5_vars_40056529071950017729452319816 : (((((((p5 ∨ True) → (((p5 ∨ (False ∨ p5)) ∨ p4) → ((p5 ∧ (True ∧ p4)) ∨ (p4 → p1)))) → (p3 ∧ p1)) ∨ p1) ∧ p5) ∨ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307458614122654306329905173474 : (p1 ∨ (p5 ∨ ((True ∧ p5) → ((((p2 ∧ p1) ∨ ((True ∨ (p5 ∧ p4)) ∧ ((False ∨ True) ∨ (p5 ∧ p4)))) ∧ (p5 → (p1 ∨ True))) ∧ p5)))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h1.left
  let h6 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h7 := h1.left
  let h8 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_618837183307722367990641921421 : (((((False ∨ (False ∨ p3)) ∧ (((p3 ∧ (((((p5 ∧ False) ∨ p5) ∨ p3) ∧ p2) → ((True ∧ False) ∧ (p2 ∧ p5)))) ∧ p5) ∨ p4)) ∨ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156796022191501678518811163256 : (((p4 ∧ ((p2 ∧ (False ∨ ((True ∨ True) → ((p1 → p4) ∧ (p1 → (p2 → p5)))))) ∨ p5)) ∧ p5) ∨ ((True ∨ (p1 ∧ (p2 ∧ p1))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171849863554101282919504479038 : ((((p3 ∨ False) ∨ ((((p5 → (p5 ∧ p5)) → (True ∧ p3)) ∧ p1) ∧ p2)) → p5) ∨ (p5 → ((p2 ∨ p1) → (p1 → (True ∧ (p3 ∨ p1)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_176292816451075993644588598342 : ((((False ∧ p1) ∨ (p1 ∧ (p4 ∨ (False ∨ (p5 ∧ p3))))) ∨ (p4 ∨ True)) ∧ (((p5 ∨ ((p2 ∧ False) ∨ p3)) → p3) ∨ ((False → p5) ∨ True))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354023575573229978620825731799 : (p4 → (p4 → (((((((((True ∨ (p3 ∨ (p3 → p4))) ∨ False) ∨ (p3 ∧ True)) ∨ p1) ∧ (p5 ∨ p1)) → p1) ∨ (p5 ∨ p4)) → p2) → p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : (((((((True ∨ (p3 ∨ (p3 → p4))) ∨ False) ∨ (p3 ∧ True)) ∨ p1) ∧ (p5 ∨ p1)) → p1) ∨ (p5 ∨ p4)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112565053454643856922264140312 : ((((p5 ∧ (((p2 → (p1 ∨ (((p4 ∨ True) → p2) ∧ ((p3 → p2) ∧ (p1 ∧ False))))) → (p2 ∧ False)) ∨ False)) → False) → p1) ∨ (p4 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39918634208533010352643811151 : (((p3 → ((((p1 ∨ p5) ∧ ((p2 → p4) ∧ p1)) → (False ∧ (True ∨ (p4 ∧ ((False ∧ p2) ∨ True))))) ∨ (p1 → (p5 → p3)))) ∧ True) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206411168905171481800494906009 : ((p3 ∨ (False ∧ (p4 ∨ (p4 ∨ p5)))) ∨ ((True ∨ (((((p1 → (False ∨ True)) ∨ (True → True)) ∨ p3) ∨ False) ∨ (True → p1))) → (p2 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_698431620453815731675591032893 : ((((((p2 ∧ p5) ∨ ((p4 ∨ p2) ∧ p2)) ∧ (p4 ∨ (p3 ∨ True))) ∨ ((p3 → (p1 → ((p5 ∨ p3) → p4))) ∨ (True → (p4 ∨ True)))) ∨ False) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_610319524673961618714460434585 : ((((((False → ((((True → False) ∧ p4) ∧ p3) ∨ (True → (((((p2 → (p2 ∨ p1)) ∧ p4) ∨ p5) → p2) → p2)))) ∨ p2) → p3) ∨ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_349067278216077203778385905967 : (p3 → (p5 ∨ ((p2 → p1) → ((False → False) → (((((p1 ∧ (p5 → (True ∨ ((True → p5) → True)))) ∨ p2) ∧ p3) → (p3 → p4)) ∨ p3))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_311824891554180275413763488324 : (p2 ∨ (p1 ∨ ((False ∧ (p3 ∧ (p2 ∨ ((p1 ∧ p2) → (((p4 → p2) ∨ p3) → False))))) ∨ ((p5 ∨ (p2 ∨ ((False → False) ∨ p2))) ∨ p1)))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_608926584119138803720318215603 : (((((((p5 ∨ (((((True ∨ (p2 ∨ True)) ∨ p3) ∧ p5) ∧ p2) ∧ p3)) → p5) → ((p3 ∨ p3) → ((p5 ∧ p5) → p2))) ∨ True) ∨ p4) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_303956306808551744765965231962 : (p1 ∨ (((((False ∨ p1) ∨ p1) → p3) → (p1 → (((p1 → (p2 ∧ ((False ∧ p1) ∨ ((p2 ∧ p2) ∨ p1)))) ∨ p4) ∨ (p3 ∨ p1)))) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178920185468964773566510107674 : (((p2 → True) ∧ ((((p2 ∨ p2) ∨ p1) ∨ p4) ∧ (p1 → (p2 ∧ True)))) ∨ (((p4 ∨ True) → p4) → (((p2 ∧ False) ∨ p1) → (False → False)))) := by
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
theorem thm_5_vars_355865124225821733814515935787 : (p5 → (((((True ∨ p4) ∧ p2) ∨ p3) ∧ ((p5 → False) ∨ ((p4 → ((p3 ∨ p4) ∧ ((False ∨ True) ∨ False))) → p3))) ∨ (p5 → (p5 → p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61340728414428913321729138743 : ((p1 ∧ (((p2 ∨ (p1 → (p1 ∧ ((True ∧ ((p4 ∨ (((p1 ∨ (p2 ∨ p2)) → p3) → p3)) ∧ True)) ∧ (p3 ∨ p5))))) → p3) ∧ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_320115191613886373848669446079 : (p4 ∨ ((p3 ∧ (p2 ∧ p5)) → ((p1 ∨ ((p2 ∨ p1) ∧ ((p2 → p2) → p4))) ∨ (((p3 → (False ∨ (False → p2))) ∧ p2) ∨ (p2 ∨ p4))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111277149164816001436071337202 : ((((True ∨ p3) → ((p5 → (True ∧ p5)) → (p2 ∧ ((p5 ∨ ((p5 → (p2 ∨ p1)) ∧ p2)) ∨ ((p2 ∧ True) ∧ p3))))) ∧ p4) ∨ (p2 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_653727529245964600104332172441 : ((((((p5 ∨ (((p1 ∧ (False → (p3 ∨ ((True ∧ (True ∧ p3)) ∨ (True ∧ True))))) → p3) ∧ p3)) ∧ (p4 → p5)) ∧ False) ∨ (True ∨ p3)) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_178942217801359797293464928241 : (((p2 ∧ p1) ∨ (p1 ∨ (p2 ∨ ((((p4 ∨ False) → p1) → p3) ∨ True)))) ∨ (p5 ∨ ((p1 ∨ p3) → ((False → (False ∨ (p5 ∨ p3))) ∨ p2)))) := by
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
theorem thm_5_vars_42093973786431275693408351963 : ((((True ∧ True) → ((p2 ∨ ((p5 ∧ (True ∨ p5)) ∨ p5)) → ((p4 ∨ (True ∧ False)) ∨ ((p2 ∨ p1) ∨ (p3 ∨ (False ∨ p4)))))) ∨ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158016024547773347550203063872 : ((((p4 ∨ (p4 ∨ (p4 → p2))) → p2) ∧ (((False ∨ (p4 → p4)) → p3) → ((p2 ∨ p2) ∧ True))) ∨ ((p3 ∨ p3) → ((p2 → True) → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41531716676760141615415044992 : (((((((p5 → False) ∧ False) → (False ∧ (True ∧ False))) ∧ p2) ∨ (p1 → (p4 ∨ ((p3 ∨ ((p2 → p5) → (True → p5))) ∨ p1)))) ∨ p3) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148654847235578799684593697155 : ((((True ∧ False) ∨ (p1 → ((p5 → p3) ∨ True))) ∧ (((p2 ∧ (p3 ∨ p5)) ∨ p4) ∧ ((p2 ∨ p2) ∧ p4))) ∨ (p1 ∨ ((False ∨ p1) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_318859596082871296148461335911 : (p4 ∨ (((((p3 ∨ (p4 ∧ p5)) ∧ (p4 ∨ p4)) ∧ (p2 ∨ ((((p1 ∨ p2) ∨ (p3 ∧ p5)) → p3) ∧ p3))) → p5) ∨ ((p3 ∨ True) ∨ p4))) := by
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
theorem thm_5_vars_136695179315142231555051827982 : (((False ∧ True) ∧ (((False ∨ False) ∧ p1) ∨ ((p5 ∨ (p2 → ((p3 ∧ (p3 ∧ (p1 → p5))) → p5))) ∧ (p4 ∨ False)))) ∨ ((p2 ∨ True) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165661260415062743895099162872 : ((((p4 ∨ p5) ∨ (p2 → (p5 ∧ p1))) ∨ (((p5 → (p2 ∨ p5)) ∧ (p1 ∧ p3)) ∨ p1)) ∨ (((((p5 → True) → p5) → p2) → p4) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200135517946672505855183569165 : (((p3 → (True → p1)) ∧ (p2 ∨ (False → p3))) → ((p5 → (p3 ∧ (p1 ∧ False))) ∨ (p5 → (p4 → ((((False → p2) → True) ∨ p2) ∨ p2))))) := by
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
    -- Implications on the right can always be decomposed.
    intro h6
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- Implications on the right can always be decomposed.
    intro h9
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h10
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204258804181936222836414259839 : ((((p3 ∧ p2) ∨ (p2 ∧ p2)) ∧ p4) ∨ (((True ∧ p3) ∨ False) ∨ (((p2 ∧ False) ∨ p4) ∨ (p3 ∨ (False → (((False ∨ p3) → p5) ∧ p1)))))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- False on the left can always be used.
    apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_194744439882183962722736630417 : (((p4 ∧ ((p5 ∧ p1) ∨ (True ∧ False))) ∨ True) ∧ ((p1 ∨ (True ∨ True)) ∧ ((((p2 → (p3 → p5)) → p3) → p2) ∨ ((False → p4) ∨ p4)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47659419984718999814433959519 : ((((((False ∨ (p1 ∨ p5)) ∨ ((p3 ∧ p5) ∨ ((p5 → (p5 ∨ p2)) ∧ p2))) ∨ (p2 ∨ ((False → False) ∨ p2))) ∧ p3) → (p4 → p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166216041302271257977151980963 : ((p2 ∧ ((((p4 ∨ p4) ∨ False) ∨ (p1 → ((((True ∧ p4) ∧ False) → p4) ∧ True))) ∨ p2)) ∨ (p1 ∨ ((p5 ∨ p3) → (p1 ∨ (p4 ∨ True))))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_738472570382842509446143178960 : ((((p1 ∧ p3) ∨ ((p1 → ((p5 ∧ (((((p5 ∧ p2) → True) → p4) ∨ (p3 ∧ p3)) ∨ (p3 ∨ p2))) ∧ (p2 ∧ p3))) ∨ (True ∨ p5))) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_706997738395141493240697024569 : (((((p1 ∧ ((p2 ∧ (p3 ∧ p3)) ∨ True)) ∨ p4) ∨ ((p1 ∧ (p2 ∨ (((p2 → (True ∨ (p5 ∧ p2))) → p1) → (p3 ∧ True)))) ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134336112723040366598615347553 : (((p4 ∧ (((((p1 → (p5 ∧ True)) ∧ (True → True)) ∨ (p1 ∨ ((True ∨ (True → p1)) ∧ p3))) ∧ p2) ∧ p5)) ∨ False) ∨ ((True ∧ True) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150024433167196332203343976651 : ((p5 ∨ ((((p3 ∨ p3) ∨ p1) ∨ p4) ∧ (p4 ∧ (p1 ∨ (p1 ∨ (False → ((True ∧ p3) → (p1 ∨ p2)))))))) ∨ ((True ∨ (True ∧ p5)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233416176971506041746059776956 : ((False ∨ (p2 ∨ p5)) → ((((True → p3) → (((p3 ∧ p1) ∧ p3) ∨ p4)) ∨ p3) ∨ (False → (p4 ∨ ((True ∧ p1) → (p2 ∨ (p3 ∧ p5))))))) := by
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
      -- False on the left can always be used.
      apply False.elim h5
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h7
      -- False on the left can always be used.
      apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149410275533698075101415981136 : ((True ∧ ((((p5 → ((p2 ∨ (p2 ∧ False)) ∧ p3)) ∨ (True ∧ (p5 → p5))) ∨ p1) → (False ∨ (True ∧ p4)))) ∨ (False → (p4 ∨ (True → p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_238118631518629220980731877347 : ((True ∨ p3) ∧ ((p4 ∧ (p4 → (p5 ∧ (p5 → (((True ∧ ((((((p4 ∧ p2) ∨ p4) → True) ∧ p5) ∨ p1) ∧ p2)) ∧ p2) → p1))))) ∨ True)) := by
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
theorem thm_5_vars_312495738269964336805229408260 : (p2 ∨ (p5 → ((((((False → p2) → (p2 → p3)) → False) ∨ p4) → p1) → ((p3 ∧ (True → (p2 → ((True ∨ (p3 ∧ p5)) ∧ p1)))) ∨ True)))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148605059815782972167727495380 : (((p4 → (((p2 ∧ (p5 ∨ (p2 ∧ p3))) → p1) → p1)) ∨ ((p1 → (p5 ∧ (p4 → p3))) ∧ (p4 → p2))) ∨ (((p5 ∧ p2) ∧ p3) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_265776558360960890842702563670 : (True ∧ (p4 ∨ (((p4 ∧ p1) ∧ (((p4 → True) ∧ (((p3 ∧ p1) ∧ p5) → p4)) → p3)) ∨ (((p5 ∧ False) → (False ∧ False)) → (p3 → True))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117561748844077695601742552884 : ((p2 ∧ ((p3 ∨ (((p4 → p1) ∨ p5) → True)) ∧ (((p3 ∧ (p2 ∨ p5)) ∧ ((p5 ∨ (p2 → p4)) → (p1 → True))) ∧ p3))) ∨ (p3 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_665457993725825189349830977796 : (((((((p4 ∧ p3) ∧ ((p4 ∨ (p1 ∨ (p1 ∨ p4))) ∨ (((False → False) ∧ (p3 → p2)) ∨ True))) ∧ p5) ∨ True) ∧ (p5 ∨ (p1 → True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148937203687380674608829056829 : (((p4 ∧ (True ∨ (p1 ∧ True))) → (((p1 ∧ p2) ∨ (p4 → (p2 ∧ (p4 ∨ True)))) ∨ (p4 ∨ (True → p4)))) ∨ (p4 ∨ ((p5 → p4) ∧ p5))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315660756378033572290070600401 : (p3 ∨ ((p3 ∧ False) ∨ (p1 → (p5 ∨ ((p4 ∧ (p4 ∨ p2)) → (((p4 → (p1 → True)) ∧ ((True → False) → ((p5 ∧ p5) ∨ p5))) ∨ p2)))))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h6
    -- Implications on the right can always be decomposed.
    intro h7
    -- True on the right can always be proven directly.
    apply True.intro
    -- Implications on the right can always be decomposed.
    intro h8
    -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
    have h9 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h8, we can now drive its conclusion.
    let h10 := h8 h9
    -- False on the left can always be used.
    apply False.elim h10
  case inr h11 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113417012419321124548674138072 : ((((((((p3 ∨ False) ∧ (p3 ∧ False)) ∨ (p4 → p3)) ∨ p4) ∧ ((p5 ∧ ((p3 ∨ p3) ∧ p1)) → True)) ∧ p4) ∨ (p2 ∨ False)) ∨ (p3 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230818800850677449180641317405 : (((False ∧ p3) ∨ True) → (((((((True → p4) → (p1 ∨ p2)) ∨ False) ∨ p4) ∧ (p1 → ((p1 ∨ p2) ∨ (True ∧ p2)))) → (False ∧ False)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- False on the left can always be used.
    apply False.elim h3
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114713264440169552511923605380 : (((((True ∨ (p4 → p2)) ∧ ((p2 ∨ ((p4 → p4) ∨ p4)) → (p1 → p4))) → p4) → ((p2 ∨ ((True ∧ p2) ∨ p3)) ∨ p5)) ∨ (True ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351739520189678956630951010192 : (p4 → ((p2 ∧ (((False ∨ p5) ∧ (True ∧ ((p5 ∧ (p2 → p1)) → p2))) ∨ p4)) ∨ ((p2 ∨ True) → (((True ∧ False) → p3) ∧ (False ∨ p4))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- False on the left can always be used.
  apply False.elim h5
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68339844439017782496450632901 : ((p3 → ((((False → (p5 ∨ (p1 ∨ True))) ∨ False) → ((p5 ∧ p1) ∨ p1)) ∨ (p3 ∨ (((p3 → True) ∨ ((p3 → p3) ∨ p2)) ∧ False)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48322347491248100090774391718 : (((p1 ∨ ((((True ∧ (p1 ∧ False)) → True) ∨ (p1 ∧ ((p2 ∨ ((p1 ∧ p5) → p1)) ∨ (p2 ∨ (p4 → p4))))) ∨ False)) → (p4 ∨ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52098876170355787289906811702 : (((((True ∨ p2) ∨ ((False ∨ True) → ((p4 ∧ (p2 ∨ (p1 → False))) ∨ False))) ∨ p5) → ((p1 ∨ ((p1 ∨ (p3 ∨ p3)) ∨ p3)) ∧ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324206421779124467751009510034 : (p5 ∨ (((True ∨ p1) → ((True ∨ (p2 ∧ False)) ∧ (False ∧ p2))) → (p3 → ((p3 ∨ p3) → (((p4 ∨ (p1 ∨ False)) → p3) → (p4 → p1)))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h5
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h6 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h7 : (True ∨ p1) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h8 := h1 h7
    -- We need to get the right conjuct of h8 based on <expert-advice>.
    let h9 := h8.right
    -- We need to get the left conjuct of h9 based on <expert-advice>.
    let h10 := h9.left
    -- False on the left can always be used.
    apply False.elim h10
  case inr h11 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h12 : (True ∨ p1) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h13 := h1 h12
    -- We need to get the right conjuct of h13 based on <expert-advice>.
    let h14 := h13.right
    -- We need to get the left conjuct of h14 based on <expert-advice>.
    let h15 := h14.left
    -- False on the left can always be used.
    apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_326995414637335696564268425443 : (True → ((((p1 ∨ (((((p1 ∨ p2) → False) ∨ (True → p5)) ∧ True) ∨ False)) ∧ ((False ∧ p5) ∧ p1)) ∨ ((p3 ∨ True) ∨ (p3 → True))) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
theorem thm_5_vars_301957122090480731220013966943 : (False ∨ ((p4 ∨ p3) → (p4 → (((p3 ∨ (p3 ∨ p3)) ∧ ((False ∨ (True ∧ ((p2 → True) → True))) ∧ p1)) ∨ ((p5 → True) ∨ (p3 → False)))))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h4
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h6
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_26612605583925681539087896839 : (((p2 ∧ p4) ∨ ((p4 ∧ (p2 → ((((((p3 ∨ p1) ∧ p1) ∨ p1) → p3) ∧ (((p4 → p4) ∨ p4) ∨ (p3 ∨ p5))) → p5))) ∨ True)) ∧ True) := by
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
theorem thm_5_vars_54116665083047153960134506465 : (((p5 ∧ (((p3 ∧ p3) → (p2 ∨ (p3 → p2))) ∨ p3)) → (((((p4 ∨ p2) ∨ (p3 ∨ p4)) ∧ False) ∧ (p3 ∨ False)) ∧ (p2 ∨ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_624373358162634196872740452615 : ((((p3 ∨ ((p4 → True) ∧ ((False ∧ p3) ∧ (False ∧ (True ∨ (p2 ∨ (((False ∧ (True ∧ (p1 ∧ (p1 → p5)))) ∧ p5) ∨ False))))))) ∨ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111127990263703426088411114061 : (((((p1 → ((False → p4) ∧ False)) ∧ (p4 ∧ p3)) ∨ (((((p2 ∨ ((p5 → p2) ∨ p5)) ∧ True) ∧ p4) → p4) → p1)) ∧ p4) ∨ (p2 → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_229084633205133243073931580534 : ((p5 ∨ (p2 → p3)) ∨ ((p1 ∨ ((p1 → p3) ∨ ((((p3 ∨ p3) ∨ ((((False ∧ p2) ∧ p2) ∧ p5) ∧ False)) → p1) ∨ False))) ∨ (p5 → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66168580590068795824394278115 : ((p5 ∨ ((p3 ∧ ((True ∨ (True ∨ (((p2 ∨ p1) ∧ (((True ∧ p4) ∧ (p2 → p1)) ∧ p4)) → True))) → p3)) ∨ (p2 → (p1 ∨ True)))) ∨ False) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45252905315357928452889864456 : (((p1 ∧ ((p4 ∧ p5) → (((p4 → (p1 ∨ p2)) ∨ ((p1 ∨ p4) ∧ (p5 ∨ (p2 → (p3 → False))))) → ((True ∧ p3) ∨ p3)))) → p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161651880142805817214762326943 : ((p1 ∨ ((p5 ∨ (((p2 ∨ (((p1 ∨ False) → False) ∧ p4)) ∨ p1) → p3)) ∧ ((p3 → p2) ∨ True))) → (False ∨ ((p4 ∧ False) → (p4 → p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the left can always be decomposed.
    let h5 := h3.left
    let h6 := h3.right
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h12
        -- Implications on the right can always be decomposed.
        intro h13
        -- Conjunctions on the left can always be decomposed.
        let h14 := h12.left
        let h15 := h12.right
        -- False on the left can always be used.
        apply False.elim h15
      case inr h16 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h17
        -- Implications on the right can always be decomposed.
        intro h18
        -- Conjunctions on the left can always be decomposed.
        let h19 := h17.left
        let h20 := h17.right
        -- False on the left can always be used.
        apply False.elim h20
    case inr h21 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h22 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h23
        -- Implications on the right can always be decomposed.
        intro h24
        -- Conjunctions on the left can always be decomposed.
        let h25 := h23.left
        let h26 := h23.right
        -- False on the left can always be used.
        apply False.elim h26
      case inr h27 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h28
        -- Implications on the right can always be decomposed.
        intro h29
        -- Conjunctions on the left can always be decomposed.
        let h30 := h28.left
        let h31 := h28.right
        -- False on the left can always be used.
        apply False.elim h31



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44154957135245458342332532124 : (((((p2 → ((True → p3) ∨ (False ∨ (((p5 ∨ True) → False) ∧ (((p1 → True) → p5) ∧ False))))) → p2) → ((p1 ∧ False) ∨ p4)) → p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181471553709771865429724234404 : ((p4 ∨ ((p3 ∧ ((p5 ∧ True) → p4)) ∨ ((True → p3) ∧ (p3 ∧ p4)))) → ((((True → p1) → p5) ∧ (p2 ∨ p2)) → ((False ∨ True) ∨ p3))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h6 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Conjunctions on the left can always be decomposed.
        let h9 := h8.left
        let h10 := h8.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h9
      case inr h11 =>
        -- Conjunctions on the left can always be decomposed.
        let h12 := h11.left
        let h13 := h11.right
        -- Conjunctions on the left can always be decomposed.
        let h14 := h13.left
        let h15 := h13.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h14
  case inr h16 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h17 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h18 =>
      -- Disjunctions on the left can always be decomposed.
      cases h18
      case inl h19 =>
        -- Conjunctions on the left can always be decomposed.
        let h20 := h19.left
        let h21 := h19.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h20
      case inr h22 =>
        -- Conjunctions on the left can always be decomposed.
        let h23 := h22.left
        let h24 := h22.right
        -- Conjunctions on the left can always be decomposed.
        let h25 := h24.left
        let h26 := h24.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h25



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259951500059669054108688009762 : ((p1 → p5) → ((p3 ∧ False) ∨ (p2 → (((False ∨ ((p4 → p4) ∨ (False → p2))) ∧ (p5 ∧ False)) ∨ (p2 ∧ (((False → True) ∨ p1) ∧ p2)))))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_619633384203569146713226231125 : (((((p2 ∧ p3) ∧ ((p4 ∧ False) ∧ ((((p3 ∨ (p1 ∧ ((p5 ∨ False) ∧ False))) → (p2 ∨ p1)) ∧ p5) ∧ (p4 ∨ (p4 ∧ p3))))) ∨ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113177747946591014348366053837 : (((((((((p3 → (True → p5)) → (p2 ∧ p2)) → (p2 ∧ ((p4 ∨ p4) ∧ p4))) ∨ True) ∧ p3) ∨ False) ∧ p2) ∧ (p5 ∧ p4)) ∨ (True ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307156710545858078507826899206 : (p1 ∨ (False ∨ (True ∧ ((((p1 ∧ ((False ∨ ((p2 → p2) ∧ p5)) → p5)) ∨ p1) → (p2 ∨ (True ∨ (False → (p3 ∨ p1))))) ∧ (p4 ∨ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322213136187136527189239683034 : (p5 ∨ (((((((True → p4) ∧ (((p4 ∧ p5) ∨ (p4 ∨ p4)) ∨ (p2 ∨ p5))) → p3) ∧ p1) → (((p3 ∨ p5) ∨ p4) ∧ p1)) ∧ False) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307380968316146181647130387863 : (p1 ∨ (p4 ∨ ((p1 ∨ ((True ∧ p2) ∨ ((((((p2 ∨ p3) ∨ p4) → p3) ∧ True) ∨ False) → (p2 ∨ p1)))) ∨ (((False ∧ True) → p2) ∨ p2)))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_108260985887982501067653179578 : ((True ∧ ((((p5 ∧ p5) ∨ ((p3 ∨ p2) → (((False → p1) ∨ True) ∧ True))) → ((True ∨ p3) ∧ p4)) ∨ ((True → p2) → p2))) ∧ (True ∨ p4)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180670663364357228823846443960 : ((((p4 → (p3 ∧ (p5 ∨ False))) ∨ p2) → ((p4 → p4) ∨ (p5 ∨ False))) → ((True ∧ (p3 ∨ (p2 → ((False ∧ (p1 ∧ p5)) ∨ p1)))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149600365150592623939103217729 : ((p3 ∧ ((p3 ∧ ((p2 → ((True → True) ∨ (p5 → p2))) ∧ p3)) ∨ ((p3 ∧ (p3 ∧ p2)) ∨ (p2 → True)))) ∨ (p2 → ((True → True) ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



