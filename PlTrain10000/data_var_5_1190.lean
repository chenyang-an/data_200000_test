variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119235022043935089435487316651 : ((p2 → ((False → p4) → (p2 ∧ ((p1 ∨ (((p2 ∨ (p5 → ((p5 ∧ p2) ∧ p2))) ∧ p5) ∧ p4)) ∧ (False ∧ (p4 ∨ p4)))))) ∨ (p1 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231456506382834046031709187439 : (((p2 → p4) ∨ p1) → (p4 → (((((p4 ∧ True) ∨ p1) ∨ True) ∧ p5) ∨ ((((True ∧ p4) ∨ False) ∨ ((True → False) ∨ p3)) ∧ (p3 ∨ p4))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- One of the premise coincides with the conclusion.
    exact h2
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- One of the premise coincides with the conclusion.
    exact h2
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350036142149722879569929402547 : (p4 → (((((p3 → p3) ∧ (True → p2)) ∨ (((True ∨ (p5 → p1)) ∧ ((p3 ∨ p1) ∨ p4)) → ((p4 → (p3 ∧ p5)) → p5))) → p1) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351257437154996639867401248382 : (p4 → ((p4 ∧ (((False → ((((p3 ∧ (p4 ∧ True)) → p2) → p5) ∧ False)) → (True ∧ (p3 → p1))) → (p1 ∧ False))) ∨ (p3 → (p5 ∨ p4)))) := by
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
theorem thm_5_vars_52443107212785159398922451876 : (((p1 ∧ (((p3 ∨ (p5 ∧ ((False ∧ p4) → p1))) → (p2 ∧ False)) → False)) ∧ ((True ∧ p3) ∧ (((p3 ∨ p4) ∨ p5) → (False → p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67627302754173987754255607771 : ((p1 → (p5 ∧ (p2 ∨ (((p5 ∧ ((p1 → (((((p4 ∨ p1) ∧ True) ∧ p1) ∧ False) → p1)) → p3)) → p4) → (False ∧ (p2 ∨ p5)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55397065363922506882667336680 : ((((p1 → ((p2 ∨ p4) ∨ p1)) ∧ p1) → (((((p5 ∧ p5) ∧ p1) → (((p2 ∨ p5) ∨ ((p4 → True) ∨ False)) ∨ p4)) → False) → False)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h5 : (((p5 ∧ p5) ∧ p1) → (((p2 ∨ p5) ∨ ((p4 → True) ∨ False)) ∨ p4)) := by
    -- Implications on the right can always be decomposed.
    intro h6
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h7.left
    let h10 := h7.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h10
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h11 := h2 h5
  -- False on the left can always be used.
  apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166685618875361459116957201653 : ((p2 → ((p1 ∧ p2) ∧ (p2 → (p4 ∧ ((p1 → (p5 ∨ p5)) ∨ ((p3 ∨ True) → False)))))) ∨ ((False → p1) ∨ ((True ∧ (p3 ∧ p2)) ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171565318550061337638813061162 : ((((p5 → (p5 → ((p1 ∧ (True ∧ ((p4 ∨ p5) ∨ p1))) → p5))) → p5) ∨ False) ∨ ((((p4 ∧ p2) ∧ True) ∧ (p1 ∧ (p4 ∨ p3))) → p1)) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h8 := h3.left
  let h9 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h9
  case inl h10 =>
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h11 =>
    -- One of the premise coincides with the conclusion.
    exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217195472714562557662031333437 : ((((p2 ∨ p3) → False) ∨ False) → ((((True ∨ False) → (False ∧ p2)) ∧ (((p3 ∨ True) ∨ False) ∧ True)) → (True → (((p1 ∨ p1) ∧ p3) → p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
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
    -- Conjunctions on the left can always be decomposed.
    let h8 := h2.left
    let h9 := h2.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h12 =>
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- Disjunctions on the left can always be decomposed.
        cases h1
        case inl h14 =>
          -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
          have h15 : (p2 ∨ p3) := by
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h13
          -- We have shown the premise of h14, we can now drive its conclusion.
          let h16 := h14 h15
          -- False on the left can always be used.
          apply False.elim h16
        case inr h17 =>
          -- False on the left can always be used.
          apply False.elim h17
      case inr h18 =>
        -- Disjunctions on the left can always be decomposed.
        cases h1
        case inl h19 =>
          -- We want to use the implication h19 based on <expert-advice>. So we show its premise.
          have h20 : (p2 ∨ p3) := by
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h6
          -- We have shown the premise of h19, we can now drive its conclusion.
          let h21 := h19 h20
          -- False on the left can always be used.
          apply False.elim h21
        case inr h22 =>
          -- False on the left can always be used.
          apply False.elim h22
    case inr h23 =>
      -- False on the left can always be used.
      apply False.elim h23
  case inr h24 =>
    -- Conjunctions on the left can always be decomposed.
    let h25 := h2.left
    let h26 := h2.right
    -- Conjunctions on the left can always be decomposed.
    let h27 := h26.left
    let h28 := h26.right
    -- Disjunctions on the left can always be decomposed.
    cases h27
    case inl h29 =>
      -- Disjunctions on the left can always be decomposed.
      cases h29
      case inl h30 =>
        -- Disjunctions on the left can always be decomposed.
        cases h1
        case inl h31 =>
          -- We want to use the implication h31 based on <expert-advice>. So we show its premise.
          have h32 : (p2 ∨ p3) := by
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h30
          -- We have shown the premise of h31, we can now drive its conclusion.
          let h33 := h31 h32
          -- False on the left can always be used.
          apply False.elim h33
        case inr h34 =>
          -- False on the left can always be used.
          apply False.elim h34
      case inr h35 =>
        -- Disjunctions on the left can always be decomposed.
        cases h1
        case inl h36 =>
          -- We want to use the implication h36 based on <expert-advice>. So we show its premise.
          have h37 : (p2 ∨ p3) := by
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h6
          -- We have shown the premise of h36, we can now drive its conclusion.
          let h38 := h36 h37
          -- False on the left can always be used.
          apply False.elim h38
        case inr h39 =>
          -- False on the left can always be used.
          apply False.elim h39
    case inr h40 =>
      -- False on the left can always be used.
      apply False.elim h40



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_106198543915349306997788465078 : ((((p5 ∧ (p2 ∨ ((p4 ∧ p2) → p4))) → (p3 ∨ (p1 ∧ p5))) → (((p5 ∨ True) → (p5 ∧ (False ∧ p2))) → (False ∧ p2))) ∧ (p2 ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (p5 ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- False on the left can always be used.
  apply False.elim h6
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h7 : (p5 ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h8 := h2 h7
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- We need to get the left conjuct of h9 based on <expert-advice>.
  let h10 := h9.left
  -- False on the left can always be used.
  apply False.elim h10
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117032929479985426420430628009 : (((p2 ∨ p5) → (p4 ∨ (p3 ∨ (((p4 → (((p2 → False) → p3) → ((True ∧ p5) → p1))) ∨ True) ∨ (False ∨ (p4 ∧ p5)))))) ∨ (p5 ∧ p4)) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
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
theorem thm_5_vars_989187025386295580868021958666 : (((p3 ∧ (((p4 → ((p2 → p4) → ((p4 ∧ p4) ∨ (p4 → p5)))) → p5) ∧ (p4 → (p3 ∧ (((p5 ∧ p5) → (p5 ∧ False)) ∧ p4))))) → p5) ∧ True) := by
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
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h6 : (p4 → ((p2 → p4) → ((p4 ∧ p4) ∨ (p4 → p5)))) := by
    -- Implications on the right can always be decomposed.
    intro h7
    -- Implications on the right can always be decomposed.
    intro h8
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h7
    -- One of the premise coincides with the conclusion.
    exact h7
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h9 := h4 h6
  -- One of the premise coincides with the conclusion.
  exact h9
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44167573741621664941265116857 : (((((p5 → (p2 ∧ (p4 → p2))) ∨ (True ∧ (p3 ∨ ((p2 → (True ∨ (p2 → (p2 → p3)))) → p2)))) → (p3 ∧ (p2 ∨ p5))) → p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186142224899243977052621795409 : (((((False ∧ p3) ∨ p3) → ((False ∧ p5) ∧ (p2 ∨ False))) ∨ p2) → ((p2 → (p5 → (False ∨ p1))) ∨ (True ∨ (p3 → (True ∨ (p2 ∨ False)))))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60304926411523320193356649456 : (((p1 → p2) → (p3 ∨ ((((p3 ∧ p4) ∧ (False ∨ p1)) → (((p3 ∧ (True ∧ ((True ∧ p1) ∨ (p2 → p1)))) → p3) → p2)) ∧ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174792158472040470703903793350 : (((p3 ∨ p2) ∧ ((True ∨ (p2 ∧ ((p3 → False) ∧ (p3 ∧ p4)))) ∧ (True → False))) → (((p2 → False) → (p1 ∨ (p1 ∧ p5))) ∧ (p1 ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
      have h9 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h7, we can now drive its conclusion.
      let h10 := h7 h9
      -- False on the left can always be used.
      apply False.elim h10
    case inr h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- Conjunctions on the left can always be decomposed.
      let h14 := h13.left
      let h15 := h13.right
      -- Conjunctions on the left can always be decomposed.
      let h16 := h15.left
      let h17 := h15.right
      -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
      have h18 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h7, we can now drive its conclusion.
      let h19 := h7 h18
      -- False on the left can always be used.
      apply False.elim h19
  case inr h20 =>
    -- Conjunctions on the left can always be decomposed.
    let h21 := h4.left
    let h22 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h21
    case inl h23 =>
      -- We want to use the implication h22 based on <expert-advice>. So we show its premise.
      have h24 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h22, we can now drive its conclusion.
      let h25 := h22 h24
      -- False on the left can always be used.
      apply False.elim h25
    case inr h26 =>
      -- Conjunctions on the left can always be decomposed.
      let h27 := h26.left
      let h28 := h26.right
      -- Conjunctions on the left can always be decomposed.
      let h29 := h28.left
      let h30 := h28.right
      -- Conjunctions on the left can always be decomposed.
      let h31 := h30.left
      let h32 := h30.right
      -- We want to use the implication h22 based on <expert-advice>. So we show its premise.
      have h33 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h22, we can now drive its conclusion.
      let h34 := h22 h33
      -- False on the left can always be used.
      apply False.elim h34
  -- Conjunctions on the left can always be decomposed.
  let h35 := h1.left
  let h36 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h35
  case inl h37 =>
    -- Conjunctions on the left can always be decomposed.
    let h38 := h36.left
    let h39 := h36.right
    -- Disjunctions on the left can always be decomposed.
    cases h38
    case inl h40 =>
      -- We want to use the implication h39 based on <expert-advice>. So we show its premise.
      have h41 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h39, we can now drive its conclusion.
      let h42 := h39 h41
      -- False on the left can always be used.
      apply False.elim h42
    case inr h43 =>
      -- Conjunctions on the left can always be decomposed.
      let h44 := h43.left
      let h45 := h43.right
      -- Conjunctions on the left can always be decomposed.
      let h46 := h45.left
      let h47 := h45.right
      -- Conjunctions on the left can always be decomposed.
      let h48 := h47.left
      let h49 := h47.right
      -- We want to use the implication h39 based on <expert-advice>. So we show its premise.
      have h50 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h39, we can now drive its conclusion.
      let h51 := h39 h50
      -- False on the left can always be used.
      apply False.elim h51
  case inr h52 =>
    -- Conjunctions on the left can always be decomposed.
    let h53 := h36.left
    let h54 := h36.right
    -- Disjunctions on the left can always be decomposed.
    cases h53
    case inl h55 =>
      -- We want to use the implication h54 based on <expert-advice>. So we show its premise.
      have h56 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h54, we can now drive its conclusion.
      let h57 := h54 h56
      -- False on the left can always be used.
      apply False.elim h57
    case inr h58 =>
      -- Conjunctions on the left can always be decomposed.
      let h59 := h58.left
      let h60 := h58.right
      -- Conjunctions on the left can always be decomposed.
      let h61 := h60.left
      let h62 := h60.right
      -- Conjunctions on the left can always be decomposed.
      let h63 := h62.left
      let h64 := h62.right
      -- We want to use the implication h54 based on <expert-advice>. So we show its premise.
      have h65 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h54, we can now drive its conclusion.
      let h66 := h54 h65
      -- False on the left can always be used.
      apply False.elim h66



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134325110115718382684015908672 : (((p2 ∧ ((((p3 → (True → (p1 → p3))) ∨ p5) ∧ (p2 ∨ ((p5 → p2) ∧ (p5 ∧ (p4 → p5))))) → False)) ∨ p4) ∨ (p1 ∨ (p4 → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165034686017534096680170318357 : ((((True → (p3 ∨ p1)) → ((p1 ∧ p1) ∧ (p3 → ((p2 → (p1 ∧ p4)) ∧ False)))) → p4) ∨ ((p2 ∧ (p2 → (p5 ∨ p5))) → (p3 ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : p2 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_563647108367827500003094735936 : (((p5 ∨ (True ∧ ((((True → (p1 → False)) → p2) ∧ (((p4 ∨ p5) ∨ p2) ∧ p2)) → ((False ∨ (p3 ∨ (p2 ∨ (False ∨ p4)))) ∨ p1)))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
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
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h8 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h5
  case inr h9 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h5
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_302496123450223762856872832288 : (False ∨ (False ∨ (((p3 ∧ (((False ∧ False) ∨ ((p4 → ((p2 → p2) ∨ (p4 → True))) ∧ (True → False))) ∨ (p3 ∨ (p5 ∨ p4)))) ∨ False) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_382208694818794164858637475998 : (((((((((p3 → ((p1 ∨ p4) → p1)) → p5) ∨ ((False → p5) ∧ ((True ∨ True) → p4))) ∧ p4) ∧ ((p3 → p1) ∨ p4)) ∨ p4) ∨ True) ∧ True) ∧ True) := by
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
theorem thm_5_vars_244280515100363107790290649543 : ((False ∧ True) ∨ (((False ∨ p1) ∧ p1) → ((((False ∧ (((False ∧ (False ∧ p1)) → (False → False)) → p2)) ∧ p1) ∨ True) ∨ (p5 ∨ (False ∨ p4))))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190873112941882235806672751690 : (((((p2 ∧ False) ∧ p2) → (p5 ∨ True)) → (p4 → False)) ∨ (True ∨ ((p1 → ((((p2 ∨ p5) ∨ (p1 → True)) ∧ (p3 ∨ False)) ∧ p4)) → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52974046072485235295585535583 : (((((True → p4) ∧ (p3 → ((p3 → (p5 → p3)) ∨ p4))) → p1) ∧ ((((p4 → True) ∨ (p2 ∨ False)) ∧ (p4 ∨ p2)) ∧ (p5 → p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48996481819442468673491359314 : ((((p1 ∨ (p3 ∨ ((p2 → (((p3 → p3) ∧ False) ∧ ((((p1 ∨ True) ∨ p4) ∨ p4) ∨ p2))) ∨ p4))) ∨ False) ∨ ((p3 → p4) ∧ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173149154362117108875436449295 : ((p3 ∨ ((((True ∨ (p4 ∧ False)) ∧ True) → p4) → (((p5 ∨ p2) ∧ p3) ∨ p4))) ∨ (p1 → ((p4 ∧ (False ∧ ((p2 ∧ True) ∧ False))) ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_252405213030533642180461773861 : ((p5 → False) ∨ ((((p3 → (p3 ∨ (True ∨ True))) → False) ∨ (((p5 ∨ ((p4 → p5) ∧ p5)) ∨ p5) → True)) ∨ (p1 ∧ ((True → p2) → True)))) := by
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
theorem thm_5_vars_242135824918243909036853682255 : ((p2 → True) ∧ (((p1 ∧ (((((False → (p1 → p1)) ∨ p4) ∨ p5) → p1) → p3)) ∧ ((False ∨ (True ∧ (False → p1))) ∧ p1)) ∨ (True → True))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50278885494844774349246208516 : ((((p2 ∨ (True ∧ (((True ∨ (((p2 → (p4 ∧ p2)) ∧ p4) ∨ p4)) → p1) ∨ True))) ∨ (p1 ∧ True)) ∨ ((p4 ∨ p4) → (p5 → p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_810001187360081494175057060128 : (((p5 → (((p1 → ((p5 ∧ (((p3 ∨ p1) → p3) ∨ p1)) ∨ ((True → p5) ∨ True))) ∨ ((True ∧ p3) → False)) → ((p2 ∨ p5) → p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199563459079491211071250508118 : ((((((p3 ∨ p4) ∨ p5) → p4) ∨ True) → False) → (p5 ∧ ((p2 ∨ ((((p2 ∨ True) ∧ True) → p5) → (p5 ∧ ((p1 ∧ p2) → p4)))) ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((((p3 ∨ p4) ∨ p5) → p4) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h4 : ((((p3 ∨ p4) ∨ p5) → p4) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h4
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164777635136119919554231889740 : (((((((True → p4) ∨ p5) → p1) → p5) ∧ (p2 ∨ (False → (p1 → (p4 ∧ p3))))) ∨ False) ∨ (p2 → ((p2 ∧ p5) → ((True ∨ p3) ∨ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186537153527042721387960927571 : ((((True → (p5 → (p4 ∧ p2))) ∧ (p4 → p3)) ∨ (True → True)) → ((p3 ∧ p3) ∨ (False → (p5 ∨ (True ∧ (p3 → ((p3 ∨ True) ∨ p3))))))) := by
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
theorem thm_5_vars_181440564749177867198842235548 : ((p3 ∨ ((True ∨ (p5 ∨ (False → (True ∧ False)))) ∨ (p4 → (True → False)))) → ((((p2 → ((p1 → p4) ∧ p2)) ∨ True) ∨ p1) ∨ (p3 ∧ p4))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h5 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h6 =>
        -- Disjunctions on the left can always be decomposed.
        cases h6
        case inl h7 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h8 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
    case inr h9 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60655704877987760986809602637 : ((True ∧ (((((((((p4 → False) ∧ True) ∨ True) ∧ True) → (p2 → p5)) ∨ p3) ∨ p1) ∨ (p5 ∨ p1)) ∨ (p3 ∨ ((p1 ∨ p4) ∧ True)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_645821460512745278869291691276 : ((((p5 ∨ (True → (((p1 ∨ ((p2 ∨ ((p4 → (p3 ∧ p3)) ∧ (p2 ∨ ((p2 → p2) → p1)))) ∧ p3)) → (False ∧ p5)) ∧ p5))) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41474162501521849851599347476 : ((((((p5 → (p3 ∧ ((p2 ∨ p4) ∧ False))) ∨ p3) ∧ (False ∨ False)) ∨ (False → ((p4 ∧ ((True ∧ (p1 ∧ p5)) ∧ p3)) ∧ False))) ∨ p5) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- False on the left can always be used.
  apply False.elim h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66570461583974374066202476221 : ((True → ((p5 ∨ ((((p3 → p5) ∨ (p5 → p3)) → (((p3 ∨ (False ∨ p3)) ∧ p5) ∧ (False ∨ (p5 ∨ p4)))) ∨ p1)) ∨ (p4 → p4))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309309248520535597517667005060 : (p2 ∨ ((((((p5 ∨ p5) ∧ p3) → ((((True → ((p2 ∧ (False ∨ (p5 ∧ True))) → p5)) ∧ p4) ∨ p4) ∨ True)) → p4) ∨ p5) ∨ (p1 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177910001251822927462886980069 : (((((p4 ∧ p5) → ((p5 ∧ (False → p3)) ∧ p2)) → (p3 → False)) ∨ True) ∨ (p2 → ((p3 ∧ (False ∨ ((False ∨ p1) ∧ (p2 → False)))) ∧ p5))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317878054291734625539559774443 : (p4 ∨ (((p1 → p3) → ((p3 ∨ p1) → ((p2 ∧ (p4 → (p4 ∧ (p2 ∨ (p3 ∧ ((p2 ∧ (False → p4)) ∨ (True ∧ p5))))))) ∧ p4))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150368173350551465465231130937 : ((p5 → (True → ((p5 ∧ ((p3 ∨ p2) ∧ (p3 ∧ (True ∧ ((p4 ∧ (p5 ∨ p5)) ∨ (p5 → False)))))) ∧ p4))) ∨ ((p1 ∧ (p1 ∨ p5)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_3984799035331623656706222899 : (p1 ∨ ((p2 ∧ (((p4 → (True → p4)) ∧ ((False ∧ True) → p3)) ∧ (p3 ∨ True))) → (((False ∨ (p1 ∨ p3)) ∧ False) ∨ (p3 → p3)))) := by
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
  cases h5
  case inl h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- One of the premise coincides with the conclusion.
    exact h9
  case inr h10 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h11
    -- One of the premise coincides with the conclusion.
    exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_698837644806163575584110460795 : ((((True ∧ ((False ∨ p2) ∧ ((p4 → (False → (p1 ∧ True))) → True))) ∨ (False ∨ (p3 → ((True → (p1 → (p2 ∧ (p4 ∨ False)))) ∨ True)))) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_243946757018054584512458007092 : ((True ∧ p1) ∨ ((((p2 ∨ (((p3 → (p4 → (False ∨ (p5 → False)))) → p2) ∨ True)) → p4) → (p4 ∨ (p2 ∨ (True → (p3 ∧ p2))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322212423479649259150642603506 : (p5 ∨ ((((((((p5 ∨ (p4 ∧ p4)) ∨ p3) → False) ∨ (True ∧ (p2 ∨ p2))) → (True → p2)) ∧ ((p1 → True) ∧ (True ∨ False))) ∧ True) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44260395272937095259662950722 : ((((((((p5 ∧ False) ∨ True) ∨ ((p3 → (p2 → p3)) ∨ True)) → False) ∧ ((p5 ∧ p3) ∧ p2)) → ((True → (False ∨ p3)) → p2)) → p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_804354686680937134866728716692 : (((p3 → ((((p3 ∨ (p4 ∧ ((p4 → p3) ∧ p3))) ∨ (p2 → True)) ∧ p2) → (p1 ∨ (p3 → ((False ∧ (p3 ∨ (p1 ∧ p4))) ∨ p2))))) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h7
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h13
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
  case inr h14 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h15
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136043412726588098729713111477 : (((p5 ∨ ((p1 → (p5 ∧ (p2 ∨ (p4 → True)))) → p1)) → ((p4 ∧ ((p3 ∧ ((False ∧ True) ∧ p5)) ∨ p1)) ∨ p2)) ∨ (True ∨ (p2 → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_105600201057398906517767379028 : (((p1 ∨ ((((((p4 ∨ p4) ∧ (p5 → p1)) → p5) ∨ (False ∧ (True → p5))) → p3) ∨ p3)) → ((p1 ∨ (p3 ∨ True)) ∨ p3)) ∧ (True ∨ p1)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64908575637978114778038234918 : ((p2 ∨ ((True ∧ (p4 → ((p5 ∨ (p1 → (p3 ∧ (p2 → p4)))) ∨ (p1 ∨ ((p5 → p4) ∧ p2))))) ∨ (p1 ∧ (False ∧ (p1 → p3))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_645908467553602983694764386699 : ((((True → ((((p5 ∨ (True ∧ p5)) ∨ ((p2 ∨ ((p4 ∨ p1) ∨ (True → (p4 → p4)))) → p4)) ∨ (False → (p4 ∧ p2))) → p5)) → p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116422095920040936922113346904 : (((p4 ∨ (True ∨ p4)) → ((p3 ∨ ((p4 → p2) ∨ p3)) ∨ (((True ∧ (p1 ∧ (p4 ∧ p4))) ∨ p4) ∨ (False → (True ∨ p3))))) ∨ (p5 → p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h5
      -- False on the left can always be used.
      apply False.elim h5
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_641830243254971041365743900223 : (((((True → p4) → (((True → p2) ∨ p2) → ((True → True) ∨ ((p2 ∧ (p3 ∧ (True ∧ (p5 ∧ p2)))) ∧ ((p3 ∨ p1) ∨ p2))))) → p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38132909348026284075546177083 : (((((p2 ∧ p2) ∨ (((False ∧ ((p5 → ((p1 ∨ p3) → p3)) → (True ∧ p5))) ∧ True) ∧ (p5 ∧ p2))) ∧ (p1 ∨ (p2 → p3))) ∧ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49937501138097907854458073576 : (((((True ∧ ((True ∨ ((p3 ∨ p4) → False)) → (((p5 ∧ True) ∧ False) ∧ p2))) → p1) ∧ (p4 ∨ p4)) ∧ (False ∨ (False ∧ (False ∧ p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_226045742200718851893995969789 : (((p5 ∧ p1) ∨ False) ∨ ((p5 → (((p5 ∧ p3) ∨ (p1 ∧ True)) ∧ (((False → True) → ((p3 ∨ (p1 → p3)) ∨ False)) → p1))) ∨ (p3 → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174518562295808835001064186652 : (((p2 → (True → (p5 → (p3 ∨ p5)))) ∨ ((p2 ∨ ((p5 → p5) ∧ p4)) ∧ p3)) → (((p5 → (True ∧ ((p5 → True) ∧ p5))) → p2) → p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h4 : (p5 → (True ∧ ((p5 → True) ∧ p5))) := by
      -- Implications on the right can always be decomposed.
      intro h5
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h6
      -- True on the right can always be proven directly.
      apply True.intro
      -- One of the premise coincides with the conclusion.
      exact h5
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h7 := h2 h4
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h11 =>
      -- One of the premise coincides with the conclusion.
      exact h11
    case inr h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h12.left
      let h14 := h12.right
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h15 : (p5 → (True ∧ ((p5 → True) ∧ p5))) := by
        -- Implications on the right can always be decomposed.
        intro h16
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- True on the right can always be proven directly.
        apply True.intro
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Implications on the right can always be decomposed.
        intro h17
        -- True on the right can always be proven directly.
        apply True.intro
        -- One of the premise coincides with the conclusion.
        exact h16
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h18 := h2 h15
      -- One of the premise coincides with the conclusion.
      exact h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147299089256536730480507928591 : (((((p2 → (p4 → (((p1 → p5) → ((p5 ∧ p4) ∧ p4)) ∧ (p5 → (p5 ∧ p5))))) → p1) → p2) ∨ p4) ∨ (((p2 ∨ p3) ∧ True) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53955360454176639731761003390 : ((((((True → p4) → (p1 ∨ (p5 ∨ True))) ∧ p2) ∧ p4) → ((((p3 → p2) → (True ∧ p2)) → (p3 ∨ (p3 ∧ (p3 ∨ False)))) ∧ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148367105274680771890621003405 : (((((True → p1) → (((False ∨ p2) ∨ p2) ∨ (p4 ∨ (p2 ∨ p1)))) ∧ p4) ∨ (p3 ∨ (p2 ∧ (p5 → p1)))) ∨ (p3 → ((p1 ∨ True) ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_678019766390864952401949747565 : (((((p3 ∨ ((p2 ∨ ((((p5 ∨ (p5 → p1)) → p3) ∨ p4) → p4)) ∧ p4)) ∧ ((p5 ∨ p5) ∧ p4)) ∨ (((True ∨ True) ∨ p4) ∨ p5)) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227591810158394584759459649539 : ((False ∧ (p3 ∧ True)) ∨ (p3 → (p4 ∨ (p2 → (((p3 ∨ p2) → (p2 ∧ (p5 ∨ ((p3 ∨ p5) ∨ (False ∧ p4))))) ∧ (p3 ∧ (False → p2))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h5 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h8
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198115225522416792663856235712 : (((p4 → p3) ∨ ((p5 ∨ p5) ∧ (p5 ∨ p5))) ∨ (p3 → (p2 ∨ (p1 ∨ (True ∨ (False ∨ ((False ∨ (p3 ∨ (p3 ∧ (p5 → p5)))) ∧ True))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_710136369822090653778192371438 : (((((((p3 ∨ p4) ∨ True) ∨ p2) ∨ True) ∧ (p4 → ((p1 ∨ ((p2 ∨ ((p3 ∧ True) ∨ p4)) → p1)) → ((p4 ∨ (True ∧ p5)) → p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60936467139907882494561133768 : ((False ∧ ((p4 ∧ (p3 ∧ ((p1 ∧ ((((((p3 → (p3 ∨ True)) → p2) → False) → ((False ∨ p1) ∨ p2)) → p5) ∧ False)) ∨ True))) ∧ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314855512302940174359391722089 : (p3 ∨ (((((True ∨ (True ∧ p1)) ∨ (p5 → p1)) → (p4 ∧ p5)) ∨ p1) → (((False ∧ (p5 ∧ (((p4 ∨ p2) ∨ p2) ∧ p4))) ∧ p4) ∨ True))) := by
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
theorem thm_5_vars_183887015540363102977616390665 : ((((p5 ∧ (p5 → True)) → (((p3 ∧ p2) ∧ True) → False)) ∧ p5) ∨ (True ∧ ((p2 ∧ (((p4 ∧ (True ∨ True)) ∨ p2) ∨ p5)) ∨ (p1 ∨ True)))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46388707445451182705095320664 : ((((p2 ∨ (p1 ∧ ((p5 ∧ (p5 → (p4 → p1))) ∨ True))) ∨ ((((p1 ∨ (p5 ∨ p5)) ∧ p2) ∨ (True ∨ p5)) ∧ p4)) ∧ (False → True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42510337442880536947950258866 : (((False ∨ ((p4 → (p1 ∨ False)) ∨ (((p2 → (((p4 → True) ∧ (((p5 ∨ p4) → (True → p3)) ∧ p4)) → p4)) → p3) ∨ p3))) ∨ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328294714813997356477286460366 : (True → ((((p3 ∨ (p5 ∨ True)) → p3) ∧ (p3 ∧ (((p1 ∨ p4) → False) ∧ (p3 → ((True → p5) ∧ True))))) ∨ ((True ∧ (True ∧ p1)) → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40674346756819266095875365870 : ((((((p1 ∨ p5) ∧ ((True ∧ (True ∨ (((p3 ∨ p3) ∨ False) → ((p4 → True) → False)))) ∧ p5)) ∧ (p1 ∧ (p5 ∨ False))) → p3) ∨ True) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165471351050225627465145831239 : (((False → (p4 ∧ ((p5 ∧ ((p4 ∨ False) ∨ p4)) → p2))) ∧ (p3 ∨ (True → (False ∧ False)))) ∨ ((p3 ∨ ((False ∨ p3) ∨ True)) ∨ (p2 ∨ p5))) := by
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
theorem thm_5_vars_710750940816143111828590373706 : ((((((p1 → p4) → p3) → (False → p4)) ∧ (((((p1 ∧ (p5 → p3)) ∨ False) ∨ p2) → (((p3 ∧ (p4 ∧ p4)) ∧ p1) → p3)) ∧ True)) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Conjunctions on the left can always be decomposed.
  let h9 := h8.left
  let h10 := h8.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h12.left
      let h14 := h12.right
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h15 =>
      -- False on the left can always be used.
      apply False.elim h15
  case inr h16 =>
    -- One of the premise coincides with the conclusion.
    exact h7
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347373179578466659486438357869 : (p3 → ((((p1 → (p3 ∨ p3)) ∨ (p4 ∨ p2)) → p1) ∨ ((((((False → p4) ∧ p2) → (p4 ∨ (True ∧ p5))) ∧ True) ∧ p4) ∨ (p2 ∨ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_778623687832285127770136183152 : (((p1 ∨ (p1 ∨ (((p4 → (p2 ∨ p2)) ∧ ((p4 ∨ ((p1 ∨ p2) ∧ (((False ∨ p1) → p3) → True))) → True)) ∨ (p5 ∨ (p5 → p5))))) ∨ False) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_182032810661514053900080268141 : (((((False ∨ p1) → (p3 ∧ False)) → ((p1 ∨ p4) ∨ p2)) ∨ True) ∧ (p5 → (p1 ∨ (True ∧ (True ∨ (p4 → ((True → (p2 → p3)) ∨ False))))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
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
theorem thm_5_vars_264082898661449539167412442045 : (True ∧ ((p3 ∨ (True → ((((p2 ∨ p5) ∧ p5) ∨ p3) ∧ p1))) ∨ (False → (True → (((False → p5) → True) ∨ (True ∨ (p2 ∧ (p3 ∨ p1)))))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114828847886771656848938551498 : (((p4 ∨ ((p4 ∧ p5) → ((True ∨ ((False → (p1 ∨ p3)) ∨ p2)) → True))) ∧ ((p5 ∧ (p3 ∨ (p5 ∧ False))) ∨ (p4 ∧ p5))) ∨ (False → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49555918652783419205574118415 : (((((((p1 ∧ False) ∨ (p1 → (p3 ∧ False))) ∧ ((p4 → p5) → (p4 → False))) → p1) ∨ (p1 → (p2 → p1))) → ((True → False) → False)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h4 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h5 := h2 h4
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h7 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h8 := h2 h7
    -- False on the left can always be used.
    apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64852281933660399122859947193 : ((p2 ∨ (((((((p4 → p1) ∨ p4) → p2) ∧ ((p2 ∨ (p2 ∨ (p4 → (p1 ∨ p3)))) → p5)) ∧ p2) ∧ (p1 → p4)) ∧ (True → p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328829879520375069590897999806 : (True → (((False → p2) → ((((p4 → p4) → p3) → False) → p4)) → (p3 → ((True ∨ False) ∧ (((((p3 ∧ True) ∧ p4) → p1) → p3) ∨ p5))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h4
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_613814611693886779694864923780 : (((((p3 → ((False ∧ ((((p3 → False) ∨ (((p1 ∨ p4) ∨ (p2 → p4)) ∧ p4)) ∧ p1) ∧ True)) ∧ p3)) ∧ (True → (True → False))) ∨ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38602666187330422224177420164 : (((((((p4 ∧ p5) ∨ True) ∧ (False ∨ True)) → p4) ∧ (p1 ∨ (((p2 → (p1 ∨ (p2 → p1))) ∨ ((p3 ∨ p5) → p4)) ∨ True))) ∧ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323806092462614634200637334034 : (p5 ∨ ((p4 ∧ ((p1 ∨ ((False ∧ ((p1 ∨ p5) ∧ False)) ∨ (True ∨ p1))) ∨ ((True ∧ p4) ∧ p1))) ∨ ((p5 ∧ False) → (True ∨ (True → p1))))) := by
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
theorem thm_5_vars_204690585189813185872953323635 : (((p2 ∨ (p1 ∧ (p5 ∧ p3))) ∨ False) ∨ ((p3 → True) → (p3 → (p1 → ((((True → ((False ∧ p1) ∨ True)) → (True ∨ False)) ∧ p4) ∨ p1))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134881671628481471494228562953 : (((p3 → ((p4 ∨ (((True ∧ p5) → ((False ∧ (p3 → p2)) ∨ (p5 ∧ p3))) ∨ (p3 ∧ (p1 ∧ p1)))) → p2)) → p4) ∨ ((p4 ∨ p5) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_727331224460797354376084721251 : ((((p1 ∧ (p4 → p4)) ∨ (((p3 ∨ ((p1 → p1) ∧ ((p3 ∧ (False → p4)) ∧ ((((p5 ∨ p2) ∧ p2) → True) ∧ True)))) → p2) ∨ True)) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_20816026975359893502280299111 : ((((((True ∨ p5) ∨ True) ∨ ((p4 ∧ (p4 ∧ p3)) → p1)) → p5) ∨ (p2 → ((False → False) ∨ ((p5 ∨ False) ∨ (p1 ∨ (True ∧ p1)))))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324587337936625452296576272584 : (p5 ∨ (((p4 → True) ∨ False) ∧ (True ∧ ((((p2 ∨ p1) → (p2 ∨ (p1 ∧ (p4 ∧ True)))) ∨ ((p1 ∧ ((False → p2) ∧ False)) ∨ False)) ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_780480568359629208609063252888 : (((p2 ∨ ((p3 ∨ ((True → p3) ∨ ((p2 ∧ ((p2 ∨ p5) ∨ p2)) ∨ (False ∨ p1)))) ∨ (True → (((p3 ∧ (p1 ∨ False)) → p3) ∨ p3)))) ∨ p4) ∧ True) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h6 =>
    -- False on the left can always be used.
    apply False.elim h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43859962144536356127034800585 : ((((((((True → False) ∧ ((p5 → (p5 ∧ p2)) ∨ p3)) ∧ p3) → True) → (p4 ∧ ((p5 → p3) ∧ (False → p4)))) ∧ (p1 → p2)) → p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301832271341021170099804303117 : (False ∨ ((p3 ∨ p2) ∨ ((((p4 ∧ p1) ∨ p5) ∧ (p5 ∨ p3)) → (((((p2 ∧ (((False → True) → False) ∧ True)) ∨ True) ∧ p2) → p5) ∨ p1)))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h6
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h10 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h11
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h14 =>
        -- Conjunctions on the left can always be decomposed.
        let h15 := h14.left
        let h16 := h14.right
        -- Conjunctions on the left can always be decomposed.
        let h17 := h16.left
        let h18 := h16.right
        -- One of the premise coincides with the conclusion.
        exact h10
      case inr h19 =>
        -- One of the premise coincides with the conclusion.
        exact h10
    case inr h20 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h21
      -- Conjunctions on the left can always be decomposed.
      let h22 := h21.left
      let h23 := h21.right
      -- Disjunctions on the left can always be decomposed.
      cases h22
      case inl h24 =>
        -- Conjunctions on the left can always be decomposed.
        let h25 := h24.left
        let h26 := h24.right
        -- Conjunctions on the left can always be decomposed.
        let h27 := h26.left
        let h28 := h26.right
        -- One of the premise coincides with the conclusion.
        exact h9
      case inr h29 =>
        -- One of the premise coincides with the conclusion.
        exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115479388793316191226506108347 : (((p3 → ((p1 ∨ (True ∨ True)) ∧ (p5 ∨ p2))) ∨ ((((True → p4) ∧ p2) ∨ (False ∨ (p1 ∧ p4))) ∨ (p3 → (p5 ∨ p3)))) ∨ (p3 ∨ False)) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337343316653916996585836088408 : (p1 → (((((p2 → False) ∨ ((True ∨ ((p5 ∨ p5) ∨ ((p4 ∧ p3) → p1))) → (p2 ∨ (p2 → p1)))) ∨ p5) ∨ False) ∨ ((p2 ∨ p3) ∧ True))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h8
        -- One of the premise coincides with the conclusion.
        exact h1
      case inr h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h10
        -- One of the premise coincides with the conclusion.
        exact h1
    case inr h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h12
      -- One of the premise coincides with the conclusion.
      exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_677819218578413357461621507839 : (((((((((p3 ∧ p1) ∨ (((p1 ∧ p3) ∨ p5) ∧ p1)) → p2) ∨ p5) ∨ (p1 → p5)) ∧ (p4 ∨ p1)) ∨ ((p1 ∨ (p5 ∨ True)) ∨ p1)) ∨ p4) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59670094766352045289635105631 : (((True ∧ p1) → (p3 → (p5 ∧ (((((p1 ∧ p2) → p4) ∧ ((False ∧ (((p1 → p3) ∨ (p1 ∨ True)) ∧ p2)) → False)) ∧ True) → p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113542356602505262553833411057 : (((((p2 → p5) ∨ (p3 ∧ False)) → (((p5 ∧ ((p2 ∨ (p4 → (p3 → p5))) → (False ∨ p4))) ∨ p5) ∧ True)) ∨ (False ∨ True)) ∨ (p5 → False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_742980427052544487679913120283 : ((((p3 → p5) ∨ (p2 ∨ (((((((((p4 → p5) → p4) ∧ p4) → p4) ∧ p4) → (((p5 → p1) ∨ p5) → p5)) → False) ∧ p4) ∨ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



