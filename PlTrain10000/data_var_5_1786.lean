variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185846368719599467605559242164 : (((((((p2 ∧ p1) → p1) ∨ p1) ∨ (False ∨ True)) ∨ False) ∧ p5) → ((p2 ∨ ((p4 ∨ p3) ∨ p5)) → (False ∨ (((False ∨ p1) → p5) → True)))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Disjunctions on the left can always be decomposed.
        cases h7
        case inl h8 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h9
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h10 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h11
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h12 =>
        -- Disjunctions on the left can always be decomposed.
        cases h12
        case inl h13 =>
          -- False on the left can always be used.
          apply False.elim h13
        case inr h14 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h15
          -- True on the right can always be proven directly.
          apply True.intro
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
        -- Conjunctions on the left can always be decomposed.
        let h20 := h1.left
        let h21 := h1.right
        -- Disjunctions on the left can always be decomposed.
        cases h20
        case inl h22 =>
          -- Disjunctions on the left can always be decomposed.
          cases h22
          case inl h23 =>
            -- Disjunctions on the left can always be decomposed.
            cases h23
            case inl h24 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- Implications on the right can always be decomposed.
              intro h25
              -- True on the right can always be proven directly.
              apply True.intro
            case inr h26 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- Implications on the right can always be decomposed.
              intro h27
              -- True on the right can always be proven directly.
              apply True.intro
          case inr h28 =>
            -- Disjunctions on the left can always be decomposed.
            cases h28
            case inl h29 =>
              -- False on the left can always be used.
              apply False.elim h29
            case inr h30 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- Implications on the right can always be decomposed.
              intro h31
              -- True on the right can always be proven directly.
              apply True.intro
        case inr h32 =>
          -- False on the left can always be used.
          apply False.elim h32
      case inr h33 =>
        -- Conjunctions on the left can always be decomposed.
        let h34 := h1.left
        let h35 := h1.right
        -- Disjunctions on the left can always be decomposed.
        cases h34
        case inl h36 =>
          -- Disjunctions on the left can always be decomposed.
          cases h36
          case inl h37 =>
            -- Disjunctions on the left can always be decomposed.
            cases h37
            case inl h38 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- Implications on the right can always be decomposed.
              intro h39
              -- True on the right can always be proven directly.
              apply True.intro
            case inr h40 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- Implications on the right can always be decomposed.
              intro h41
              -- True on the right can always be proven directly.
              apply True.intro
          case inr h42 =>
            -- Disjunctions on the left can always be decomposed.
            cases h42
            case inl h43 =>
              -- False on the left can always be used.
              apply False.elim h43
            case inr h44 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- Implications on the right can always be decomposed.
              intro h45
              -- True on the right can always be proven directly.
              apply True.intro
        case inr h46 =>
          -- False on the left can always be used.
          apply False.elim h46
    case inr h47 =>
      -- Conjunctions on the left can always be decomposed.
      let h48 := h1.left
      let h49 := h1.right
      -- Disjunctions on the left can always be decomposed.
      cases h48
      case inl h50 =>
        -- Disjunctions on the left can always be decomposed.
        cases h50
        case inl h51 =>
          -- Disjunctions on the left can always be decomposed.
          cases h51
          case inl h52 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h53
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h54 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h55
            -- True on the right can always be proven directly.
            apply True.intro
        case inr h56 =>
          -- Disjunctions on the left can always be decomposed.
          cases h56
          case inl h57 =>
            -- False on the left can always be used.
            apply False.elim h57
          case inr h58 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h59
            -- True on the right can always be proven directly.
            apply True.intro
      case inr h60 =>
        -- False on the left can always be used.
        apply False.elim h60



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_343036463239347580615864984487 : (p2 → (((p4 → p1) ∨ (p3 ∧ p5)) → (p2 → (p2 ∧ (((p5 → p3) ∨ (p5 ∨ ((p5 → p1) ∧ True))) ∨ (p3 → (False ∨ (p5 ∨ True)))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- One of the premise coincides with the conclusion.
    exact h1
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_601596721302001853835331330252 : ((((p3 ∧ (((False ∧ p3) → p5) ∧ (((((p5 ∨ p3) ∧ (p4 ∧ True)) → False) ∨ p1) ∨ (((True ∨ False) ∧ p1) → (False ∧ p5))))) ∧ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61478180155305467432682524763 : ((p1 ∧ (((p1 → p4) → (p5 ∧ ((((((True → p1) → p3) ∧ (True → p2)) ∧ p4) → (p2 ∧ p2)) → (p3 ∧ True)))) → (p1 ∧ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53698351778631428829769672262 : (((p5 ∧ (p2 ∧ (p1 ∧ ((False ∧ True) ∨ (p3 ∧ True))))) ∧ (p1 ∨ (p3 ∨ ((((False ∧ (False ∧ p5)) → p4) ∨ (False ∧ True)) ∧ p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_654528204419457405310625264773 : (((((p4 ∧ ((p2 ∧ ((p4 ∨ (True ∨ p2)) → ((p4 → ((True ∧ False) ∨ p5)) ∨ (p1 ∨ p4)))) ∨ (True → True))) ∨ True) ∨ (p4 ∨ p3)) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_164469517650651107331217461270 : (((((p5 → (p2 → (((p3 → p5) → (True ∧ (p5 → True))) ∧ False))) → p5) ∨ p5) ∧ p1) ∨ ((p5 → (p1 ∧ True)) ∨ (False → (p1 ∨ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307882125815375989335637985217 : (p1 ∨ (p5 → ((True ∧ p3) ∨ (((p2 ∨ (((False ∧ p2) ∧ ((True ∧ (p3 ∧ (p1 → p3))) ∨ ((p5 → p2) → False))) ∧ p1)) ∨ True) ∧ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113932255678440533608511970300 : (((((((p4 ∨ (p2 ∨ p1)) ∨ p4) ∧ (True ∨ p3)) ∨ p5) → (((p3 → p4) → p4) ∧ (p5 ∧ False))) ∧ (p3 ∨ (p2 ∨ p3))) ∨ (True ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257196693620758603739700762057 : ((p2 ∨ p2) → (((p3 ∨ (((False ∨ ((((p1 ∨ p2) → p3) ∧ (False ∨ p3)) ∨ True)) ∨ False) ∧ p2)) ∨ (p5 ∨ (True ∧ True))) ∨ (True → p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_594683452010713604460977950356 : (((((((((p3 ∧ p1) ∧ p1) ∨ True) ∧ (p1 ∨ (p4 ∨ p1))) ∧ ((True ∨ p2) → False)) → (p4 → (((False ∧ p2) ∨ p2) ∨ p2))) ∧ True) ∨ False) ∧ True) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h8.left
    let h11 := h8.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h12 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h13 : (True ∨ p2) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h14 := h4 h13
      -- False on the left can always be used.
      apply False.elim h14
    case inr h15 =>
      -- Disjunctions on the left can always be decomposed.
      cases h15
      case inl h16 =>
        -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
        have h17 : (True ∨ p2) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h4, we can now drive its conclusion.
        let h18 := h4 h17
        -- False on the left can always be used.
        apply False.elim h18
      case inr h19 =>
        -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
        have h20 : (True ∨ p2) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h4, we can now drive its conclusion.
        let h21 := h4 h20
        -- False on the left can always be used.
        apply False.elim h21
  case inr h22 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h23 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h24 : (True ∨ p2) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h25 := h4 h24
      -- False on the left can always be used.
      apply False.elim h25
    case inr h26 =>
      -- Disjunctions on the left can always be decomposed.
      cases h26
      case inl h27 =>
        -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
        have h28 : (True ∨ p2) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h4, we can now drive its conclusion.
        let h29 := h4 h28
        -- False on the left can always be used.
        apply False.elim h29
      case inr h30 =>
        -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
        have h31 : (True ∨ p2) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h4, we can now drive its conclusion.
        let h32 := h4 h31
        -- False on the left can always be used.
        apply False.elim h32
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307446143948356491398243589580 : (p1 ∨ (p5 ∨ ((p4 ∨ ((p2 → (True ∨ (p3 → (False ∨ (True ∧ False))))) ∧ p4)) ∨ ((p4 ∧ p2) → ((((p5 → p1) ∧ p3) ∨ p4) ∧ p4))))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59216044157724831868082429915 : (((p1 ∨ p5) ∨ (((((p5 ∧ (True ∨ (p4 ∧ False))) → (((p1 ∧ (p2 ∨ p1)) ∨ p1) ∨ p5)) ∧ False) → (p2 → (p4 → p1))) → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_92636319119688896840941358043 : (((False → p4) → ((p2 ∨ (((p1 → False) ∧ p5) ∨ False)) ∧ (((True ∨ (p5 ∧ (((p5 ∨ p5) ∨ p3) ∨ (p4 ∨ False)))) ∨ p3) ∧ False))) → p1) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (False → p4) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319581609777209952073325008652 : (p4 ∨ (((True → p1) ∧ (p2 ∨ (False ∧ (p2 ∨ (p1 → p2))))) → (((p5 → (p4 ∧ (p4 ∨ (p4 ∨ (p3 ∨ p3))))) ∨ p2) ∨ (True ∧ p3)))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- False on the left can always be used.
    apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_251305262751642830068050284019 : ((p2 → p3) ∨ ((p4 → (((p5 ∨ (True ∨ (((False ∧ p1) ∨ p4) ∨ p5))) ∨ (p4 → (p4 ∨ p2))) → ((p2 ∧ p4) ∨ p4))) ∧ (p2 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h1
      case inr h7 =>
        -- Disjunctions on the left can always be decomposed.
        cases h7
        case inl h8 =>
          -- Disjunctions on the left can always be decomposed.
          cases h8
          case inl h9 =>
            -- Conjunctions on the left can always be decomposed.
            let h10 := h9.left
            let h11 := h9.right
            -- False on the left can always be used.
            apply False.elim h10
          case inr h12 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h1
        case inr h13 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h1
  case inr h14 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  -- Implications on the right can always be decomposed.
  intro h15
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158364266527127989821255432666 : (((p2 ∨ p2) ∧ (((p2 ∨ (p4 ∧ (p2 → (p3 → (True ∧ p3))))) → (p4 → (False ∨ p4))) → True)) ∨ (p2 → (((p1 → p4) → p1) ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56708620468368082171932728530 : ((((p4 ∧ p2) ∨ True) ∧ ((p1 ∨ (((False → p1) ∧ (((p5 ∧ (True ∧ p4)) ∨ (p2 → False)) ∧ p3)) ∨ (True → (True ∧ p5)))) → p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171081647040137133354523502917 : ((p5 ∨ (p4 → ((p4 ∨ (p1 ∨ p2)) ∨ ((False ∨ (p1 → (False ∧ p5))) → p1)))) ∧ (False ∨ (p3 ∨ ((p2 ∧ p1) ∨ (p5 → (True ∨ p1)))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233437069345909506556309903107 : ((False ∨ (True → p3)) → (((p5 → (((p3 ∧ p2) ∧ p2) ∨ (p5 → p3))) ∨ True) → ((p2 ∧ (False ∨ True)) → ((p5 → p1) ∨ (p5 → True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h9 =>
        -- False on the left can always be used.
        apply False.elim h9
      case inr h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h11
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h12 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h13 =>
        -- False on the left can always be used.
        apply False.elim h13
      case inr h14 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h15
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53948696544879540394980540887 : (((p4 → (((p5 ∧ p2) → (False ∧ p3)) ∨ (p5 ∧ p2))) ∨ (True ∧ (p2 → ((p4 → ((p3 → True) ∨ p1)) → (p3 ∨ (False ∨ p1)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171784213664938282398707218208 : ((((((True ∨ p4) ∧ ((False ∨ p1) → False)) ∨ (p5 ∧ p3)) ∨ (p4 → p3)) → False) ∨ ((True ∧ ((True → p5) ∨ ((p5 ∧ True) → False))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160447374248952642184619679779 : (((((False → p1) → (p2 ∧ ((p2 → p5) → ((p2 → p5) ∨ p2)))) ∨ p1) → (p4 → (p2 ∧ p4))) → (((True → p2) ∨ (p1 ∨ True)) ∨ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156743201583750904605387458743 : (((((p5 → p3) ∨ p3) ∧ ((False ∧ p1) ∨ (False ∨ (((p1 → True) ∧ False) ∨ (p2 → p5))))) ∧ True) ∨ (((p2 → (p5 → p5)) ∨ False) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_789412206587207017319696089304 : (((p5 ∨ ((((True ∧ p3) ∨ (p1 ∨ ((p1 ∧ (p3 → True)) → (p4 ∨ True)))) ∧ p1) → (False ∨ ((p3 ∨ ((p3 ∧ False) → p5)) ∨ p3)))) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    let h5 := h4.left
    let h6 := h4.right
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h9
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- False on the left can always be used.
      apply False.elim h11
    case inr h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h13
      -- Conjunctions on the left can always be decomposed.
      let h14 := h13.left
      let h15 := h13.right
      -- False on the left can always be used.
      apply False.elim h15
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_739647041183373087132298575435 : ((((p5 ∧ p5) ∨ ((p5 ∧ (p1 ∨ (((True ∧ (p2 → ((((p1 ∧ False) ∨ (True → p4)) → True) ∧ (False ∨ p3)))) → p5) ∨ p4))) ∨ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49971879768549243523160366987 : ((((p1 ∨ (((p1 → p4) ∨ (((p4 ∨ p1) ∧ p5) → p5)) ∧ (p2 ∨ p4))) ∨ ((p2 ∧ p2) ∧ True)) ∧ ((p3 ∧ (True ∨ True)) ∧ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_106519773513121778629511859547 : ((((False ∨ (p4 ∧ True)) ∧ ((p5 ∧ True) → False)) ∨ (((p3 ∨ (p2 → True)) → ((p1 ∧ p5) ∧ p1)) ∨ ((True ∨ True) ∨ True))) ∧ (p1 → p1)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158110376412182828744303957123 : ((((p5 → False) ∨ (p3 ∨ False)) ∧ (((p2 ∧ (p3 ∧ ((p4 → p4) ∨ p1))) ∧ (p2 ∧ p2)) ∧ p5)) ∨ (True ∨ (p4 ∨ ((p2 ∧ False) ∨ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38028655166061658025865904393 : (((((((p5 → p3) ∧ (True → (((True ∨ ((p5 ∨ p3) ∧ p4)) ∧ ((p2 → p1) ∧ p2)) → p5))) → p1) ∧ p3) → (False ∨ p2)) ∧ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48986787591096658480931482274 : (((((True ∨ (True ∧ p4)) → (((p5 ∧ (False → (p3 ∧ p2))) ∧ (p1 ∨ ((False ∧ p3) → p1))) ∨ p3)) ∨ p4) ∨ ((p4 → p3) → p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148546880560610359375461989551 : ((((p1 ∨ (p4 ∨ ((p2 ∧ True) → (p3 → p4)))) ∧ p1) ∧ ((p1 → (p4 ∧ ((p1 ∨ p5) ∨ p1))) → p5)) ∨ ((p4 → False) ∨ (p3 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_655537417681617749281451002604 : (((((((((p1 → p4) ∧ p2) ∨ False) ∨ (p2 → (p1 ∧ ((False → (True → p5)) → p4)))) ∨ (p5 ∨ p5)) → (p2 → p1)) ∨ (p1 → p1)) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_329756461758126263167275585905 : (True → (True ∧ ((((p2 → p5) → (False ∧ p2)) ∧ (p3 ∧ ((p2 ∨ (True ∨ ((False ∧ True) ∧ (p5 ∨ p1)))) → ((p5 → p3) ∧ p5)))) → False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h7 : (p2 → p5) := by
    -- Implications on the right can always be decomposed.
    intro h8
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h9 : (p2 ∨ (True ∨ ((False ∧ True) ∧ (p5 ∨ p1)))) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h8
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h10 := h6 h9
    -- We need to get the right conjuct of h10 based on <expert-advice>.
    let h11 := h10.right
    -- One of the premise coincides with the conclusion.
    exact h11
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h12 := h3 h7
  -- We need to get the left conjuct of h12 based on <expert-advice>.
  let h13 := h12.left
  -- False on the left can always be used.
  apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328454419072573985519327609743 : (True → (((p2 ∧ (((p2 ∨ p2) ∧ p2) ∨ (p2 ∧ (p4 ∨ True)))) → (p1 → ((p1 ∨ p3) ∧ p5))) → (((p5 → (p2 ∨ p2)) ∧ p1) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_318579298840839205814387446774 : (p4 ∨ (((((((p3 → p4) → p1) → (p5 ∨ False)) ∨ p1) ∧ ((p5 ∨ (((p4 → True) → p1) → p3)) ∧ p5)) ∨ (p1 → p2)) ∨ (False → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66103981998083170679730410351 : ((p5 ∨ (((p5 ∨ (p3 → (((True → (p3 ∨ (p4 → p5))) ∧ False) ∨ p5))) ∨ (((p3 → (p2 ∨ True)) ∧ (p4 ∧ p2)) ∨ False)) → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113181408221693318017158139205 : (((((p3 ∧ (True ∨ (((p5 ∧ p3) ∧ (p4 ∧ p4)) ∧ (p2 ∨ ((p5 ∧ False) → (False ∧ p5)))))) → False) ∧ p2) ∧ (p1 → p5)) ∨ (p5 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135258688268723807656588582424 : (((p1 ∧ (p4 ∧ ((p3 ∧ (p4 ∧ (p3 → False))) ∧ ((p2 → ((p2 ∧ (p4 ∨ p4)) ∨ False)) ∨ p3)))) → (p5 → False)) ∨ (p4 ∨ (p3 ∨ p1))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Conjunctions on the left can always be decomposed.
  let h7 := h6.left
  let h8 := h6.right
  -- Conjunctions on the left can always be decomposed.
  let h9 := h7.left
  let h10 := h7.right
  -- Conjunctions on the left can always be decomposed.
  let h11 := h10.left
  let h12 := h10.right
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h13 =>
    -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
    have h14 : p3 := by
      -- One of the premise coincides with the conclusion.
      exact h9
    -- We have shown the premise of h12, we can now drive its conclusion.
    let h15 := h12 h14
    -- False on the left can always be used.
    apply False.elim h15
  case inr h16 =>
    -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
    have h17 : p3 := by
      -- One of the premise coincides with the conclusion.
      exact h16
    -- We have shown the premise of h12, we can now drive its conclusion.
    let h18 := h12 h17
    -- False on the left can always be used.
    apply False.elim h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_98830004010534587281978977715 : ((True → ((p1 → (False ∨ ((p3 ∨ True) ∨ (p3 ∧ (((p1 → (p1 ∧ ((p3 → p2) ∧ (p5 ∧ p4)))) ∨ (False → True)) ∨ p3))))) ∧ False)) → False) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147242647384083671889498893750 : (((((p1 ∧ (False ∨ ((p5 → (p1 ∨ p2)) → p1))) ∧ (False → (p3 → (p3 ∧ (True ∧ p2))))) ∧ p5) ∨ False) ∨ (True ∨ (p5 → (p4 ∧ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190614970206686633276369434844 : (((True ∧ (p2 → (p5 → ((True ∨ False) → True)))) → p5) ∨ ((((True ∧ False) ∧ p5) → (True ∨ p3)) ∨ ((True ∧ ((p4 ∨ p1) ∧ p2)) ∧ p4))) := by
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
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215256103557230556828651823424 : ((False ∧ (p2 ∧ (p5 → p1))) ∨ ((((p4 → (p3 ∧ (((p3 ∧ (p1 ∧ p3)) ∧ p5) ∧ (p5 ∨ p1)))) ∨ False) ∧ ((p5 ∧ p2) ∧ False)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55835754569640019046249562462 : (((False ∧ ((p2 → False) → p1)) ∧ ((p4 → (((p3 ∧ (p4 ∨ (False → (p3 → p5)))) ∧ (p1 → True)) ∨ p4)) ∧ (p4 ∧ (p3 ∨ True)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_774763492640891515626139144114 : (((False ∨ ((True ∧ ((p3 → (False ∧ False)) ∨ p4)) ∧ ((p1 → ((p5 ∨ ((False ∨ False) → False)) → (((p3 ∨ True) → p1) ∧ p4))) ∨ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_302012751536765794397624060624 : (False ∨ (True ∧ (((p2 ∧ (True ∧ p4)) ∧ (p4 ∧ ((p4 ∧ ((True → True) → ((((p3 → p4) ∨ (p5 ∨ p3)) ∧ p3) ∨ p5))) → False))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_678248900416870691490635173561 : (((((p3 ∧ (p2 ∨ ((p4 → (p2 ∧ p2)) ∨ (p1 ∨ True)))) → ((p3 → (p5 ∧ (True ∨ p1))) → p1)) ∨ ((True ∧ (True ∧ True)) ∨ p4)) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133685447376122057998369977329 : ((((((((p4 ∧ (p5 ∧ p4)) ∨ ((p3 → (p1 → p2)) ∧ True)) ∧ p1) ∨ p5) ∧ False) ∨ (p4 → (p5 → False))) ∧ False) ∨ ((p5 ∧ False) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_176282821457316024834750721360 : (((((p2 ∧ (p5 ∧ p3)) ∨ p1) ∨ ((p1 ∧ True) ∨ p3)) ∨ (False → p2)) ∧ ((p4 ∧ p3) → (((p1 ∧ p2) ∨ True) ∧ (p4 ∧ (p4 ∨ p5))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h5 := h2.left
  let h6 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h5
  -- Conjunctions on the left can always be decomposed.
  let h7 := h2.left
  let h8 := h2.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185023619468004299686234484100 : (((p4 ∨ True) ∧ (p1 ∨ ((p4 ∧ ((False ∧ False) ∨ p5)) ∧ True))) ∨ (p2 ∨ ((((p3 → ((p1 ∨ (p1 ∧ p4)) → p1)) ∨ False) ∨ p3) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- One of the premise coincides with the conclusion.
    exact h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190926088934357102521289517390 : ((((p3 ∧ (p2 ∨ p3)) ∨ False) ∧ ((True ∧ p5) ∧ True)) ∨ ((((False ∧ (((p5 ∨ p3) → True) ∨ True)) ∧ ((False → p3) ∧ True)) → p4) ∨ p1)) := by
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
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249096869842314495079537293647 : ((p4 ∨ p1) ∨ (p1 → ((((p5 → (p1 → ((p1 ∧ p4) ∧ p4))) ∧ (p2 ∧ ((p2 → (False ∨ p2)) ∨ False))) ∨ True) ∨ (p3 ∨ (p4 ∨ False))))) := by
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
theorem thm_5_vars_695127083656981712144558545969 : ((((((((False → (False ∨ False)) ∨ (p3 ∧ False)) ∨ True) ∨ (p5 → True)) ∨ False) → ((p4 ∨ p5) ∨ (((p4 ∧ False) → (False → p5)) ∨ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_708734881482153736136201634303 : ((((((p3 ∧ p3) ∧ ((p5 ∨ p5) ∧ p1)) → False) → ((False → True) → ((True → (((False ∧ (False → p5)) ∧ p5) ∧ True)) ∨ (p5 ∧ p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_748152425777528714680625599635 : ((((p1 → p4) → (((p4 → p1) ∨ ((((((p4 ∧ p2) → (p4 ∧ p1)) → p4) → (p1 → p4)) ∧ ((p5 → True) → p3)) ∧ p1)) → p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62317684792142411101889802383 : ((p3 ∧ ((False ∧ ((p5 ∧ p2) → ((((p1 ∧ p3) ∧ (p4 ∧ (p3 → True))) ∧ False) ∨ (True ∧ (p2 ∧ (p2 ∨ p5)))))) ∨ (True → p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60119959788179520255496160138 : (((p3 ∨ p4) → (p4 → (((p1 ∨ (p2 ∨ ((True ∧ (((False → p2) → p3) ∧ ((p2 ∨ True) ∧ p3))) ∧ (False ∧ p2)))) ∧ p4) ∧ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187580169972787904030788622483 : ((p3 ∨ (((p1 ∨ False) → p2) → ((True ∧ p3) ∧ (p2 ∧ p2)))) → ((p5 ∨ ((True ∧ (((False → p4) ∧ p5) ∨ (p5 ∨ p2))) ∨ True)) ∨ True)) := by
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
theorem thm_5_vars_152406224461806753786645626381 : (((p1 ∧ ((True → p2) ∧ p1)) → ((((p2 ∧ p1) ∧ (p2 → False)) ∨ (((p4 ∧ p1) → p3) ∨ True)) → p4)) → ((p5 ∨ (p2 ∨ True)) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314669817469709880241439136567 : (p3 ∨ ((p4 → (p5 ∨ ((((p4 ∨ (p2 ∨ p5)) ∧ p5) ∨ False) ∧ (True ∨ (p5 ∧ False))))) ∨ (((False ∧ ((p3 ∨ p1) ∨ p2)) → p1) ∨ p1))) := by
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
theorem thm_5_vars_308082344493016626220333832326 : (p2 ∨ ((((p1 ∧ (((p5 ∨ p2) → (p1 → ((p2 ∧ p5) → (p4 ∧ p5)))) ∧ False)) ∨ (p5 → p2)) → (((p4 ∨ p2) → p2) ∨ True)) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136834913045598637042121378217 : (((p1 ∧ p2) ∨ (((p2 ∧ p4) ∨ p5) → (((((p1 ∧ p2) → (False ∧ p5)) → p1) → ((p1 ∧ p5) → p3)) ∧ p2))) ∨ ((p2 ∧ p3) → p3)) := by
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
theorem thm_5_vars_89299929781101734543732059037 : (((False ∨ (True → False)) ∧ ((p1 ∨ p1) ∨ (((p2 ∧ ((False ∨ ((True ∨ (p1 ∨ (True ∧ (p1 → p4)))) ∨ p1)) ∧ p3)) ∧ p5) ∨ p2))) → False) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
        have h8 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h5, we can now drive its conclusion.
        let h9 := h5 h8
        -- False on the left can always be used.
        apply False.elim h9
      case inr h10 =>
        -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
        have h11 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h5, we can now drive its conclusion.
        let h12 := h5 h11
        -- False on the left can always be used.
        apply False.elim h12
    case inr h13 =>
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h14 =>
        -- Conjunctions on the left can always be decomposed.
        let h15 := h14.left
        let h16 := h14.right
        -- Conjunctions on the left can always be decomposed.
        let h17 := h15.left
        let h18 := h15.right
        -- Conjunctions on the left can always be decomposed.
        let h19 := h18.left
        let h20 := h18.right
        -- Disjunctions on the left can always be decomposed.
        cases h19
        case inl h21 =>
          -- False on the left can always be used.
          apply False.elim h21
        case inr h22 =>
          -- Disjunctions on the left can always be decomposed.
          cases h22
          case inl h23 =>
            -- Disjunctions on the left can always be decomposed.
            cases h23
            case inl h24 =>
              -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
              have h25 : True := by
                -- True on the right can always be proven directly.
                apply True.intro
              -- We have shown the premise of h5, we can now drive its conclusion.
              let h26 := h5 h25
              -- False on the left can always be used.
              apply False.elim h26
            case inr h27 =>
              -- Disjunctions on the left can always be decomposed.
              cases h27
              case inl h28 =>
                -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
                have h29 : True := by
                  -- True on the right can always be proven directly.
                  apply True.intro
                -- We have shown the premise of h5, we can now drive its conclusion.
                let h30 := h5 h29
                -- False on the left can always be used.
                apply False.elim h30
              case inr h31 =>
                -- Conjunctions on the left can always be decomposed.
                let h32 := h31.left
                let h33 := h31.right
                -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
                have h34 : True := by
                  -- True on the right can always be proven directly.
                  apply True.intro
                -- We have shown the premise of h5, we can now drive its conclusion.
                let h35 := h5 h34
                -- False on the left can always be used.
                apply False.elim h35
          case inr h36 =>
            -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
            have h37 : True := by
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h5, we can now drive its conclusion.
            let h38 := h5 h37
            -- False on the left can always be used.
            apply False.elim h38
      case inr h39 =>
        -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
        have h40 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h5, we can now drive its conclusion.
        let h41 := h5 h40
        -- False on the left can always be used.
        apply False.elim h41



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_126644135396741201598936117895 : ((p3 ∧ (p2 ∨ (((p5 ∨ (((p3 ∧ ((p1 ∧ False) → p3)) → ((p4 ∨ (p5 ∨ p5)) ∧ p4)) ∧ p4)) ∧ p5) ∧ (p5 ∨ p5)))) → (False ∨ p3)) := by
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
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h6.left
    let h9 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h2
      case inr h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h2
    case inr h13 =>
      -- Conjunctions on the left can always be decomposed.
      let h14 := h13.left
      let h15 := h13.right
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h16 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h2
      case inr h17 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336251493734955381532568636810 : (p1 → (((p4 ∧ ((p5 ∨ (p5 ∧ ((p5 ∨ False) ∨ ((False ∨ p3) ∨ p4)))) ∧ (p5 ∧ p5))) ∧ ((True ∧ ((p5 ∨ p2) → p2)) → p3)) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_805753834594004809153300065931 : (((p3 → (p3 → (((p2 ∨ ((p1 → ((p4 ∨ True) ∧ (p4 ∨ False))) → p3)) → (((p4 → (p2 → p5)) ∧ p2) → (p4 ∨ p4))) → False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185376583104521551949431518727 : ((p5 ∧ (((p2 ∧ (p4 → p4)) ∧ (p4 ∨ p1)) ∨ (p5 ∨ p1))) ∨ ((((p3 ∧ (p1 ∧ (True → p2))) → p3) ∧ (p4 → (p4 ∨ p5))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65021552292628876783462252282 : ((p2 ∨ ((p2 ∨ p2) ∨ ((((p1 ∨ (((p2 ∧ True) ∧ p4) ∧ (True ∨ p5))) ∨ p3) ∨ (False ∨ p5)) → (p1 → (p4 ∨ (True ∨ p1)))))) ∨ p2) := by
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
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h6 =>
        -- Conjunctions on the left can always be decomposed.
        let h7 := h6.left
        let h8 := h6.right
        -- Conjunctions on the left can always be decomposed.
        let h9 := h7.left
        let h10 := h7.right
        -- Conjunctions on the left can always be decomposed.
        let h11 := h9.left
        let h12 := h9.right
        -- Disjunctions on the left can always be decomposed.
        cases h8
        case inl h13 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h10
        case inr h14 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h10
    case inr h15 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h16 =>
    -- Disjunctions on the left can always be decomposed.
    cases h16
    case inl h17 =>
      -- False on the left can always be used.
      apply False.elim h17
    case inr h18 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137948982638259657899446943350 : ((p5 ∨ (((((False → p1) ∧ True) ∧ (p1 ∨ (((p3 → (p2 ∨ p4)) ∨ True) ∨ (p3 → False)))) → (p5 → p2)) ∨ p4)) ∨ ((p3 ∧ False) → False)) := by
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
theorem thm_5_vars_201350687715846747646115673148 : ((p5 → (False → (((False → p5) → p3) ∨ p4))) → ((True ∧ ((p5 ∨ ((p3 → p3) ∨ True)) → False)) → (p2 → (True → (p5 ∧ (p1 → p1)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h5 := h2.left
  let h6 := h2.right
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h7 : (p5 ∨ ((p3 → p3) ∨ True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h8 := h6 h7
  -- False on the left can always be used.
  apply False.elim h8
  -- Implications on the right can always be decomposed.
  intro h9
  -- Conjunctions on the left can always be decomposed.
  let h10 := h2.left
  let h11 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177236734227500663508134016626 : ((True ∨ (p2 ∧ (((p5 ∨ True) ∧ ((p4 ∧ True) → p5)) ∨ (p5 → p2)))) ∧ ((p5 ∨ ((p3 ∧ (p5 ∧ (p2 ∧ p1))) ∧ (p5 → p4))) ∨ True)) := by
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
theorem thm_5_vars_612638284584732873320705454484 : (((((((p1 ∧ ((p5 → ((False ∧ p4) → (p3 → True))) ∨ ((True ∧ p1) ∨ True))) ∧ p4) ∧ (p2 ∧ (p1 ∨ p2))) ∨ (p5 ∧ p4)) ∨ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56794839486556372662089273505 : ((((True ∨ p5) → p1) ∧ ((((p5 ∧ (p4 ∨ (p5 ∨ p4))) → p5) → ((False ∧ ((p1 ∨ (p1 ∧ p5)) → (p3 → p4))) → p4)) → p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206075032559442176912325893335 : ((p3 ∧ ((p4 ∨ p2) ∧ (p3 ∨ p5))) ∨ ((p2 ∨ True) ∨ (p2 ∧ (p2 ∧ (((((p5 ∨ True) ∨ p5) ∨ p3) → True) ∨ ((p2 ∨ p1) ∨ True)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257793364292565523406950835953 : ((p3 ∨ p5) → ((((p4 ∧ (p1 → True)) ∧ (p3 ∨ ((p5 ∧ True) ∨ p1))) ∨ (((p2 ∨ (False → (p1 ∧ p5))) ∨ True) ∨ (False ∨ False))) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
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
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186492460188867022629005882587 : (((p1 ∧ ((p2 ∧ ((p5 → True) → False)) ∧ p2)) ∧ (p4 → p3)) → ((False ∧ p5) ∨ (((((False ∧ p4) ∧ p2) ∧ False) ∨ (p5 → False)) → p5))) := by
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
  let h8 := h6.left
  let h9 := h6.right
  -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
  have h10 : (p5 → True) := by
    -- Implications on the right can always be decomposed.
    intro h11
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h9, we can now drive its conclusion.
  let h12 := h9 h10
  -- False on the left can always be used.
  apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52311781986559493209094632321 : ((((((p3 ∨ p5) → ((p4 ∨ (True ∨ p4)) ∧ (p1 ∨ p3))) ∧ True) ∨ p1) ∧ (p2 ∨ ((False → False) ∨ ((p5 → (p3 → p5)) ∧ p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115468769785449151933484519545 : (((False ∨ (((p5 → True) → p2) ∧ (False ∧ True))) ∨ ((((p2 ∧ (True → False)) ∧ True) ∧ (p2 → (p4 → True))) → (True ∧ p3))) ∨ (p2 ∨ p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
  have h8 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h7, we can now drive its conclusion.
  let h9 := h7 h8
  -- False on the left can always be used.
  apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234175968808896297553541723951 : ((True → (p5 → True)) → ((p5 → ((p4 ∧ (((p3 ∨ ((p5 ∧ True) ∧ (p2 ∧ (p2 ∧ (p2 → p4))))) ∨ p1) ∨ p4)) → False)) ∨ (p2 ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258764850701896835779054560511 : ((True → False) → ((((((p3 ∧ (p2 ∧ p5)) ∧ p2) ∧ (p1 ∨ p3)) ∧ (True ∧ p5)) ∧ (((True ∨ (p4 → p1)) ∨ p1) ∧ (False ∧ True))) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161309608049410532374592427988 : ((True ∧ ((((((True ∨ p1) ∨ (p2 → p4)) → p4) → (p4 ∧ p4)) ∨ ((True ∧ False) ∧ True)) → p2)) → (((p1 ∧ True) ∨ (p4 ∨ p2)) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : (((((True ∨ p1) ∨ (p2 → p4)) → p4) → (p4 ∧ p4)) ∨ ((True ∧ False) ∧ True)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h6 : ((True ∨ p1) ∨ (p2 → p4)) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h7 := h5 h6
    -- One of the premise coincides with the conclusion.
    exact h7
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h8 : ((True ∨ p1) ∨ (p2 → p4)) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h9 := h5 h8
    -- One of the premise coincides with the conclusion.
    exact h9
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h10 := h3 h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h10
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115602111128345745877242474373 : (((p2 ∧ ((False → True) ∧ (p4 ∧ p2))) ∧ ((p3 ∨ (False ∨ ((((p2 ∨ False) ∧ p1) ∨ p5) → (p2 ∨ (p4 ∧ p2))))) → p3)) ∨ (False → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_724426176702906535875784227398 : ((((True ∨ (p4 ∧ p5)) ∧ (p1 ∨ ((p3 → (((False ∨ p3) ∧ ((p4 → True) ∧ (True ∧ True))) ∨ False)) → (p4 ∧ ((p5 → p5) ∧ p1))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207987869286548609495511745918 : ((((p4 ∧ False) ∨ False) ∨ (False ∨ p3)) → (p1 → ((True ∧ ((p1 ∨ p5) → False)) → (((p3 ∨ (p2 ∨ p4)) ∧ (p4 ∨ (p5 ∧ p5))) ∨ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- False on the left can always be used.
      apply False.elim h9
    case inr h10 =>
      -- False on the left can always be used.
      apply False.elim h10
  case inr h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- False on the left can always be used.
      apply False.elim h12
    case inr h13 =>
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h14 : (p1 ∨ p5) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h2
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h15 := h5 h14
      -- False on the left can always be used.
      apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_216875951119323558457536799026 : (((p1 ∨ (p3 ∨ p1)) ∧ p2) → ((((True ∧ p5) → ((False ∨ p4) ∨ p5)) ∨ (True ∧ p2)) ∧ ((True ∨ False) ∧ (((True → p2) → False) → p4)))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- One of the premise coincides with the conclusion.
      exact h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h8 := h1.left
  let h9 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h10 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h13 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  -- Implications on the right can always be decomposed.
  intro h14
  -- Conjunctions on the left can always be decomposed.
  let h15 := h1.left
  let h16 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h15
  case inl h17 =>
    -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
    have h18 : (True → p2) := by
      -- Implications on the right can always be decomposed.
      intro h19
      -- One of the premise coincides with the conclusion.
      exact h16
    -- We have shown the premise of h14, we can now drive its conclusion.
    let h20 := h14 h18
    -- False on the left can always be used.
    apply False.elim h20
  case inr h21 =>
    -- Disjunctions on the left can always be decomposed.
    cases h21
    case inl h22 =>
      -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
      have h23 : (True → p2) := by
        -- Implications on the right can always be decomposed.
        intro h24
        -- One of the premise coincides with the conclusion.
        exact h16
      -- We have shown the premise of h14, we can now drive its conclusion.
      let h25 := h14 h23
      -- False on the left can always be used.
      apply False.elim h25
    case inr h26 =>
      -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
      have h27 : (True → p2) := by
        -- Implications on the right can always be decomposed.
        intro h28
        -- One of the premise coincides with the conclusion.
        exact h16
      -- We have shown the premise of h14, we can now drive its conclusion.
      let h29 := h14 h27
      -- False on the left can always be used.
      apply False.elim h29



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68111817622622818907680953876 : ((p2 → (p2 → ((p2 ∧ ((p1 ∨ (p3 ∧ ((((p3 ∧ p3) ∨ True) ∧ True) ∧ (False ∨ False)))) ∨ False)) ∨ ((p3 ∧ (True ∧ p4)) ∨ True)))) ∨ p5) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_615492551194465464272320888327 : ((((((p2 ∧ (p2 → (((False ∨ (p3 ∨ (True → (p2 ∧ p3)))) ∨ p5) ∨ p3))) → p3) → ((p5 ∧ (p1 ∧ (p5 ∧ p3))) ∨ p1)) ∨ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197829948531547694551603724443 : (((p3 ∧ (p5 ∧ p1)) ∨ (p4 ∨ (p4 → False))) ∨ ((((p3 ∧ p3) ∧ p1) ∨ (p3 ∨ ((p4 ∨ (False ∨ ((p3 ∧ p1) → True))) ∧ True))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198820394150216223876688611451 : ((p1 → ((p4 ∧ (p5 → (p2 ∨ p2))) ∨ p2)) ∨ (p3 ∨ (p3 ∨ (True ∨ (p1 ∧ ((p1 ∧ True) → (p3 ∧ (((True ∨ p4) ∧ False) ∨ p1)))))))) := by
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
theorem thm_5_vars_200077003425095485074438618512 : ((((p5 → p1) ∧ p5) ∧ (p3 → (p2 ∨ p4))) → (((((((True → (p2 → p5)) ∧ (True → p1)) ∨ p5) → (p2 ∨ p5)) ∧ p3) ∨ p2) ∨ p1)) := by
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
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h6 : p5 := by
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h7 := h4 h6
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_622635458608376777763820319286 : ((((p4 ∧ ((p1 → ((p1 ∨ ((p2 → ((((p1 ∨ (p2 ∧ (p5 ∧ False))) ∨ p2) → p4) → p4)) ∨ True)) → p2)) → (p1 ∧ False))) ∨ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_733134373717156355063739987647 : ((((p3 ∧ False) ∧ ((False → True) → ((((p5 → (p4 ∧ (p2 → (p3 ∧ p5)))) ∨ (p4 → (p5 ∧ p4))) ∧ (True → (p4 → False))) ∧ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65183990258911592939724411544 : ((p3 ∨ (((p2 ∨ p1) → ((p3 ∨ p5) → ((p3 ∧ (((p4 ∨ (p2 ∧ (p2 → p5))) ∧ (True → True)) ∧ p2)) → (p5 ∧ p1)))) ∧ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149187390085364509905430459370 : (((p2 → True) ∧ (p5 → (False ∨ ((p1 ∨ ((p2 ∨ (p1 ∧ p4)) ∧ (p5 ∧ True))) ∨ (p5 ∨ (p3 → p4)))))) ∨ (((p5 ∧ False) ∨ True) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_701807182024748209103559208385 : ((((p3 ∧ (p2 ∧ ((p4 ∧ (True ∧ (p2 ∨ p2))) ∧ p2))) ∧ ((p4 ∧ (p2 ∧ (p5 ∧ (p3 ∨ (p3 ∧ ((p3 ∨ True) ∨ False)))))) ∨ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118628510932777156877950445285 : ((p4 ∨ ((((p4 ∧ p2) → p4) → p1) ∨ (((((p1 ∨ (p3 ∧ (p2 ∧ p1))) → (p3 ∨ (p4 ∧ False))) ∨ p3) ∧ p4) ∨ True))) ∨ (p2 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314825517973102854873593545899 : (p3 ∨ ((((((p1 ∧ p2) ∧ p5) ∨ (p5 → (True → p3))) ∨ True) ∨ p5) ∨ (((((p2 ∨ p2) ∧ True) → ((True ∧ True) → p4)) ∧ p1) ∨ False))) := by
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
theorem thm_5_vars_185057332899748625869333583157 : (((False ∧ p3) ∨ (p4 → (((p4 → False) ∧ (p1 → p2)) ∨ p2))) ∨ (((((p2 ∨ (p2 ∧ p5)) ∨ p2) ∧ p5) ∨ (p3 ∨ p5)) ∨ (False → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257643681101564690069863246929 : ((p3 ∨ p2) → ((p2 ∧ True) ∨ ((p4 ∧ ((True ∧ ((p2 ∧ (p4 → (p5 → p3))) ∧ p4)) ∧ p4)) ∨ ((p2 ∧ (p1 ∨ p4)) → (p4 ∨ p1))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h7 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h7
  case inr h8 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h8
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_659029520246098450425774800814 : ((((p1 → (p3 ∨ (((((p4 ∧ p4) ∧ (p1 ∨ True)) ∨ p1) → (p5 ∧ ((p5 ∨ (False ∧ False)) ∨ p3))) ∨ (p3 ∨ True)))) ∨ (True ∨ p1)) ∨ p1) ∧ True) := by
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



