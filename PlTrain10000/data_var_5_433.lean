variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207913718774032521437507485742 : (((p4 ∧ (p4 → False)) ∧ (p3 → True)) → (((p5 ∧ p4) ∧ p5) ∧ ((((p3 ∨ p1) ∨ True) ∨ ((p4 → p3) → False)) ∧ (p4 ∧ (p2 ∨ p2))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h6 : p4 := by
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h7 := h5 h6
  -- False on the left can always be used.
  apply False.elim h7
  -- Conjunctions on the left can always be decomposed.
  let h8 := h1.left
  let h9 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h10 := h8.left
  let h11 := h8.right
  -- One of the premise coincides with the conclusion.
  exact h10
  -- Conjunctions on the left can always be decomposed.
  let h12 := h1.left
  let h13 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h14 := h12.left
  let h15 := h12.right
  -- We want to use the implication h15 based on <expert-advice>. So we show its premise.
  have h16 : p4 := by
    -- One of the premise coincides with the conclusion.
    exact h14
  -- We have shown the premise of h15, we can now drive its conclusion.
  let h17 := h15 h16
  -- False on the left can always be used.
  apply False.elim h17
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h18 := h1.left
  let h19 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h20 := h18.left
  let h21 := h18.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h22 := h1.left
  let h23 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h24 := h22.left
  let h25 := h22.right
  -- One of the premise coincides with the conclusion.
  exact h24
  -- Conjunctions on the left can always be decomposed.
  let h26 := h1.left
  let h27 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h28 := h26.left
  let h29 := h26.right
  -- We want to use the implication h29 based on <expert-advice>. So we show its premise.
  have h30 : p4 := by
    -- One of the premise coincides with the conclusion.
    exact h28
  -- We have shown the premise of h29, we can now drive its conclusion.
  let h31 := h29 h30
  -- False on the left can always be used.
  apply False.elim h31



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208096942047198101597706225634 : ((((p4 ∧ False) ∧ p3) → (p1 ∧ p4)) → ((((p4 ∨ p3) ∨ (p2 ∧ p4)) → False) → (p2 ∨ ((p1 ∨ True) ∧ (True ∧ (p3 → (False ∧ p1))))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : ((p4 ∨ p3) ∨ (p2 ∧ p4)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- False on the left can always be used.
  apply False.elim h5
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h6 : ((p4 ∨ p3) ∨ (p2 ∧ p4)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h7 := h2 h6
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52956596529204511726718695448 : ((((p4 ∧ (p1 ∨ (((p5 → p1) → p4) ∧ (False ∨ p5)))) ∨ False) ∧ (p5 ∨ (p3 ∧ ((p5 ∨ p3) ∧ ((p5 ∨ False) ∨ (p1 ∨ p3)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307365150833320184992433545469 : (p1 ∨ (p4 ∨ (((p5 ∨ False) → (((p5 ∨ p5) ∨ p4) → (p4 ∨ (((((True → p2) → p5) → True) ∧ ((p2 → p1) ∨ False)) ∨ True)))) ∨ p4))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h5 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h6 =>
        -- False on the left can always be used.
        apply False.elim h6
    case inr h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h9 =>
        -- False on the left can always be used.
        apply False.elim h9
  case inr h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h11 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h10
    case inr h12 =>
      -- False on the left can always be used.
      apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39650243705076873590596585116 : (((p3 ∨ ((((p4 → False) → p3) ∧ p1) ∧ (p2 ∧ ((((p1 → p4) → p2) ∨ p4) → (p4 → (p1 ∧ ((p1 ∧ p4) ∨ p1))))))) ∧ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_239194843355929060750974706152 : ((p2 ∨ True) ∧ (p4 ∨ (((p1 ∧ p5) ∧ (((p3 ∨ p5) → p1) ∨ p2)) → ((((p1 → False) ∨ (False → p5)) ∨ False) ∨ ((True ∧ False) → p3))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h6 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- False on the left can always be used.
    apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_96474793315027265439286752037 : ((False ∨ ((((False → p4) ∨ True) ∨ (p2 ∨ p4)) ∧ (p4 ∨ (((p2 ∧ p4) ∧ (p1 ∨ p4)) ∧ ((p1 → (p2 → (True ∧ True))) ∨ False))))) → p4) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- False on the left can always be used.
    apply False.elim h2
  case inr h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Disjunctions on the left can always be decomposed.
        cases h5
        case inl h8 =>
          -- One of the premise coincides with the conclusion.
          exact h8
        case inr h9 =>
          -- Conjunctions on the left can always be decomposed.
          let h10 := h9.left
          let h11 := h9.right
          -- Conjunctions on the left can always be decomposed.
          let h12 := h10.left
          let h13 := h10.right
          -- Conjunctions on the left can always be decomposed.
          let h14 := h12.left
          let h15 := h12.right
          -- Disjunctions on the left can always be decomposed.
          cases h13
          case inl h16 =>
            -- Disjunctions on the left can always be decomposed.
            cases h11
            case inl h17 =>
              -- One of the premise coincides with the conclusion.
              exact h15
            case inr h18 =>
              -- False on the left can always be used.
              apply False.elim h18
          case inr h19 =>
            -- Disjunctions on the left can always be decomposed.
            cases h11
            case inl h20 =>
              -- One of the premise coincides with the conclusion.
              exact h19
            case inr h21 =>
              -- False on the left can always be used.
              apply False.elim h21
      case inr h22 =>
        -- Disjunctions on the left can always be decomposed.
        cases h5
        case inl h23 =>
          -- One of the premise coincides with the conclusion.
          exact h23
        case inr h24 =>
          -- Conjunctions on the left can always be decomposed.
          let h25 := h24.left
          let h26 := h24.right
          -- Conjunctions on the left can always be decomposed.
          let h27 := h25.left
          let h28 := h25.right
          -- Conjunctions on the left can always be decomposed.
          let h29 := h27.left
          let h30 := h27.right
          -- Disjunctions on the left can always be decomposed.
          cases h28
          case inl h31 =>
            -- Disjunctions on the left can always be decomposed.
            cases h26
            case inl h32 =>
              -- One of the premise coincides with the conclusion.
              exact h30
            case inr h33 =>
              -- False on the left can always be used.
              apply False.elim h33
          case inr h34 =>
            -- Disjunctions on the left can always be decomposed.
            cases h26
            case inl h35 =>
              -- One of the premise coincides with the conclusion.
              exact h34
            case inr h36 =>
              -- False on the left can always be used.
              apply False.elim h36
    case inr h37 =>
      -- Disjunctions on the left can always be decomposed.
      cases h37
      case inl h38 =>
        -- Disjunctions on the left can always be decomposed.
        cases h5
        case inl h39 =>
          -- One of the premise coincides with the conclusion.
          exact h39
        case inr h40 =>
          -- Conjunctions on the left can always be decomposed.
          let h41 := h40.left
          let h42 := h40.right
          -- Conjunctions on the left can always be decomposed.
          let h43 := h41.left
          let h44 := h41.right
          -- Conjunctions on the left can always be decomposed.
          let h45 := h43.left
          let h46 := h43.right
          -- Disjunctions on the left can always be decomposed.
          cases h44
          case inl h47 =>
            -- Disjunctions on the left can always be decomposed.
            cases h42
            case inl h48 =>
              -- One of the premise coincides with the conclusion.
              exact h46
            case inr h49 =>
              -- False on the left can always be used.
              apply False.elim h49
          case inr h50 =>
            -- Disjunctions on the left can always be decomposed.
            cases h42
            case inl h51 =>
              -- One of the premise coincides with the conclusion.
              exact h50
            case inr h52 =>
              -- False on the left can always be used.
              apply False.elim h52
      case inr h53 =>
        -- Disjunctions on the left can always be decomposed.
        cases h5
        case inl h54 =>
          -- One of the premise coincides with the conclusion.
          exact h54
        case inr h55 =>
          -- Conjunctions on the left can always be decomposed.
          let h56 := h55.left
          let h57 := h55.right
          -- Conjunctions on the left can always be decomposed.
          let h58 := h56.left
          let h59 := h56.right
          -- Conjunctions on the left can always be decomposed.
          let h60 := h58.left
          let h61 := h58.right
          -- Disjunctions on the left can always be decomposed.
          cases h59
          case inl h62 =>
            -- Disjunctions on the left can always be decomposed.
            cases h57
            case inl h63 =>
              -- One of the premise coincides with the conclusion.
              exact h61
            case inr h64 =>
              -- False on the left can always be used.
              apply False.elim h64
          case inr h65 =>
            -- Disjunctions on the left can always be decomposed.
            cases h57
            case inl h66 =>
              -- One of the premise coincides with the conclusion.
              exact h65
            case inr h67 =>
              -- False on the left can always be used.
              apply False.elim h67



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191583668832932393972686337258 : ((p2 ∧ ((False → False) ∨ (p2 → (p2 ∨ (p2 ∨ p3))))) ∨ ((((True ∨ False) → ((p4 ∨ p3) ∧ False)) ∧ True) → (((p4 ∨ p5) ∧ p4) ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (True ∨ False) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117344386611659942495931437302 : ((False ∧ ((True ∨ False) → (p1 → (False ∧ ((p3 ∨ (p3 ∧ ((p5 ∨ (p2 ∧ p1)) → (p5 ∧ p3)))) ∧ (p4 ∨ (False → p2))))))) ∨ (p4 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257439674480340464004643731407 : ((p3 ∨ True) → (((p5 ∨ ((p1 ∧ (p5 ∧ p2)) ∧ (p5 → (((p2 → p3) ∨ True) ∧ p2)))) ∨ (p2 → ((p4 ∧ p5) → False))) ∨ (p5 ∨ True))) := by
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
theorem thm_5_vars_8720270821199417769993939676 : (((((((((p4 → (p2 ∨ p2)) ∨ p5) → (p2 → p3)) ∧ p3) → ((p4 ∧ (p1 → p5)) → p1)) ∧ p1) ∧ (p4 → (False ∨ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_744372097056167575600483024335 : ((((p2 ∧ True) → ((((p5 ∨ False) → ((p3 ∧ ((p5 → p3) ∧ ((((p3 ∨ False) ∧ True) ∨ p5) ∧ p1))) ∨ (p2 ∨ p4))) → False) → p3)) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  have h5 : ((p5 ∨ False) → ((p3 ∧ ((p5 → p3) ∧ ((((p3 ∨ False) ∧ True) ∨ p5) ∧ p1))) ∨ (p2 ∨ p4))) := by
    -- Implications on the right can always be decomposed.
    intro h6
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h8 =>
      -- False on the left can always be used.
      apply False.elim h8
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h9 := h2 h5
  -- False on the left can always be used.
  apply False.elim h9
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_755963673360104637329296957373 : (((p1 ∧ ((((p2 ∧ (p3 ∧ (p5 → p2))) ∨ (p4 ∧ (p5 ∧ False))) ∨ (p1 ∨ ((False ∧ p4) ∨ ((True ∧ (False → False)) ∧ p3)))) → p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147801247724730373635516069716 : (((p1 ∧ (p2 ∨ (((False → (True → (p1 ∨ ((p2 → (p5 ∨ True)) ∨ True)))) ∨ False) ∧ (p1 ∧ p5)))) → False) ∨ (False → ((p3 ∧ True) ∧ True))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245272928161024628561031036373 : ((p2 ∧ p1) ∨ (p3 → (p5 ∨ (((p4 → p4) → False) ∨ ((p5 ∧ (p2 ∨ ((p5 ∧ ((p3 → (True ∧ p4)) ∨ p2)) → (p4 ∧ p3)))) → True))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55132025191105028314793799861 : ((((p2 ∨ (True ∧ (p5 ∨ True))) ∧ p3) ∨ ((p4 ∨ (p3 ∨ p3)) ∧ ((((((False ∨ p5) → False) → p2) ∨ (p3 ∧ p1)) ∧ p3) ∨ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328625110025079065090632648017 : (True → ((p4 ∧ ((p5 ∨ ((((False ∨ (p4 ∧ p2)) ∨ p1) ∧ p4) ∨ p4)) ∧ p2)) ∨ (p5 → ((((p5 ∨ p3) ∨ (p1 ∧ False)) → p3) → p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : ((p5 ∨ p3) ∨ (p1 ∧ False)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305302736050197041889644743590 : (p1 ∨ (((p2 ∨ ((False → p5) ∧ (p5 ∧ (p5 → p3)))) ∨ ((p3 → False) ∨ (True ∨ (p3 → p4)))) ∨ (((p2 ∧ p3) ∧ (p1 → False)) → p2))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47205585838911369117599872843 : ((((((True ∨ p4) → (p5 → (False → False))) ∧ (p5 → p3)) ∧ (((True ∧ True) ∨ p5) ∧ (p5 ∨ ((False → p3) → p2)))) ∨ (False ∧ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_685649346971411181642603220481 : ((((((True ∨ ((p5 ∧ (True ∨ p5)) ∨ p3)) ∧ ((p5 → (True ∨ p5)) → (p4 ∧ p3))) ∨ False) → ((p4 → ((p3 ∨ p2) ∨ False)) ∨ True)) ∨ False) ∧ True) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Conjunctions on the left can always be decomposed.
        let h8 := h7.left
        let h9 := h7.right
        -- Disjunctions on the left can always be decomposed.
        cases h9
        case inl h10 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h11 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h13 =>
    -- False on the left can always be used.
    apply False.elim h13
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134481282760532568734587361723 : ((((((p1 ∨ ((((p1 ∧ True) ∧ False) ∨ p2) ∨ (p2 → p2))) → ((False ∧ p4) ∨ (p1 ∨ p5))) ∧ True) ∨ p1) → p4) ∨ ((p2 ∧ p4) → p4)) := by
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
theorem thm_5_vars_38978073664389501642421195544 : ((((p2 ∧ p5) ∧ (((True ∨ ((p5 ∨ p5) → (False ∧ p4))) → p4) → ((p3 ∨ p4) → (False ∧ (p3 ∨ ((p3 → True) ∨ p3)))))) ∧ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118633135404279575504989280173 : ((p4 ∨ (((p4 ∧ p5) → p1) ∨ (p4 ∧ ((p1 → (True ∧ (p5 ∧ p2))) ∧ (p5 ∨ (((p4 → (p4 → p2)) → False) ∧ True)))))) ∨ (True ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46985480942404110374873186184 : (((((p5 ∧ (False ∧ (p5 → (((p3 ∨ (p2 → p2)) ∧ p1) ∨ ((False → p2) ∨ True))))) → (p1 ∨ (p1 ∧ p1))) → p3) ∨ (p4 → True)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218441406523944389864788433818 : (((p3 ∧ p3) → (False ∧ False)) → ((p5 ∧ ((((p1 ∨ False) → p5) ∨ p2) ∧ p3)) → (((p4 ∨ (p1 → (p1 ∧ (p2 ∧ p3)))) ∧ p4) ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h7 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h8 : (p3 ∧ p3) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h6
      -- One of the premise coincides with the conclusion.
      exact h6
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h9 := h1 h8
    -- We need to get the left conjuct of h9 based on <expert-advice>.
    let h10 := h9.left
    -- False on the left can always be used.
    apply False.elim h10
  case inr h11 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_791900719342852857262296937438 : (((True → (((p4 ∧ (((False → p2) → (False ∨ (p3 ∨ p1))) ∧ ((p5 ∨ p2) ∧ (((True ∧ True) ∨ p5) ∧ p4)))) ∨ p4) ∨ (p5 → True))) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137044012962199347353833463795 : (((False → True) → (((p3 ∧ p1) ∧ p1) ∧ (True ∧ ((p3 ∧ ((True ∨ p4) ∨ (p5 ∧ (p4 ∧ False)))) ∧ (p1 ∧ p4))))) ∨ (p4 ∨ (p3 → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_241821022547198478552045734269 : ((p1 → p1) ∧ ((((p4 ∨ True) → (False ∨ (((p2 ∨ p1) ∧ (p4 → (True ∧ p1))) ∧ (p4 ∨ False)))) ∨ (p3 ∧ (False → (p3 → True)))) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118455669947671099425940288999 : ((p3 ∨ (((((p4 → p3) → ((p2 ∨ False) → (p4 → ((False ∧ (p3 ∨ (p3 ∧ True))) ∨ p1)))) ∧ (False → p3)) → p4) ∨ p4)) ∨ (True ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159831329132484271634712531162 : (((p4 ∨ ((p4 ∧ ((p4 ∧ False) → (p3 ∧ p2))) → ((False → p1) → ((p5 ∧ p1) ∨ False)))) ∨ p2) → ((p4 ∨ (p3 ∨ p4)) ∨ (p5 → p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h3 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h5
      -- One of the premise coincides with the conclusion.
      exact h5
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_613810829284289207664413392086 : (((((p2 → (((p4 → p1) ∧ ((((((p5 ∧ (False ∨ True)) ∧ p5) → p5) ∨ p3) ∧ False) ∨ True)) ∨ p4)) ∧ ((False → True) → p4)) ∨ True) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_623734793759204116468209218327 : ((((p1 ∨ ((((p3 ∨ (p4 → p3)) → p3) ∧ (((((p2 ∨ True) ∧ (p2 → p1)) ∨ p5) ∨ True) ∨ (p2 ∧ p5))) → (p4 ∨ True))) ∨ True) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_739301583402481059758566676033 : ((((p4 ∧ p3) ∨ (((((p5 → (p2 ∧ p5)) → ((p5 → p1) → ((p4 ∧ (p5 → False)) ∧ True))) ∨ p4) → True) → (False ∧ (p5 ∧ p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68598047631904833569403029384 : ((p4 → (((((((p1 → (True ∧ False)) ∧ True) → p5) → (p4 ∨ (False → True))) ∧ ((p4 → p5) ∨ (p1 ∨ (p4 ∧ False)))) ∧ p2) ∨ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356615955648755665909282186383 : (p5 → ((((p4 ∨ True) ∧ ((p5 ∧ p2) ∧ p2)) ∨ p2) ∨ ((False ∧ (p3 → (p1 ∧ (False ∧ (p3 ∨ (True → p5)))))) ∨ ((p3 ∨ True) → p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h4 =>
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41857849412421135692976984418 : (((((p1 → p1) ∧ p4) ∨ (p1 ∧ ((False ∧ (p1 ∨ p1)) ∨ ((((True ∧ p1) → p1) ∧ ((True → True) ∧ (False → p3))) → p1)))) ∨ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115820749118747647296819439499 : ((((p2 ∧ False) ∨ (False ∨ p5)) ∧ ((((p2 → (p3 ∨ ((p3 ∨ (False ∧ (p2 → p3))) → p4))) → p2) → (False → p1)) ∧ False)) ∨ (False → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199468217236450634408769070249 : (((False ∨ (p4 ∧ (False ∧ (p1 ∨ p1)))) ∨ p3) → ((((p4 ∨ p4) ∧ (((((False ∧ p2) → True) ∧ (False ∧ p5)) ∨ p3) → p2)) → p2) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h3 =>
      -- False on the left can always be used.
      apply False.elim h3
    case inr h4 =>
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- False on the left can always be used.
      apply False.elim h7
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111139777713923750272981285270 : (((((((p5 ∧ p4) ∧ True) ∧ p1) ∨ p5) ∧ (((((p4 ∧ p4) → p2) ∨ False) → ((False → p5) ∧ (p2 ∧ p4))) ∨ p3)) ∧ False) ∨ (True ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214428631603502559661270756590 : (((p3 → (p2 ∨ False)) → p3) ∨ ((p4 → (p3 ∧ (p4 → p2))) ∨ (True ∨ (((True ∨ ((p1 → (p4 → (p4 ∨ p1))) ∧ p2)) ∧ p4) ∧ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135642360958153174040157338369 : ((((False ∨ (((p1 ∧ (True ∧ True)) ∧ True) ∨ ((True → p3) ∨ p3))) ∨ (True ∧ p4)) → (((p4 → False) ∧ True) ∨ True)) ∨ (True ∧ (p1 → True))) := by
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
theorem thm_5_vars_137815187628700161875188460403 : ((p3 ∨ ((((((p2 ∧ (p2 ∨ p4)) ∧ p4) ∨ (((((p4 → p4) ∨ False) ∨ p1) → False) ∧ p3)) ∨ p4) ∨ True) ∨ p4)) ∨ (p3 ∨ (p4 → p3))) := by
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
theorem thm_5_vars_206097698709279789092607978049 : ((p3 ∧ (p2 → ((p5 ∧ p5) ∧ p1))) ∨ (True ∧ (p1 ∨ ((False ∨ ((p4 → (((p3 ∧ p5) ∨ (p2 ∨ p3)) ∧ (False → False))) ∨ True)) ∨ p4)))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_590523049349032034454285571778 : ((((((p2 → p3) → (p4 ∧ (p3 ∨ ((False ∨ p1) ∨ ((True → (p3 ∨ p3)) → (p4 → (p5 ∧ (False ∧ (p3 ∧ p1))))))))) → False) ∧ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119086137743933508942510137377 : ((p1 → ((p1 ∧ ((p2 ∧ p3) ∨ ((((False ∨ (p2 → p5)) ∨ p4) → False) ∨ False))) ∨ (((False → p5) ∧ p2) → (p2 → p1)))) ∨ (p3 ∧ p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
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
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323931323773084721322371835091 : (p5 ∨ ((((p5 ∨ True) ∧ (p4 ∧ (p3 → (p1 ∨ p1)))) ∨ (p1 → ((p1 ∧ p4) → p2))) → (((p1 ∨ (p3 → False)) → p4) ∨ (False → p5)))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h4.left
      let h7 := h4.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- False on the left can always be used.
      apply False.elim h8
    case inr h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h4.left
      let h11 := h4.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h12
      -- False on the left can always be used.
      apply False.elim h12
  case inr h13 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h14
    -- False on the left can always be used.
    apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41064201151833422802325962226 : ((((p5 ∧ ((((p4 ∧ p5) ∨ ((p2 ∧ p3) ∨ p1)) → (p3 ∧ ((True ∧ (True → (p2 ∧ True))) → True))) ∧ p1)) → (p2 ∧ p4)) ∨ True) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157275057762989368446108208434 : (((((p3 ∨ p1) ∨ p5) → (False ∧ ((False ∨ False) → (((True ∧ p1) ∨ (p5 ∧ p4)) ∨ p5)))) → p1) ∨ (True ∨ ((p5 → (False → p1)) ∧ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_632499404344431692577265655661 : (((((p3 ∨ (p3 → (((True ∧ p5) ∧ p1) ∧ ((p4 ∧ p2) ∧ (((p3 ∧ True) ∧ (((p1 ∨ p1) ∨ p1) ∧ True)) → False))))) → p3) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115278328425980071939556874256 : (((p5 ∨ (((p1 → p5) ∨ False) ∨ (True → (p1 → p3)))) ∨ ((((p2 ∧ (p2 → (p5 → p3))) → (p2 ∧ p3)) → p2) ∧ p4)) ∨ (p1 → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_229875552817214609783184475808 : ((p5 → (p3 ∨ False)) ∨ (True → (((p1 ∨ (p3 → ((False → p3) → p4))) ∧ p5) ∨ ((True ∨ True) → (((False ∨ (True → p2)) ∧ p3) → p3))))) := by
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
  cases h4
  case inl h6 =>
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h8 =>
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h9 =>
      -- One of the premise coincides with the conclusion.
      exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338809774945089382649051123759 : (p1 → ((p2 ∨ False) ∨ (p5 → (p4 → (((((True → (False ∨ (p1 ∨ (p2 ∧ (False → p5))))) ∨ p5) → p2) ∧ (p4 → p1)) ∨ (True ∨ True)))))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43695869850958773916955218382 : (((((p4 ∨ ((p3 ∧ (p3 ∨ (p3 ∧ True))) → True)) → (False ∧ (((p5 → p5) ∧ ((True ∧ (p4 ∨ p5)) → p5)) ∨ p4))) → p5) → p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192205581377607121261768195206 : ((((((p1 → (True ∧ p3)) → p4) → p5) → False) ∧ p1) → (((((p4 → False) → ((False ∧ (p5 ∧ p5)) ∨ p3)) ∨ (False ∨ p3)) ∨ True) ∧ p1)) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54126224968830792421515216117 : (((p1 ∨ ((True ∧ (((True ∧ p5) ∨ True) ∧ True)) ∨ False)) → (((p2 ∧ (p1 → False)) ∧ (p1 → ((True → p1) ∨ (True → p2)))) ∨ True)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h9 =>
        -- Conjunctions on the left can always be decomposed.
        let h10 := h9.left
        let h11 := h9.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h13 =>
      -- False on the left can always be used.
      apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204643732613574119631021864129 : (((p2 ∧ ((p3 ∧ False) ∧ p5)) ∨ p3) ∨ (((p4 ∨ (p4 ∨ (True → ((p2 ∨ p4) ∨ (True → True))))) ∨ (p2 ∨ p5)) ∧ ((False → False) ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52138400600097941197937612404 : ((((((False ∨ (p3 ∧ (False ∨ p1))) → p4) ∧ (False ∨ (p3 → p2))) ∨ (p2 ∧ p2)) → (((True ∧ p1) → p2) ∨ (True ∨ (p2 ∧ p2)))) ∨ p2) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- False on the left can always be used.
      apply False.elim h5
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135412854803804318236285761976 : ((((p1 ∧ p2) ∧ (((True → (((p2 ∧ True) ∧ ((p4 ∨ False) ∧ p3)) → False)) ∧ p3) ∨ False)) ∨ ((p3 ∨ p2) → True)) ∨ ((True ∨ False) ∧ p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134224687176913451649771576316 : ((((p1 ∨ ((p2 ∧ p4) → (p3 → p5))) ∨ (((p3 ∧ (p5 ∨ p2)) ∨ True) ∧ ((p2 ∧ (True ∨ False)) ∧ p5))) ∨ p2) ∨ ((False ∨ True) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185549985528019130947772794504 : ((p4 ∨ ((((p2 ∧ (p2 ∨ p1)) ∨ False) ∨ (True → p1)) ∨ True)) ∨ (False ∨ ((False → ((((p5 ∨ (p5 ∨ True)) ∧ p4) → True) ∧ p1)) ∧ False))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_720281249369767939552658069950 : ((((((False ∨ p4) ∧ p2) ∨ p2) → (p2 → ((p3 ∨ ((False ∨ ((p4 ∨ (p3 → p5)) ∨ p5)) ∨ (((p1 ∧ p5) ∨ p5) ∨ False))) ∧ True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193637861533104390181133595566 : ((True ∧ (True → (p5 ∨ (((False → p3) → p1) ∧ p5)))) → ((p2 ∨ p5) ∨ ((p5 ∧ ((p1 ∨ p1) → p2)) ∧ (False ∧ (p5 ∧ (p1 → p2)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116496637045241571113380839719 : (((p3 ∧ p1) ∧ ((p5 ∨ (False → ((p4 → (p1 ∧ True)) → (((False ∧ (((p3 ∨ p5) → False) ∨ True)) ∧ True) → p4)))) → p5)) ∨ (True ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_719315923310043550314732197828 : ((((p5 ∧ ((p1 ∧ False) → p1)) ∨ (((p1 ∧ (p3 → (True → ((p3 ∧ p2) ∧ p5)))) ∧ p5) → (p3 ∧ (((True ∨ p3) ∧ p2) ∧ p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_773300922948298255482839454993 : (((False ∨ (((p3 ∨ (p1 ∨ False)) ∨ (((p3 ∨ (p5 → (((False ∨ p5) ∨ p3) ∨ (p4 ∨ p1)))) → ((p2 ∧ p5) → p4)) ∨ p2)) ∧ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138045568990100278457250128516 : ((True → ((True → ((p4 ∧ p2) ∧ p2)) → ((p2 → p5) ∧ ((((((True ∧ p5) → True) → p2) ∧ False) ∨ p2) ∨ p4)))) ∨ (True ∨ (True → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_90373142082466955290059885328 : (((True ∧ p1) ∧ (((True → True) → (((p4 ∧ False) ∨ p3) ∧ (p3 ∧ (((p2 ∧ (True ∧ p4)) ∧ (True ∧ (False ∨ False))) ∧ p2)))) ∧ p4)) → False) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h3.left
  let h7 := h3.right
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h8 : (True → True) := by
    -- Implications on the right can always be decomposed.
    intro h9
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h10 := h6 h8
  -- We need to get the right conjuct of h10 based on <expert-advice>.
  let h11 := h10.right
  -- We need to get the right conjuct of h11 based on <expert-advice>.
  let h12 := h11.right
  -- We need to get the left conjuct of h12 based on <expert-advice>.
  let h13 := h12.left
  -- We need to get the right conjuct of h13 based on <expert-advice>.
  let h14 := h13.right
  -- We need to get the right conjuct of h14 based on <expert-advice>.
  let h15 := h14.right
  -- Disjunctions on the left can always be decomposed.
  cases h15
  case inl h16 =>
    -- False on the left can always be used.
    apply False.elim h16
  case inr h17 =>
    -- False on the left can always be used.
    apply False.elim h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135418884286494528068375450498 : ((((p5 → True) → (p5 ∨ (p3 → (p2 ∧ (((p2 ∧ p2) ∧ True) ∨ ((True ∧ False) ∨ False)))))) ∨ (True ∨ (p5 ∨ p2))) ∨ ((p4 → p4) → p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42283616228123476499200218295 : (((p1 ∧ (p2 ∨ (p5 ∨ (((((p2 ∨ (((p3 ∨ False) → p4) ∧ False)) → p2) ∧ True) ∨ False) → ((p1 → p4) ∨ (p3 → False)))))) ∨ True) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_700055920664593441392918534508 : (((((p5 → (p4 → p1)) ∧ (p4 → ((p3 ∨ (p2 → p4)) → p5))) → ((((p5 ∨ p4) ∧ p4) ∨ ((p5 ∧ p3) ∨ (p1 ∧ p4))) ∨ True)) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_779923822120252526450298759551 : (((p2 ∨ (((((p4 → ((False ∨ (True → p2)) ∨ False)) ∧ ((p3 → (((True → True) → p3) ∨ p5)) ∧ p3)) → p1) → p1) ∧ (p1 → p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_596644306832374584635287191938 : ((((((p3 ∧ ((p3 → False) ∨ p1)) ∨ p1) ∧ (((True ∨ ((p4 → False) ∨ True)) ∨ (True → p1)) ∨ (p4 ∧ (p5 → (p4 → p2))))) ∧ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300552893792162861577430982147 : (False ∨ (((((p3 ∧ p5) → ((p2 ∨ p2) ∨ (p3 → p4))) ∧ p1) → (p5 ∨ ((p4 → (p5 ∨ p5)) ∨ p2))) ∨ ((True ∨ p5) ∨ (p2 ∧ False)))) := by
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
theorem thm_5_vars_354603481051976002377099023761 : (p5 → ((((p1 ∧ (((False ∧ p5) ∨ p1) ∨ (p3 ∧ (((((p3 → (p1 ∧ p2)) ∧ (p3 ∨ False)) ∨ p2) ∨ p4) ∨ False)))) ∨ True) ∨ False) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_626689341739824190866636367000 : ((((p5 → ((p1 ∧ ((True → p2) ∨ ((((p4 → p5) ∨ p1) → (p2 ∧ (p5 ∨ (p4 ∧ True)))) ∨ (p4 ∨ (p4 ∨ p4))))) ∧ p1)) ∨ True) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_152867394209446124565279933947 : ((True ∧ ((p2 → ((p2 ∨ p5) ∧ (((p4 → ((p5 ∨ p1) ∧ p1)) → ((p3 ∧ False) ∧ False)) ∧ p2))) ∧ p2)) → ((p2 → False) ∨ (True ∨ p5))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54825780025534297083299430610 : (((False → ((p3 → p4) ∧ ((p5 → p1) → p4))) → (((p3 → (p3 ∧ ((p5 ∨ (p5 ∨ p1)) ∨ False))) → (p3 → p5)) ∨ (p2 ∨ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200128884360297415072430143335 : (((True → (p5 → True)) ∧ (False → (p2 → True))) → ((p4 → (p4 ∨ p4)) → ((p3 → p1) ∨ (p5 ∨ ((False ∧ (False ∨ False)) → (p2 ∧ p1)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h5
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- False on the left can always be used.
  apply False.elim h6
  -- Conjunctions on the left can always be decomposed.
  let h8 := h5.left
  let h9 := h5.right
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308563161510403355197656390831 : (p2 ∨ ((((False → (p5 ∧ (p4 → True))) → p2) ∨ (((False ∧ (((p4 ∧ (p5 ∨ p3)) ∧ p3) ∧ p3)) ∧ False) ∨ (False → (p5 → True)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150924181542357758805394399310 : ((((p5 → p5) ∨ (((False → p2) ∧ p1) ∨ (True → (p4 ∨ (p5 ∨ ((p1 ∧ (p4 ∧ p2)) ∧ p2)))))) ∨ p1) → ((p2 ∧ (False ∨ p4)) ∨ True)) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304025907061121467135164343484 : (p1 ∨ ((p1 ∧ ((True ∧ (p2 ∧ p1)) ∨ ((p3 ∧ ((False ∨ p1) ∨ ((p2 ∨ True) → p4))) ∧ ((((p3 ∨ True) ∧ p4) ∧ p4) ∨ False)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_326984111842846168203006721291 : (True → ((((p3 ∨ ((((p3 ∨ (p5 → ((p5 ∧ (p5 ∧ True)) → p2))) ∧ (p2 ∧ p4)) ∨ p2) ∨ p3)) ∨ p2) → ((p2 ∨ p4) → p5)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208722423970127641210995110174 : ((p1 ∧ (((True → True) ∨ p4) → p1)) → (((p5 → ((p4 → (p5 → p3)) → (((p3 ∨ p3) ∧ p5) ∨ False))) ∨ p3) ∨ (p1 → (p2 → p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137159465171530301174038421743 : ((False ∧ ((((((((p3 ∨ False) ∧ p5) ∧ ((True → True) ∨ p2)) → ((True ∨ p5) → p2)) ∨ p3) ∧ p1) ∧ p5) → False)) ∨ ((False ∧ p1) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40875997693051978518602378089 : (((((p2 ∨ ((p5 ∨ ((((False ∧ (False ∨ (p1 ∨ p4))) ∨ p1) → (False ∧ p3)) → False)) ∨ p1)) → (False ∨ p3)) ∧ (p4 ∨ p2)) ∨ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59217496891842564593313713970 : (((p1 ∨ p5) ∨ ((((True ∨ (False ∨ ((p2 ∧ (True ∨ p2)) ∧ p2))) ∧ p4) → p1) → (((p1 ∧ (p4 → (True → True))) ∨ p4) → p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114407653230415070147567107490 : (((((p2 → False) ∧ (p1 ∧ False)) ∨ ((((p1 → (True → p4)) → False) ∨ p4) ∨ (p4 → False))) ∨ (p1 ∨ (p4 → (p4 ∨ p5)))) ∨ (p2 ∨ p5)) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350964309152770006610860481209 : (p4 → (((p5 → (((p1 ∧ True) ∨ p3) → (p5 ∧ p2))) ∧ (p1 ∧ ((p1 ∨ (p3 ∨ False)) ∧ (p2 ∨ ((p3 ∨ p2) → p5))))) ∨ (False → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119478318752804215935691940896 : ((p4 → (p3 ∧ (((((p4 ∧ ((p3 ∨ p5) → (p5 ∧ (True ∨ (False ∧ True))))) ∧ p4) → False) → (p2 → (p3 → p1))) ∧ p3))) ∨ (p3 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190547897285379910830230167295 : (((((p1 ∧ (p3 ∧ p5)) → p3) ∨ (p5 → True)) → p2) ∨ ((((p1 ∧ (p3 ∨ p4)) → False) ∧ ((p3 → p4) ∧ ((p2 ∨ p1) → False))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_789753436682252328369368316647 : (((p5 ∨ ((p2 ∧ ((p4 ∨ p4) ∨ p1)) ∨ ((((((p5 ∨ ((False → (False ∨ True)) ∨ p2)) ∨ (p1 ∧ p4)) → p2) ∨ p2) ∨ True) ∧ True))) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_245484598924901162914985068136 : ((p2 ∧ p5) ∨ (((p4 ∧ (p3 ∨ ((p3 → ((p1 → (True ∨ True)) ∧ True)) ∧ p4))) ∨ True) ∧ (p4 ∨ (((p1 → (False → p1)) ∧ p4) ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_177629801240162516601335326963 : ((((((((p4 → p4) ∨ True) ∨ p1) ∧ (False ∨ p5)) → p3) ∧ p4) ∧ p3) ∨ ((p5 ∨ (p5 ∨ p5)) ∨ ((p5 ∨ (False ∨ (p2 ∨ p1))) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_672788873256798878121351858356 : (((((p3 → ((p5 → (((p1 → p1) ∧ p3) ∧ (p2 ∨ (True ∨ (True ∨ (p2 ∨ p3)))))) ∨ p1)) → (p1 ∨ False)) → (p5 → (p2 ∨ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_962546229259043449387115409976 : ((((True → p3) ∧ (p1 → (False ∨ ((p3 ∧ (p1 → ((p4 → p5) ∧ (((p2 ∨ p1) → ((p3 → p4) ∧ p4)) ∨ (p2 → p2))))) ∧ True)))) → p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- One of the premise coincides with the conclusion.
  exact h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_661445205936361579294844805285 : ((((((((True → True) → (p1 ∨ ((p1 ∨ True) ∧ ((p2 ∨ False) ∧ (p5 → False))))) → p4) → p1) ∧ ((p1 → True) ∧ p3)) → (p5 ∧ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_782387048900737710084314260804 : (((p3 ∨ ((((((True ∨ p4) ∧ (((False ∧ (p2 ∧ (p1 → True))) → (p3 ∧ p4)) ∧ p1)) ∨ (True → (p4 ∨ True))) ∨ p5) → p5) ∨ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171976515408848901013720299444 : (((p3 ∨ ((((True → p2) ∧ p1) ∨ (p4 ∧ False)) → (p4 ∧ p4))) ∧ (False ∨ False)) ∨ (((False → ((p5 ∧ True) ∧ False)) ∨ (p3 ∨ True)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148003497696369395258093770603 : ((((((p5 ∨ p2) ∨ (((p4 → False) ∨ p5) → (p3 ∧ True))) → (p5 ∧ p3)) ∧ (p4 ∧ p3)) ∨ (p5 → p1)) ∨ (((False → p1) ∨ False) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322537783309246700915030332098 : (p5 ∨ ((p5 ∧ (((p3 → (p2 ∨ (((p4 ∧ ((p4 ∧ (p4 → p1)) → ((False → (p4 ∧ p3)) ∨ p2))) → p5) ∧ p4))) → p2) ∨ p2)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



