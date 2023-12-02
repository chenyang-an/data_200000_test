variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_804672436956746830294506070443 : (((p3 → ((p3 → (p2 ∧ (False ∧ p3))) → (((p5 ∨ (((p5 ∧ (p3 ∧ p4)) ∨ True) → ((p3 ∨ p2) ∨ True))) ∨ p2) → (False ∧ p4)))) ∨ p1) ∧ True) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h6 : p3 := by
        -- One of the premise coincides with the conclusion.
        exact h1
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h7 := h2 h6
      -- We need to get the right conjuct of h7 based on <expert-advice>.
      let h8 := h7.right
      -- We need to get the left conjuct of h8 based on <expert-advice>.
      let h9 := h8.left
      -- False on the left can always be used.
      apply False.elim h9
    case inr h10 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h11 : p3 := by
        -- One of the premise coincides with the conclusion.
        exact h1
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h12 := h2 h11
      -- We need to get the right conjuct of h12 based on <expert-advice>.
      let h13 := h12.right
      -- We need to get the left conjuct of h13 based on <expert-advice>.
      let h14 := h13.left
      -- False on the left can always be used.
      apply False.elim h14
  case inr h15 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h16 : p3 := by
      -- One of the premise coincides with the conclusion.
      exact h1
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h17 := h2 h16
    -- We need to get the right conjuct of h17 based on <expert-advice>.
    let h18 := h17.right
    -- We need to get the left conjuct of h18 based on <expert-advice>.
    let h19 := h18.left
    -- False on the left can always be used.
    apply False.elim h19
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h20 =>
    -- Disjunctions on the left can always be decomposed.
    cases h20
    case inl h21 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h22 : p3 := by
        -- One of the premise coincides with the conclusion.
        exact h1
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h23 := h2 h22
      -- We need to get the right conjuct of h23 based on <expert-advice>.
      let h24 := h23.right
      -- We need to get the left conjuct of h24 based on <expert-advice>.
      let h25 := h24.left
      -- False on the left can always be used.
      apply False.elim h25
    case inr h26 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h27 : p3 := by
        -- One of the premise coincides with the conclusion.
        exact h1
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h28 := h2 h27
      -- We need to get the right conjuct of h28 based on <expert-advice>.
      let h29 := h28.right
      -- We need to get the left conjuct of h29 based on <expert-advice>.
      let h30 := h29.left
      -- False on the left can always be used.
      apply False.elim h30
  case inr h31 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h32 : p3 := by
      -- One of the premise coincides with the conclusion.
      exact h1
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h33 := h2 h32
    -- We need to get the right conjuct of h33 based on <expert-advice>.
    let h34 := h33.right
    -- We need to get the left conjuct of h34 based on <expert-advice>.
    let h35 := h34.left
    -- False on the left can always be used.
    apply False.elim h35
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186920373839189271711662808849 : ((((p2 → p5) → p4) ∧ ((p2 → (p2 → p1)) → (p3 → p2))) → (p4 → (((((p5 → (p3 → p1)) ∧ p5) ∨ (p5 → p2)) ∨ True) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_725517591557881228607277479339 : (((((False ∧ p1) ∧ True) ∨ (((((False → ((p5 ∨ p1) ∧ p5)) → p1) ∨ (p5 ∧ p1)) ∨ (True → False)) ∨ (True ∨ ((p1 ∨ p3) ∨ p2)))) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_187078251483419277674701938678 : (((True → False) ∧ (p1 → ((p2 ∨ False) ∨ (p3 → (p4 ∨ False))))) → ((p3 → (((p2 → (p5 ∧ p1)) → False) ∨ (p1 ∨ p5))) → (p1 ∧ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h5 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h5
  -- False on the left can always be used.
  apply False.elim h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64740347567359586026664539801 : ((p2 ∨ ((((p3 → ((((p5 ∧ p1) ∧ p2) → p4) ∨ p1)) → ((p1 ∨ p2) ∧ ((True → ((True → False) → False)) → p4))) → p5) ∧ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_139619151100825843303876549455 : ((((((((p2 → False) ∨ False) ∧ p4) ∧ (p5 ∨ p4)) ∨ False) ∨ ((p1 ∧ (p4 → (p1 ∨ (p4 ∧ p1)))) → p3)) → p4) → ((True → False) → p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65446179152264982196135520608 : ((p3 ∨ ((p1 ∨ p3) ∨ ((((p3 ∧ (p2 → (False ∨ ((p3 → False) → p4)))) ∨ ((p5 ∨ (p3 → (True → p4))) → p1)) → p2) ∧ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116595642481346028825243756552 : (((p5 ∨ p1) ∧ (((p3 ∨ p4) ∧ (False → ((p3 ∧ (p3 ∧ True)) → (((True ∨ p4) → ((p1 → p2) ∨ p4)) → False)))) ∨ p1)) ∨ (False → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259373062001859540367672701732 : ((False → p3) → ((((True ∨ p3) ∨ False) → (p4 → (p5 → ((False ∧ (((p3 ∨ True) → p4) ∨ p4)) ∧ (p5 ∧ ((p5 ∧ p3) ∧ False)))))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313977102892571498540597393348 : (p3 ∨ (((p3 → (((p4 ∧ True) → p5) ∧ ((p1 ∧ False) ∨ p5))) ∧ ((p5 ∨ ((True ∨ False) → False)) ∧ ((p4 → False) ∨ p2))) ∨ (True ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322535056685073742590460718625 : (p5 ∨ ((p4 ∧ ((p2 ∧ (False ∨ p3)) → ((((False → (p4 ∨ False)) ∧ (p5 ∧ p1)) ∨ (p2 ∨ True)) ∧ (((p1 → p3) → p5) ∨ p5)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191118960233504536365613004063 : (((p3 ∨ (False → p2)) ∧ (p5 ∨ (p3 ∧ (p4 ∧ p4)))) ∨ (False → (True → ((((p3 ∧ (p4 ∨ False)) ∨ (p4 → p3)) ∧ (p1 ∧ False)) → False)))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h5.left
      let h11 := h5.right
      -- False on the left can always be used.
      apply False.elim h11
    case inr h12 =>
      -- False on the left can always be used.
      apply False.elim h12
  case inr h13 =>
    -- Conjunctions on the left can always be decomposed.
    let h14 := h5.left
    let h15 := h5.right
    -- False on the left can always be used.
    apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171442559050711849124030100810 : (((False ∧ ((p1 ∨ ((p2 → ((p2 → True) ∨ (p5 → p2))) ∨ p4)) ∧ p2)) ∧ False) ∨ ((p4 ∧ p3) ∨ ((p4 ∧ (p5 ∧ p1)) → (p3 → p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  let h5 := h4.left
  let h6 := h4.right
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_355890955728234423732346788666 : (p5 → ((p2 → ((((p4 ∨ p1) ∧ (((((p1 → p4) ∧ p2) → p5) → (p4 ∨ p4)) ∧ (False → p5))) → p3) ∨ p2)) ∨ ((p5 → True) ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187638540522074251993979597184 : ((p5 ∨ (((p1 ∨ p5) ∨ p4) ∧ (True ∨ (p1 ∨ (p1 → p3))))) → (False ∨ ((p3 ∨ (((False ∧ (False ∨ (p5 ∨ p4))) ∨ False) → p5)) ∨ False))) := by
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
    -- Implications on the right can always be decomposed.
    intro h3
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- False on the left can always be used.
      apply False.elim h5
    case inr h7 =>
      -- False on the left can always be used.
      apply False.elim h7
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- Disjunctions on the left can always be decomposed.
        cases h10
        case inl h13 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h14
          -- Disjunctions on the left can always be decomposed.
          cases h14
          case inl h15 =>
            -- Conjunctions on the left can always be decomposed.
            let h16 := h15.left
            let h17 := h15.right
            -- False on the left can always be used.
            apply False.elim h16
          case inr h18 =>
            -- False on the left can always be used.
            apply False.elim h18
        case inr h19 =>
          -- Disjunctions on the left can always be decomposed.
          cases h19
          case inl h20 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h21
            -- Disjunctions on the left can always be decomposed.
            cases h21
            case inl h22 =>
              -- Conjunctions on the left can always be decomposed.
              let h23 := h22.left
              let h24 := h22.right
              -- False on the left can always be used.
              apply False.elim h23
            case inr h25 =>
              -- False on the left can always be used.
              apply False.elim h25
          case inr h26 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- We want to use the implication h26 based on <expert-advice>. So we show its premise.
            have h27 : p1 := by
              -- One of the premise coincides with the conclusion.
              exact h12
            -- We have shown the premise of h26, we can now drive its conclusion.
            let h28 := h26 h27
            -- One of the premise coincides with the conclusion.
            exact h28
      case inr h29 =>
        -- Disjunctions on the left can always be decomposed.
        cases h10
        case inl h30 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h31
          -- Disjunctions on the left can always be decomposed.
          cases h31
          case inl h32 =>
            -- Conjunctions on the left can always be decomposed.
            let h33 := h32.left
            let h34 := h32.right
            -- False on the left can always be used.
            apply False.elim h33
          case inr h35 =>
            -- False on the left can always be used.
            apply False.elim h35
        case inr h36 =>
          -- Disjunctions on the left can always be decomposed.
          cases h36
          case inl h37 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h38
            -- Disjunctions on the left can always be decomposed.
            cases h38
            case inl h39 =>
              -- Conjunctions on the left can always be decomposed.
              let h40 := h39.left
              let h41 := h39.right
              -- False on the left can always be used.
              apply False.elim h40
            case inr h42 =>
              -- False on the left can always be used.
              apply False.elim h42
          case inr h43 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h44
            -- Disjunctions on the left can always be decomposed.
            cases h44
            case inl h45 =>
              -- Conjunctions on the left can always be decomposed.
              let h46 := h45.left
              let h47 := h45.right
              -- False on the left can always be used.
              apply False.elim h46
            case inr h48 =>
              -- False on the left can always be used.
              apply False.elim h48
    case inr h49 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h50 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h51
        -- Disjunctions on the left can always be decomposed.
        cases h51
        case inl h52 =>
          -- Conjunctions on the left can always be decomposed.
          let h53 := h52.left
          let h54 := h52.right
          -- False on the left can always be used.
          apply False.elim h53
        case inr h55 =>
          -- False on the left can always be used.
          apply False.elim h55
      case inr h56 =>
        -- Disjunctions on the left can always be decomposed.
        cases h56
        case inl h57 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h58
          -- Disjunctions on the left can always be decomposed.
          cases h58
          case inl h59 =>
            -- Conjunctions on the left can always be decomposed.
            let h60 := h59.left
            let h61 := h59.right
            -- False on the left can always be used.
            apply False.elim h60
          case inr h62 =>
            -- False on the left can always be used.
            apply False.elim h62
        case inr h63 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h64
          -- Disjunctions on the left can always be decomposed.
          cases h64
          case inl h65 =>
            -- Conjunctions on the left can always be decomposed.
            let h66 := h65.left
            let h67 := h65.right
            -- False on the left can always be used.
            apply False.elim h66
          case inr h68 =>
            -- False on the left can always be used.
            apply False.elim h68



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340705981322567787513095214716 : (p2 → (((((p1 ∧ p1) → ((p1 ∧ p3) ∧ (p3 → (((p4 ∧ True) ∨ True) → False)))) ∧ ((p4 ∨ False) → ((p3 ∨ p5) ∨ p4))) ∧ True) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200684959051294637832917662934 : ((p2 ∧ ((False ∨ ((p3 → p4) ∧ p1)) ∧ p4)) → (((p4 ∨ p2) → p1) → ((p3 ∨ (p4 → ((p2 → p3) ∨ (p3 → p4)))) ∧ (True ∨ p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
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
    -- Implications on the right can always be decomposed.
    intro h11
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h12
    -- One of the premise coincides with the conclusion.
    exact h11
  -- Conjunctions on the left can always be decomposed.
  let h13 := h1.left
  let h14 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h15 := h14.left
  let h16 := h14.right
  -- Disjunctions on the left can always be decomposed.
  cases h15
  case inl h17 =>
    -- False on the left can always be used.
    apply False.elim h17
  case inr h18 =>
    -- Conjunctions on the left can always be decomposed.
    let h19 := h18.left
    let h20 := h18.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_316609542054201082524829626992 : (p3 ∨ (p4 ∨ ((((p5 ∧ (p4 ∨ ((False ∧ (p3 → ((p4 ∧ p5) ∨ p2))) → (p4 → p5)))) → p2) ∧ (((True ∧ False) → p3) → p4)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244188362196143623497555729742 : ((True ∧ p5) ∨ ((((((p5 → p4) → (True ∧ ((p1 ∨ ((p5 ∧ p1) ∧ p2)) ∧ p4))) ∨ (p2 → False)) → (p1 → (True ∨ p5))) → p1) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134894202064040044493066826363 : (((p5 → ((((p5 ∧ ((p2 ∨ p2) ∧ (((True ∨ (p1 → p2)) ∧ False) → p1))) ∧ p3) ∧ True) ∧ (p3 ∧ p1))) → p1) ∨ ((False ∨ False) → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- False on the left can always be used.
    apply False.elim h2
  case inr h3 =>
    -- False on the left can always be used.
    apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328305229318603660937119834524 : (True → ((p3 ∧ ((((p2 ∨ p5) ∨ p1) ∧ p5) ∧ (False ∨ (p2 ∧ (p2 ∨ ((p3 ∨ (True → True)) → p3)))))) ∨ ((p2 ∧ p4) → (p5 → p2)))) := by
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
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45547842408522256085904658226 : (((p2 ∨ (((p1 ∨ (((((p1 ∨ p4) ∨ (p1 ∧ p2)) → ((p4 ∨ ((p1 → True) ∧ p5)) ∨ p5)) ∨ p2) ∧ p1)) ∧ p3) → True)) → p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_381667377697435341135726087678 : ((((((p1 ∨ (p1 ∧ ((((p3 ∨ p4) ∨ p2) ∧ (p2 → (p5 → ((p2 ∨ p5) → (True → (True ∧ p3)))))) ∨ p3))) ∧ p5) ∨ True) ∨ True) ∧ True) ∧ True) := by
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
theorem thm_5_vars_54405632719304259844358938303 : (((((p5 ∨ p1) ∨ (p2 ∨ (True ∧ True))) ∧ p1) ∨ ((p2 ∧ p5) ∧ (True ∧ ((((p2 ∨ (p3 ∨ p5)) ∧ True) ∨ p1) ∧ (False ∨ p3))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117415900189413996647470540194 : ((p1 ∧ (((p5 ∧ ((p2 ∨ (p4 ∧ ((p2 ∨ p1) ∧ (False ∨ ((p4 → False) ∨ (p5 → False)))))) ∧ p2)) ∧ p2) ∨ (False ∧ p2))) ∨ (True ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249559704844318932603486653702 : ((p5 ∨ p2) ∨ ((p2 → ((True ∨ (False ∨ p2)) → p1)) ∨ ((p5 ∧ False) ∨ (False ∨ ((p2 ∧ p1) → ((p1 → (p4 ∧ (p4 ∧ True))) → p1)))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147981259522073571783028150496 : (((((p4 → p5) ∧ (p2 ∨ ((p2 ∨ (p5 → (p1 → p2))) ∧ (True → (p3 ∨ False))))) ∧ p1) ∨ (p5 ∧ p4)) ∨ (False → ((p4 → p5) ∧ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50642501105138781527706988474 : (((((p2 ∧ p3) ∧ (((p1 → p1) → ((p1 ∨ p2) ∧ True)) → p5)) → (((p3 ∨ False) → p2) ∨ False)) → ((p4 ∨ p2) ∨ (False ∨ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56682826626309945899114883655 : ((((p4 → p1) ∧ p5) ∧ (((p4 ∧ ((p2 ∨ ((p1 ∧ p4) ∧ True)) → True)) ∧ ((p1 ∧ False) → ((p5 ∧ p3) → (False → p1)))) → p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_265997358544886023639978576009 : (True ∧ (p1 → ((((((p4 → p3) ∧ ((((p3 ∨ p5) ∧ p4) ∧ p3) ∧ True)) → (True ∧ ((p1 ∨ False) → p5))) → (p2 ∨ p4)) ∨ p3) ∨ p1))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198298038821559365962422160683 : ((p1 ∧ ((p1 → (p5 ∨ (p2 ∧ True))) ∨ True)) ∨ ((p5 ∨ True) → (p2 → ((((p2 ∨ (p5 ∨ True)) ∧ p2) ∧ p1) ∨ ((p5 ∧ p1) ∨ True))))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165907633709635209088799851976 : (((False → (p3 ∧ True)) → ((((p5 ∨ p5) ∨ (p3 ∨ p3)) → (p1 → p1)) → (p1 ∧ p2))) ∨ (p1 → (True → ((False → p2) ∨ (p5 ∨ p2))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114484685362476964382041984199 : ((((((p3 ∨ ((((p1 ∧ True) ∨ p3) → p4) → p5)) ∨ p3) → False) ∧ (p2 ∨ (p5 ∨ p2))) → ((p5 ∧ (p4 ∨ p5)) → p1)) ∨ (p1 ∨ p3)) := by
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
  cases h4
  case inl h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h1.left
    let h7 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h9 : ((p3 ∨ ((((p1 ∧ True) ∨ p3) → p4) → p5)) ∨ p3) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h10
        -- One of the premise coincides with the conclusion.
        exact h3
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h11 := h6 h9
      -- False on the left can always be used.
      apply False.elim h11
    case inr h12 =>
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
        have h14 : ((p3 ∨ ((((p1 ∧ True) ∨ p3) → p4) → p5)) ∨ p3) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h15
          -- One of the premise coincides with the conclusion.
          exact h13
        -- We have shown the premise of h6, we can now drive its conclusion.
        let h16 := h6 h14
        -- False on the left can always be used.
        apply False.elim h16
      case inr h17 =>
        -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
        have h18 : ((p3 ∨ ((((p1 ∧ True) ∨ p3) → p4) → p5)) ∨ p3) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h19
          -- One of the premise coincides with the conclusion.
          exact h3
        -- We have shown the premise of h6, we can now drive its conclusion.
        let h20 := h6 h18
        -- False on the left can always be used.
        apply False.elim h20
  case inr h21 =>
    -- Conjunctions on the left can always be decomposed.
    let h22 := h1.left
    let h23 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h23
    case inl h24 =>
      -- We want to use the implication h22 based on <expert-advice>. So we show its premise.
      have h25 : ((p3 ∨ ((((p1 ∧ True) ∨ p3) → p4) → p5)) ∨ p3) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h26
        -- One of the premise coincides with the conclusion.
        exact h21
      -- We have shown the premise of h22, we can now drive its conclusion.
      let h27 := h22 h25
      -- False on the left can always be used.
      apply False.elim h27
    case inr h28 =>
      -- Disjunctions on the left can always be decomposed.
      cases h28
      case inl h29 =>
        -- We want to use the implication h22 based on <expert-advice>. So we show its premise.
        have h30 : ((p3 ∨ ((((p1 ∧ True) ∨ p3) → p4) → p5)) ∨ p3) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h31
          -- One of the premise coincides with the conclusion.
          exact h29
        -- We have shown the premise of h22, we can now drive its conclusion.
        let h32 := h22 h30
        -- False on the left can always be used.
        apply False.elim h32
      case inr h33 =>
        -- We want to use the implication h22 based on <expert-advice>. So we show its premise.
        have h34 : ((p3 ∨ ((((p1 ∧ True) ∨ p3) → p4) → p5)) ∨ p3) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h35
          -- One of the premise coincides with the conclusion.
          exact h21
        -- We have shown the premise of h22, we can now drive its conclusion.
        let h36 := h22 h34
        -- False on the left can always be used.
        apply False.elim h36



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135063225947399859487847674116 : (((((p5 → False) → (False ∧ ((True ∧ p1) ∨ ((p5 → (p2 → False)) ∧ (p4 ∧ (p5 → p1)))))) → p5) ∨ (p3 ∨ True)) ∨ ((False → p2) → p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_680846942229439277160325531004 : ((((((True → p5) ∧ p2) → (((False ∧ p2) → (p5 ∨ p2)) ∨ ((True → ((p3 → p4) → p4)) ∨ False))) → ((True ∧ (False ∧ p2)) ∧ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_650103878474388979153339272523 : (((((p3 ∨ ((((((p4 → True) ∧ (p3 ∨ False)) ∧ p3) ∨ True) → p5) ∨ ((p2 ∨ p1) ∧ p5))) → ((p4 ∨ p1) ∨ True)) ∧ (False → True)) ∨ p2) ∧ True) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
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
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
  -- Implications on the right can always be decomposed.
  intro h10
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2781510569018976627003877253 : (((p3 → (p3 ∨ p2)) → p2) ∨ (((p1 → (((True → p5) → (True → p4)) ∨ ((p1 ∧ p2) ∧ True))) ∨ True) ∨ ((p4 ∨ p4) ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_763602044466869301112824787249 : (((p3 ∧ (p4 ∧ (p1 ∧ ((p2 ∨ (((p3 ∧ False) → p4) ∨ (False → p2))) ∧ (((p5 ∧ True) ∧ (p4 → p1)) ∨ (p4 ∧ (p5 ∧ True))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263681227986119185204653614687 : (True ∧ (((((False ∨ (p1 ∧ ((p5 ∧ p3) ∨ (p2 → (False ∨ p4))))) → (p3 ∨ p2)) ∨ True) ∨ p3) ∨ ((True ∧ p2) → ((False ∨ p3) ∨ False)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198327881552598819850107523501 : ((p2 ∧ (((False ∨ (p3 ∨ False)) ∨ True) ∧ p3)) ∨ ((False → True) ∨ (p1 ∨ ((p2 ∨ p5) ∧ (((True → (p5 ∧ (p3 ∧ p5))) ∧ p2) ∨ p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114117622141477816938620342815 : (((p5 ∨ (((False ∧ ((((p5 → p4) ∨ (True ∧ p1)) ∨ p2) ∨ p2)) ∧ ((False ∨ p3) ∨ p5)) ∨ p5)) ∨ ((p2 ∨ p2) → True)) ∨ (p3 ∧ p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168434017689143500563570856170 : (((p2 ∨ False) → ((((p2 ∧ p3) → p3) ∨ ((True → p5) ∧ p4)) ∧ ((False → p4) → p4))) → ((((p1 ∨ p4) ∨ p5) ∨ (True ∨ False)) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57290602158100630029849788048 : ((((p1 → p4) → p5) ∨ ((p1 → (p3 ∨ p5)) ∨ ((((p2 ∧ ((p2 → (p4 ∧ (True → p3))) → True)) ∧ False) ∧ (p4 → p2)) ∧ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50478329830743146431182197967 : (((p2 → ((p3 ∨ ((True → (p4 ∧ ((((p4 ∨ (True ∨ p3)) ∨ p1) ∨ p4) → p1))) → False)) ∧ p4)) ∨ ((p1 ∨ (p3 ∧ p1)) → p1)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158207545782642613449465703994 : ((((p5 → p2) ∨ p1) ∧ ((p2 → (p5 ∨ False)) ∨ ((p4 ∧ ((p4 ∧ (False ∨ p5)) → True)) ∧ p4))) ∨ (p5 → (p5 → (False → (True ∧ p3))))) := by
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
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114269641807093821272417064672 : ((((p5 ∧ ((p3 → p4) ∧ (True ∧ ((p5 ∧ ((False ∨ p3) ∨ p1)) ∧ (p5 ∨ p4))))) ∧ p4) ∧ (p1 ∨ ((p5 ∧ p3) ∧ False))) ∨ (p2 → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156863109540994445550861642204 : (((((p4 ∧ ((p1 → p5) → ((True ∧ p5) → (True ∧ p3)))) ∧ ((p5 ∧ p3) ∧ p2)) ∧ p3) ∨ True) ∨ ((False → ((p2 ∧ p1) → True)) ∧ True)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_709870116134114498869710423187 : ((((p5 → ((p2 → p4) ∧ (p1 ∨ (p5 → True)))) → ((False ∧ ((p3 ∧ ((((p3 ∧ p5) → p1) ∧ False) ∧ True)) ∧ p1)) ∨ (True → True))) ∨ False) ∧ True) := by
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
theorem thm_5_vars_308360696286089426711961959184 : (p2 ∨ (((p1 ∨ (p5 ∧ ((p4 ∨ p1) ∧ ((((p2 → False) ∨ (p2 ∨ ((False ∨ (p4 ∨ (p2 → p4))) → True))) ∧ True) ∨ False)))) ∧ p5) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157971863101178856005183360071 : (((p4 ∧ ((p2 ∨ (p3 ∨ (p5 ∨ p4))) ∧ False)) ∨ ((p5 ∧ p2) ∨ ((p2 → p3) ∨ (p4 ∨ True)))) ∨ (p5 → (((p5 ∧ p2) → True) ∧ p2))) := by
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
theorem thm_5_vars_60749137955139672497371239201 : ((True ∧ (((True ∨ p4) ∨ True) → (((p3 → p5) ∧ p1) → (((p4 ∨ p3) ∨ p5) ∧ (p3 → ((((p4 → p1) → p5) ∧ False) ∧ False)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244638734603989099050120056088 : ((False ∧ p5) ∨ (((p3 ∨ (((p5 ∧ p2) ∧ p4) ∧ p2)) ∧ p2) ∨ (((((True ∨ p5) → p5) ∨ False) ∧ p3) ∨ (((False ∧ p4) ∨ p1) ∨ True)))) := by
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
theorem thm_5_vars_260251666265056810200804840976 : ((p2 → p3) → (((p5 ∧ p1) ∨ False) ∨ ((True ∧ ((p2 ∧ (True → ((p5 ∧ (False ∨ p5)) ∧ (p1 → True)))) → (p2 → p4))) ∨ (False → p5)))) := by
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
theorem thm_5_vars_563598823139786331602675842410 : (((p5 ∨ ((p5 ∨ True) → (((True → False) → (((p5 → p5) ∧ (((True ∧ p1) ∨ p3) ∧ p1)) ∨ (p5 ∧ (False ∨ p3)))) ∧ (False → p4)))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Implications on the right can always be decomposed.
  intro h9
  -- False on the left can always be used.
  apply False.elim h9
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66615537771189617122255552335 : ((True → (((((p4 ∧ (((True ∨ p2) → p4) ∧ True)) ∧ p5) ∨ (p2 ∧ (p5 ∨ p5))) → p2) ∧ (p1 ∨ ((p1 ∨ (p2 ∨ False)) ∧ p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166459305841402173574568287504 : ((p2 ∨ ((False ∧ p1) ∨ ((((p5 → True) ∧ (p4 ∨ False)) → (p2 ∨ (False ∨ p1))) ∨ p4))) ∨ ((((p1 ∧ p1) ∨ p2) ∧ False) → (p1 ∨ p5))) := by
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
    -- False on the left can always be used.
    apply False.elim h3
  case inr h7 =>
    -- False on the left can always be used.
    apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172894790671397604637052413366 : ((p2 ∧ (((p4 → ((p3 ∨ (p3 ∧ p1)) ∨ ((True ∨ p4) ∧ p1))) ∧ p2) ∧ False)) ∨ (p2 → ((p3 ∨ (p4 ∧ (p4 ∧ p2))) → (True ∧ p2)))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_763882197953015506426848611062 : (((p3 ∧ (p4 ∨ (p3 ∨ (((p5 ∧ (((p2 ∨ True) → (True ∨ (p4 ∨ (p3 → p3)))) ∧ ((p3 → p2) ∧ False))) ∧ True) ∨ (p2 → False))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313558650754143610487569862084 : (p3 ∨ (((((p1 ∨ (p1 ∨ (p3 ∨ (p5 → ((False ∨ (p3 ∧ p3)) → p5))))) → False) ∧ True) ∧ ((True ∧ ((p4 ∨ p3) ∨ p3)) ∨ False)) → False)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
        have h11 : (p1 ∨ (p1 ∨ (p3 ∨ (p5 → ((False ∨ (p3 ∧ p3)) → p5))))) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h12
          -- Implications on the right can always be decomposed.
          intro h13
          -- Disjunctions on the left can always be decomposed.
          cases h13
          case inl h14 =>
            -- False on the left can always be used.
            apply False.elim h14
          case inr h15 =>
            -- Conjunctions on the left can always be decomposed.
            let h16 := h15.left
            let h17 := h15.right
            -- One of the premise coincides with the conclusion.
            exact h12
        -- We have shown the premise of h4, we can now drive its conclusion.
        let h18 := h4 h11
        -- False on the left can always be used.
        apply False.elim h18
      case inr h19 =>
        -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
        have h20 : (p1 ∨ (p1 ∨ (p3 ∨ (p5 → ((False ∨ (p3 ∧ p3)) → p5))))) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h19
        -- We have shown the premise of h4, we can now drive its conclusion.
        let h21 := h4 h20
        -- False on the left can always be used.
        apply False.elim h21
    case inr h22 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h23 : (p1 ∨ (p1 ∨ (p3 ∨ (p5 → ((False ∨ (p3 ∧ p3)) → p5))))) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h22
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h24 := h4 h23
      -- False on the left can always be used.
      apply False.elim h24
  case inr h25 =>
    -- False on the left can always be used.
    apply False.elim h25



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207654655213008310824700553398 : ((((p5 → False) ∧ (p4 ∨ p5)) → True) → ((((p5 → True) ∧ (((((p2 → p4) ∨ p1) ∨ (p2 ∧ (p3 → p5))) ∨ p5) ∧ True)) ∨ True) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346452911397195066018588481714 : (p3 → (((((p5 ∨ (p1 → (p4 ∧ p4))) ∨ (p5 ∧ (p2 ∨ p2))) ∨ True) ∧ (p4 ∨ ((True ∧ ((p5 ∨ p3) → p5)) → False))) → (p1 ∨ True))) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Disjunctions on the left can always be decomposed.
        cases h4
        case inl h8 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h9 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h10 =>
        -- Disjunctions on the left can always be decomposed.
        cases h4
        case inl h11 =>
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
      -- Conjunctions on the left can always be decomposed.
      let h14 := h13.left
      let h15 := h13.right
      -- Disjunctions on the left can always be decomposed.
      cases h15
      case inl h16 =>
        -- Disjunctions on the left can always be decomposed.
        cases h4
        case inl h17 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h18 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h19 =>
        -- Disjunctions on the left can always be decomposed.
        cases h4
        case inl h20 =>
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
    cases h4
    case inl h23 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h24 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256909208128089932665041575553 : ((p1 ∨ p4) → ((((True ∧ p3) → False) ∧ p1) ∨ (p1 ∨ (p1 ∨ ((p1 ∨ ((p3 ∧ p3) → ((True → ((p1 ∨ p2) → p3)) ∨ p3))) ∧ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
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
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h6
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113710734385252066393260155149 : (((((False → (p2 → ((p4 ∨ ((p1 → (False ∧ p4)) ∧ (False → (p5 ∧ p3)))) ∨ True))) ∧ p5) ∨ (p4 → p3)) → (p2 ∨ p2)) ∨ (p3 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112163250601253250672167109776 : (((p3 ∧ ((((p1 ∨ p1) → (((p3 ∨ p5) → True) ∧ p2)) → (((True ∧ (p1 ∧ False)) ∨ (True ∧ p1)) → p3)) ∨ True)) ∨ p1) ∨ (False → False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119135957290199540208328557565 : ((p1 → (p3 ∨ (((p3 ∧ True) ∨ p5) ∧ (((p1 ∧ (p3 → (p3 ∧ True))) ∧ ((False → (p4 ∧ (p2 ∨ False))) ∨ p2)) → False)))) ∨ (p1 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199459835334213177423849713072 : (((p5 ∧ (p3 ∨ (p4 ∧ (p1 → p3)))) ∨ p1) → ((True → False) → (((p5 ∧ ((p2 ∨ p2) → p4)) ∨ p3) ∨ ((p3 ∧ (False ∨ p2)) ∨ p4)))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h8
  case inr h10 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h11 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h12 := h2 h11
    -- False on the left can always be used.
    apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179729902117743581453801467050 : ((((p2 ∧ (p4 ∨ ((p2 ∧ (p2 → False)) → (p1 → p1)))) → p5) ∧ p1) → ((((False ∧ (False ∧ p2)) → p5) → p2) → (p5 ∧ (p3 ∨ p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h5 : ((False ∧ (False ∧ p2)) → p5) := by
    -- Implications on the right can always be decomposed.
    intro h6
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- False on the left can always be used.
    apply False.elim h7
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h9 := h2 h5
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h10 : (p2 ∧ (p4 ∨ ((p2 ∧ (p2 → False)) → (p1 → p1)))) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h9
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h11
    -- Implications on the right can always be decomposed.
    intro h12
    -- Conjunctions on the left can always be decomposed.
    let h13 := h11.left
    let h14 := h11.right
    -- One of the premise coincides with the conclusion.
    exact h12
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h15 := h3 h10
  -- One of the premise coincides with the conclusion.
  exact h15
  -- Conjunctions on the left can always be decomposed.
  let h16 := h1.left
  let h17 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h18 : ((False ∧ (False ∧ p2)) → p5) := by
    -- Implications on the right can always be decomposed.
    intro h19
    -- Conjunctions on the left can always be decomposed.
    let h20 := h19.left
    let h21 := h19.right
    -- False on the left can always be used.
    apply False.elim h20
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h22 := h2 h18
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h22



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_389918097559079436073579765591 : (((((((True ∨ (p1 ∧ False)) ∧ (False → p5)) ∨ (p2 ∨ (True ∧ p1))) → (((p4 ∧ (False ∨ p3)) ∨ p1) → (p1 ∧ (p3 ∧ p4)))) ∨ True) ∧ True) ∧ True) := by
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
theorem thm_5_vars_621273221081456513939608901396 : ((((True ∧ ((p1 ∨ (((((p5 ∨ (True ∨ p2)) ∧ ((True → p4) ∧ p5)) ∨ p3) ∧ True) ∧ p4)) ∧ (((True ∧ p3) ∧ p4) → True))) ∨ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227165399526474969454757143126 : (((p5 ∨ p4) → p1) ∨ ((((p1 → p2) ∧ True) ∨ (p5 → (((p1 ∧ p4) ∧ False) ∨ ((((True ∧ p4) ∨ (False ∨ p1)) → p4) ∨ True)))) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114099121032610707872431456399 : (((p1 ∧ (p1 ∧ ((((((p1 ∧ p5) → True) ∨ p1) → ((p4 ∨ p2) ∧ (p1 → True))) → p5) ∨ p1))) ∨ (True ∨ (p3 → p4))) ∨ (p4 ∨ p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184501945763752595318920769616 : ((((p3 ∧ p3) ∧ ((p2 ∨ (p4 ∨ False)) ∧ p1)) ∨ (True ∧ False)) ∨ (((p3 ∧ (p3 → (((p1 → False) ∨ (p5 → p5)) ∨ p2))) → p5) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_612649317104229736973105319093 : (((((((((((p1 ∧ True) ∧ p2) ∨ False) ∨ (False → p5)) ∧ False) ∧ ((True ∨ p3) → p1)) ∨ ((p3 ∧ True) → True)) ∨ (p5 ∨ p1)) ∨ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191109474654088209470431951612 : (((p3 ∧ (True ∨ p5)) ∧ (((p3 ∨ False) ∨ p4) → p1)) ∨ ((p1 ∧ p2) → (((((((p5 → p3) ∨ False) ∨ p5) ∧ p2) ∨ p4) → p3) ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_777957168861378179603536524022 : (((p1 ∨ (((p5 → True) → p1) ∨ (p1 ∨ (((False ∧ p5) → (p3 ∨ (((p5 ∧ False) ∧ ((p5 → p1) → p5)) ∨ (p4 → p4)))) ∨ True)))) ∨ p2) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115317575300464156864167326403 : (((((p2 ∧ p3) → p4) ∧ ((True → (p3 ∨ p2)) → p2)) → ((p2 ∨ p5) ∧ (((((p2 → False) → True) ∧ False) ∧ False) ∨ p5))) ∨ (True → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321075971497956463426134202692 : (p4 ∨ (p1 ∨ ((False → (True → (p5 ∨ (False ∧ False)))) ∧ ((((((p3 ∧ True) → p4) → ((True ∨ p3) ∧ p4)) ∨ p3) ∨ (True → p2)) ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305064580096557354516846500190 : (p1 ∨ (((True ∨ (((p4 ∧ (p4 → p4)) → (((True ∨ p4) → p1) ∧ ((False → p5) ∨ p4))) → p1)) → (p2 ∧ p1)) → ((p2 ∨ p4) → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h4 : (True ∨ (((p4 ∧ (p4 → p4)) → (((True ∨ p4) → p1) ∧ ((False → p5) ∨ p4))) → p1)) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h5 := h1 h4
    -- We need to get the right conjuct of h5 based on <expert-advice>.
    let h6 := h5.right
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h8 : (True ∨ (((p4 ∧ (p4 → p4)) → (((True ∨ p4) → p1) ∧ ((False → p5) ∨ p4))) → p1)) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h9 := h1 h8
    -- We need to get the right conjuct of h9 based on <expert-advice>.
    let h10 := h9.right
    -- One of the premise coincides with the conclusion.
    exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314849721561986319134692456175 : (p3 ∨ ((p2 → ((((p5 ∧ p2) ∨ (p4 ∧ True)) ∧ True) ∧ (p3 ∨ p3))) ∨ ((p3 ∨ p5) → (((p5 → False) ∨ p3) ∨ ((p4 ∧ p4) → p5))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319754197440218944784442629542 : (p4 ∨ ((p1 ∧ (p4 ∨ (p5 ∧ (False ∨ p5)))) ∨ (False → ((p4 → (p4 ∧ (True ∧ (((True → True) ∨ p4) ∧ p3)))) ∨ (p3 ∧ (False ∧ p1)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60900570729440065802374363734 : ((True ∧ (p5 → (((p3 → (((p4 ∧ (p5 ∨ (p4 ∨ p4))) ∧ ((((p3 ∧ p5) → True) → p3) ∨ p2)) ∧ (p3 ∨ p2))) ∧ p4) → False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64678828163355447154537386314 : ((p1 ∨ (p3 ∨ ((p5 ∨ True) → ((p2 → (p5 ∨ ((p5 ∨ p4) ∨ (p4 ∨ True)))) ∨ (((p2 ∨ (p5 ∨ True)) ∨ (p3 ∨ False)) → p4))))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55093246122090916712278122730 : (((p2 → (False → ((True ∨ False) ∧ True))) ∧ (((p2 → False) → (p2 ∨ ((p2 → (False ∨ False)) ∧ p1))) ∨ ((p3 ∧ (p2 ∨ p3)) → True))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166332809930368742773703193024 : ((p5 ∧ (p2 ∧ ((p2 ∧ (p5 ∨ (p3 → (((p4 → (True ∧ True)) ∨ p2) ∨ True)))) → p1))) ∨ (((False ∨ True) ∨ (p5 ∨ (p4 ∧ p3))) ∨ p1)) := by
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
theorem thm_5_vars_44481443256542301970966439483 : ((((False ∨ ((p1 ∧ (p4 → (p2 → True))) ∧ ((p5 ∨ p3) → p1))) → ((p2 ∨ (p2 ∧ p2)) ∨ (p5 ∧ (False ∨ (p3 → p3))))) → p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39680937309588001628368796587 : (((p4 ∨ (((((p4 → ((((p1 → True) → (False ∨ p1)) ∧ p5) → False)) ∧ True) → p5) → (p2 ∧ (p1 → False))) → (True → False))) ∧ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43436427133094387724334808176 : (((((p1 ∨ (True ∧ (False ∧ True))) → (p4 → ((((True ∧ ((p3 ∨ p2) → p1)) → (p4 → p4)) → p1) ∧ (True → p5)))) ∨ p3) → p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179437186258782316793845036237 : ((p4 ∨ (p3 → (((p2 ∨ ((False ∧ p1) ∨ p5)) ∨ p5) ∨ (p3 ∧ False)))) ∨ ((p4 ∧ p1) → (p4 ∨ ((((p2 ∨ p5) ∧ p1) ∧ p3) → p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_85446607690064646384410570334 : (((False ∨ ((((True → (True ∧ (p2 ∨ p5))) → p1) → p2) ∧ p1)) ∧ (((False → True) → (p2 ∨ p2)) → ((p3 ∧ p4) ∧ (p2 ∧ False)))) → p3) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h8 : ((False → True) → (p2 ∨ p2)) := by
      -- Implications on the right can always be decomposed.
      intro h9
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h10 : ((True → (True ∧ (p2 ∨ p5))) → p1) := by
        -- Implications on the right can always be decomposed.
        intro h11
        -- One of the premise coincides with the conclusion.
        exact h7
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h12 := h6 h10
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h12
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h13 := h3 h8
    -- We need to get the left conjuct of h13 based on <expert-advice>.
    let h14 := h13.left
    -- We need to get the left conjuct of h14 based on <expert-advice>.
    let h15 := h14.left
    -- One of the premise coincides with the conclusion.
    exact h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307532099415115892476772068652 : (p1 ∨ (True → (p5 ∨ (p5 → (p2 → (False ∨ ((False ∧ (True ∨ (p3 ∨ p5))) ∨ ((p1 ∨ True) ∧ ((p1 ∨ ((p4 ∧ p4) → p2)) → True))))))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179311842502805240683336182121 : ((False ∨ ((p2 ∨ p5) → ((((p2 → p3) ∧ p5) ∧ False) ∧ (p5 ∨ p2)))) ∨ ((True ∧ True) ∨ (p3 ∨ (True → ((p1 ∨ p1) ∨ (p4 → p1)))))) := by
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
theorem thm_5_vars_758331951214170643008799145731 : (((p2 ∧ ((((p4 ∨ ((p2 → p4) → p1)) ∨ ((p3 ∧ ((p5 → ((False ∨ (p5 ∧ p2)) ∧ True)) ∨ p4)) ∨ p2)) ∧ (True ∨ p4)) ∧ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_348146904154656807478103208365 : (p3 → ((p4 ∧ p2) → ((True ∧ (((((p5 ∨ (p4 ∧ True)) ∨ p2) ∧ ((False ∨ (p5 ∧ p1)) → False)) → (False ∧ p5)) ∨ p1)) ∨ (p2 ∨ p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148885319535740260916794228806 : ((((False ∧ False) ∧ (True ∧ True)) ∨ ((p5 ∨ p5) ∨ (((p4 ∧ p2) → (p1 ∧ (True → (p5 ∨ p3)))) ∨ p1))) ∨ ((False ∧ (p2 ∧ p2)) → p4)) := by
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
theorem thm_5_vars_49881381450112265473898650424 : (((((p2 ∨ (((p1 → p1) ∧ (((p5 → (True ∨ p5)) ∨ p1) → p1)) ∨ (p2 ∧ True))) → p3) ∨ p3) ∧ ((p4 ∧ (False ∨ p4)) ∨ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43500262371530089273113956207 : ((((True ∨ (p3 ∨ (((p4 ∨ (p4 ∧ ((False → p2) ∧ (p1 → (p4 ∨ p4))))) ∨ (p4 → p4)) ∨ ((True ∨ False) ∨ p5)))) ∨ p4) → p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347824531738745195707459090902 : (p3 → (((p5 → p1) ∧ p5) → (((True ∧ (p3 ∧ (p2 → (False ∧ p1)))) ∧ (((p3 → (p3 ∧ (p5 ∧ p2))) ∧ (p2 ∨ p1)) ∧ p5)) → p4))) := by
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
  let h8 := h7.left
  let h9 := h7.right
  -- Conjunctions on the left can always be decomposed.
  let h10 := h5.left
  let h11 := h5.right
  -- Conjunctions on the left can always be decomposed.
  let h12 := h10.left
  let h13 := h10.right
  -- Disjunctions on the left can always be decomposed.
  cases h13
  case inl h14 =>
    -- Conjunctions on the left can always be decomposed.
    let h15 := h2.left
    let h16 := h2.right
    -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
    have h17 : p2 := by
      -- One of the premise coincides with the conclusion.
      exact h14
    -- We have shown the premise of h9, we can now drive its conclusion.
    let h18 := h9 h17
    -- We need to get the left conjuct of h18 based on <expert-advice>.
    let h19 := h18.left
    -- False on the left can always be used.
    apply False.elim h19
  case inr h20 =>
    -- Conjunctions on the left can always be decomposed.
    let h21 := h2.left
    let h22 := h2.right
    -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
    have h23 : p3 := by
      -- One of the premise coincides with the conclusion.
      exact h1
    -- We have shown the premise of h12, we can now drive its conclusion.
    let h24 := h12 h23
    -- We need to get the right conjuct of h24 based on <expert-advice>.
    let h25 := h24.right
    -- We need to get the right conjuct of h25 based on <expert-advice>.
    let h26 := h25.right
    -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
    have h27 : p2 := by
      -- One of the premise coincides with the conclusion.
      exact h26
    -- We have shown the premise of h9, we can now drive its conclusion.
    let h28 := h9 h27
    -- We need to get the left conjuct of h28 based on <expert-advice>.
    let h29 := h28.left
    -- False on the left can always be used.
    apply False.elim h29



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230761168037354221850165188039 : (((True ∧ True) ∨ p4) → ((((((p1 ∧ p3) ∧ p2) ∨ (p1 ∨ p1)) ∧ (p1 ∨ True)) → (p4 ∨ ((True → True) ∨ p4))) ∨ ((p5 ∧ p5) ∨ True))) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133895043835266917766783390495 : (((False ∨ (((p4 → (True ∨ (False ∨ (p2 → p2)))) → True) → (p3 → ((False ∨ ((p4 → p2) ∨ p5)) ∧ p4)))) ∧ True) ∨ (p4 ∨ (p2 → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245840180767955053049207229594 : ((p3 ∧ p4) ∨ ((((p1 ∧ (p1 ∧ False)) → (((((p1 ∨ p5) ∨ (True ∨ p5)) → p2) → (p5 ∨ p2)) ∨ p5)) → (p4 ∧ p4)) ∨ (False → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



