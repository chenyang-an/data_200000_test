variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_685893926429025289569517571361 : (((((p4 ∨ ((((((True ∧ False) → True) → ((p2 ∨ p1) ∨ p4)) → True) ∨ p2) ∧ p4)) → p2) → ((True → ((p2 → p1) ∧ p5)) ∨ True)) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38792246780093776801119191785 : ((((p4 ∧ ((False → p4) ∧ p3)) ∨ (((False → (((p2 ∧ p3) → (p1 ∧ ((True → False) → p2))) ∧ p2)) ∧ p5) → (p2 ∧ p5))) ∧ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260439121227608956236255578185 : ((p3 → True) → ((True ∨ True) → ((((True ∧ (False ∧ p4)) ∧ p3) ∧ (p5 → (p4 → p1))) ∨ ((False → ((p2 → False) ∧ (p2 ∨ p4))) ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_901476561409068858898710255559 : ((((((True ∨ (p3 ∨ (((p5 ∨ False) → (True ∧ (p5 ∨ True))) → True))) → (p1 ∧ (p2 ∨ p4))) ∧ p1) ∧ (((True → p3) → p3) ∨ p5)) → p1) ∧ True) := by
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
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h7 =>
    -- One of the premise coincides with the conclusion.
    exact h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56604064125522293570034535075 : (((p4 → (p4 ∨ (p2 → True))) → (((p2 → (p3 ∧ (p5 ∧ (p3 ∨ True)))) ∧ p2) ∨ ((False ∧ p4) ∧ (p5 → (p3 → (p1 → p1)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_226126943319575724048813177511 : (((False ∨ p1) ∨ p3) ∨ ((((p3 ∨ (((p4 ∨ (False ∧ p1)) ∧ p4) → (p2 ∧ p1))) ∧ (p3 ∧ p2)) ∨ False) ∨ (False → (p5 ∧ (p3 → p5))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_621152458466263605521673692673 : (((((p5 → p4) → ((((p1 ∨ (p2 ∨ ((p5 → p5) → p3))) ∧ (p2 ∧ (p1 → True))) ∨ (p1 ∨ (False ∧ (True ∨ p5)))) ∨ p1)) ∨ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315663582378726647346156598308 : (p3 ∨ ((p3 ∧ p4) ∨ ((False → (((True ∨ p5) ∨ p4) ∨ (p4 ∧ (((p4 → p2) → p5) ∧ p2)))) → ((p2 ∧ (p5 ∨ p1)) ∨ (False → p4))))) := by
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
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133647874826952092870551264920 : (((((True ∧ (p3 ∧ (True ∧ p4))) → (p3 → (((p2 ∧ (p1 → True)) ∧ True) ∨ (p5 ∧ False)))) ∧ (p1 → True)) ∧ p3) ∨ ((p3 ∨ True) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173112446768605906362694188353 : ((p2 ∨ (((p2 ∨ p1) ∨ ((False ∨ (False → (p2 → p4))) ∧ (p1 ∨ p2))) → p2)) ∨ (((((p1 → False) → p2) ∨ (p4 → p4)) → p1) → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p1 → False) → p2) ∨ (p4 → p4)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_734306604464491999998554264194 : ((((False ∨ p2) ∧ (((p2 ∧ False) → (((p2 ∧ p3) ∧ (p2 ∨ p3)) → p3)) ∧ ((True ∧ ((((p5 ∧ p2) ∨ p1) → p2) ∨ p4)) → p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_765089263701449397850170148187 : (((p4 ∧ ((p3 ∧ (p2 → ((p2 ∨ (((p1 ∨ p5) ∧ (p1 → False)) ∧ True)) → (p4 ∨ (p3 → ((p1 → p4) ∨ p5)))))) ∧ (True → p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60078177301282478692618422802 : (((p2 ∨ p4) → ((True ∨ (p4 ∨ ((True → p3) ∨ p4))) ∧ ((p5 ∧ ((False ∧ True) → p4)) → (p3 ∨ (((p4 → p2) ∧ p2) ∧ p4))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159960723923230005679521532519 : (((((p1 ∧ (True ∧ ((p1 ∨ ((p3 ∨ p5) ∨ p1)) ∨ False))) ∨ True) ∧ (p3 → (p3 ∨ p1))) → p2) → (p4 → (p2 → (p1 ∨ (p1 ∨ p2))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67971275031240229233665975918 : ((p2 → (((p2 → p4) → p1) ∨ (((False ∧ ((p5 ∨ (True ∨ (p3 ∧ (p3 ∨ (p5 ∨ (p3 ∨ p5)))))) → (p1 ∧ p5))) ∨ True) ∧ p2))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_686318865446671990159794637456 : (((((p1 ∨ (((True ∨ False) → True) → False)) ∧ (p1 ∨ (p2 ∨ ((p2 ∨ (p2 ∨ True)) → False)))) → ((False ∧ p4) ∨ (False → (p5 ∧ p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_70842215399216699003605933129 : ((((((p2 ∨ p4) ∨ (p5 ∧ True)) ∧ ((False → (p1 → p3)) → p4)) ∧ (p2 ∧ ((False ∨ ((p1 ∧ (p4 ∨ p3)) ∨ True)) ∨ p2))) ∧ p5) → p4) := by
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
  cases h6
  case inl h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h5.left
      let h11 := h5.right
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- Disjunctions on the left can always be decomposed.
        cases h12
        case inl h13 =>
          -- False on the left can always be used.
          apply False.elim h13
        case inr h14 =>
          -- Disjunctions on the left can always be decomposed.
          cases h14
          case inl h15 =>
            -- Conjunctions on the left can always be decomposed.
            let h16 := h15.left
            let h17 := h15.right
            -- Disjunctions on the left can always be decomposed.
            cases h17
            case inl h18 =>
              -- One of the premise coincides with the conclusion.
              exact h18
            case inr h19 =>
              -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
              have h20 : (False → (p1 → p3)) := by
                -- Implications on the right can always be decomposed.
                intro h21
                -- Implications on the right can always be decomposed.
                intro h22
                -- False on the left can always be used.
                apply False.elim h21
              -- We have shown the premise of h7, we can now drive its conclusion.
              let h23 := h7 h20
              -- One of the premise coincides with the conclusion.
              exact h23
          case inr h24 =>
            -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
            have h25 : (False → (p1 → p3)) := by
              -- Implications on the right can always be decomposed.
              intro h26
              -- Implications on the right can always be decomposed.
              intro h27
              -- False on the left can always be used.
              apply False.elim h26
            -- We have shown the premise of h7, we can now drive its conclusion.
            let h28 := h7 h25
            -- One of the premise coincides with the conclusion.
            exact h28
      case inr h29 =>
        -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
        have h30 : (False → (p1 → p3)) := by
          -- Implications on the right can always be decomposed.
          intro h31
          -- Implications on the right can always be decomposed.
          intro h32
          -- False on the left can always be used.
          apply False.elim h31
        -- We have shown the premise of h7, we can now drive its conclusion.
        let h33 := h7 h30
        -- One of the premise coincides with the conclusion.
        exact h33
    case inr h34 =>
      -- Conjunctions on the left can always be decomposed.
      let h35 := h5.left
      let h36 := h5.right
      -- Disjunctions on the left can always be decomposed.
      cases h36
      case inl h37 =>
        -- Disjunctions on the left can always be decomposed.
        cases h37
        case inl h38 =>
          -- False on the left can always be used.
          apply False.elim h38
        case inr h39 =>
          -- Disjunctions on the left can always be decomposed.
          cases h39
          case inl h40 =>
            -- Conjunctions on the left can always be decomposed.
            let h41 := h40.left
            let h42 := h40.right
            -- Disjunctions on the left can always be decomposed.
            cases h42
            case inl h43 =>
              -- One of the premise coincides with the conclusion.
              exact h43
            case inr h44 =>
              -- One of the premise coincides with the conclusion.
              exact h34
          case inr h45 =>
            -- One of the premise coincides with the conclusion.
            exact h34
      case inr h46 =>
        -- One of the premise coincides with the conclusion.
        exact h34
  case inr h47 =>
    -- Conjunctions on the left can always be decomposed.
    let h48 := h47.left
    let h49 := h47.right
    -- Conjunctions on the left can always be decomposed.
    let h50 := h5.left
    let h51 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h51
    case inl h52 =>
      -- Disjunctions on the left can always be decomposed.
      cases h52
      case inl h53 =>
        -- False on the left can always be used.
        apply False.elim h53
      case inr h54 =>
        -- Disjunctions on the left can always be decomposed.
        cases h54
        case inl h55 =>
          -- Conjunctions on the left can always be decomposed.
          let h56 := h55.left
          let h57 := h55.right
          -- Disjunctions on the left can always be decomposed.
          cases h57
          case inl h58 =>
            -- One of the premise coincides with the conclusion.
            exact h58
          case inr h59 =>
            -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
            have h60 : (False → (p1 → p3)) := by
              -- Implications on the right can always be decomposed.
              intro h61
              -- Implications on the right can always be decomposed.
              intro h62
              -- False on the left can always be used.
              apply False.elim h61
            -- We have shown the premise of h7, we can now drive its conclusion.
            let h63 := h7 h60
            -- One of the premise coincides with the conclusion.
            exact h63
        case inr h64 =>
          -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
          have h65 : (False → (p1 → p3)) := by
            -- Implications on the right can always be decomposed.
            intro h66
            -- Implications on the right can always be decomposed.
            intro h67
            -- False on the left can always be used.
            apply False.elim h66
          -- We have shown the premise of h7, we can now drive its conclusion.
          let h68 := h7 h65
          -- One of the premise coincides with the conclusion.
          exact h68
    case inr h69 =>
      -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
      have h70 : (False → (p1 → p3)) := by
        -- Implications on the right can always be decomposed.
        intro h71
        -- Implications on the right can always be decomposed.
        intro h72
        -- False on the left can always be used.
        apply False.elim h71
      -- We have shown the premise of h7, we can now drive its conclusion.
      let h73 := h7 h70
      -- One of the premise coincides with the conclusion.
      exact h73



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_702510066801222332329478695068 : (((((((p1 → p2) → ((p1 ∧ True) ∧ False)) ∨ p3) → False) ∨ (p5 → (p2 ∨ ((p1 ∧ p5) ∨ (p3 ∨ (((p2 → True) → False) → False)))))) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (p2 → True) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h3
  -- False on the left can always be used.
  apply False.elim h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178966804104074111709967833664 : (((p3 ∨ p3) ∨ ((False ∨ (p5 ∧ (True ∨ (True → (p2 ∨ p3))))) ∨ p5)) ∨ (False → ((((p4 ∧ p4) ∧ p5) → p4) → ((p1 ∨ p1) ∧ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_207945813650898346644450663050 : (((p1 → (p3 ∧ p3)) ∧ (p4 ∨ p1)) → ((True ∧ ((((False ∧ (True ∨ p3)) ∧ (p5 → p4)) → p2) ∧ (p5 → (True → p5)))) → (p2 ∨ True))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h7 := h1.left
  let h8 := h1.right
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207704836001233947112503771792 : (((True ∧ (p2 → (p4 → p4))) → False) → ((p4 → (p3 ∧ p5)) ∧ ((((p4 → (p4 ∨ ((p2 ∨ p5) ∧ p2))) ∨ p3) → (p4 ∨ False)) ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : (True ∧ (p2 → (p4 → p4))) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h3
  -- False on the left can always be used.
  apply False.elim h6
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h7 : (True ∧ (p2 → (p4 → p4))) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Implications on the right can always be decomposed.
    intro h8
    -- Implications on the right can always be decomposed.
    intro h9
    -- One of the premise coincides with the conclusion.
    exact h9
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h10 := h1 h7
  -- False on the left can always be used.
  apply False.elim h10
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h11 : (True ∧ (p2 → (p4 → p4))) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Implications on the right can always be decomposed.
    intro h12
    -- Implications on the right can always be decomposed.
    intro h13
    -- One of the premise coincides with the conclusion.
    exact h13
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h14 := h1 h11
  -- False on the left can always be used.
  apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42284072489165050709450607687 : (((p1 ∧ (p3 ∨ (p2 ∧ (False ∧ (((p4 → (p1 ∨ False)) ∨ (False → p1)) → ((False ∨ (True ∨ (p1 ∨ p4))) ∨ (p2 → p4))))))) ∨ True) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_327071893232051869580242916862 : (True → ((((p5 ∨ (p4 ∨ True)) → p2) → (((True → (p2 ∧ (p5 → ((p3 ∨ (p2 ∨ p2)) ∨ p1)))) ∨ (p3 ∧ (p2 → True))) ∧ p2)) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (p5 ∨ (p4 ∨ True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- One of the premise coincides with the conclusion.
  exact h5
  -- Implications on the right can always be decomposed.
  intro h6
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h7 : (p5 ∨ (p4 ∨ True)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h6
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h8 := h2 h7
  -- One of the premise coincides with the conclusion.
  exact h8
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h9 : (p5 ∨ (p4 ∨ True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h10 := h2 h9
  -- One of the premise coincides with the conclusion.
  exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158615146983086527260038550150 : ((False ∧ ((p4 ∨ p5) ∧ ((False ∧ (p5 ∨ (p4 → (False ∨ True)))) ∨ (((p1 ∧ True) ∨ p1) ∧ False)))) ∨ ((p5 → (p3 ∨ (p2 → True))) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_170137730753004992185717637722 : (((False ∧ (p1 ∨ ((p4 ∧ p4) ∨ (False ∨ p3)))) ∨ (p4 ∨ (p1 ∨ (False ∨ True)))) ∧ ((p4 ∨ ((True ∨ p5) ∨ ((True ∨ p2) ∨ p1))) ∨ p5)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_157679657931093628578050793127 : (((True ∧ (((p2 → False) → (True ∨ p3)) → (False ∨ ((False → True) → p5)))) ∨ (p3 → (False ∨ True))) ∨ ((((p2 ∧ p1) ∧ p2) ∨ True) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166635229865541718078492499378 : ((p1 → ((True ∧ ((((p2 ∧ (p1 ∧ p1)) ∨ p3) ∧ ((p5 → p5) ∧ p2)) ∨ p5)) ∧ p3)) ∨ ((False → ((p1 ∧ p4) ∧ True)) ∨ (p4 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_747386674101998984337965788884 : ((((p5 ∨ p5) → (p4 ∧ (p1 ∧ (False ∨ (((p5 → (p3 ∧ (p2 ∨ (p5 → ((p4 ∧ p3) ∨ True))))) ∧ False) ∨ ((p3 ∨ p5) → p5)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49908451159237160362089964670 : ((((((((p4 → p2) ∨ (p2 ∨ p3)) ∧ True) ∨ ((False → p1) ∧ ((True ∨ p3) ∧ False))) ∨ p3) → False) ∧ ((p1 ∧ (False → p5)) ∧ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134626292578678315788134334132 : (((((((p5 ∨ p1) ∧ (((p2 ∧ p4) ∨ p3) ∧ p3)) ∧ (p5 ∨ p5)) ∨ p4) ∧ ((p4 ∨ p1) → (p4 → True))) → False) ∨ (p1 → (p2 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319869955236539564716465423267 : (p4 ∨ (((p1 ∨ p3) ∧ (p1 ∨ p2)) ∨ ((True ∧ ((True → (p4 → ((False → (p3 ∨ (p5 → (False → p1)))) ∧ p1))) ∧ (p2 ∧ False))) → p1))) := by
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
  let h6 := h5.left
  let h7 := h5.right
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157452665940747776423419509278 : (((((p2 ∧ (((True ∨ (p3 ∧ (p3 ∨ p3))) ∨ False) ∧ (p4 ∨ p2))) ∧ p4) ∧ False) ∨ (p5 ∧ p1)) ∨ (p3 ∨ ((p2 ∧ p4) → (p1 → True)))) := by
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
theorem thm_5_vars_206935382980718557609919763155 : ((((p5 → (p1 ∨ p2)) ∨ True) ∧ p4) → (p4 ∧ (p4 → ((False ∨ p3) ∨ (p3 ∨ ((True ∨ False) ∨ ((p5 ∧ False) ∧ (False ∨ (p2 ∨ True))))))))) := by
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
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  -- Implications on the right can always be decomposed.
  intro h6
  -- Conjunctions on the left can always be decomposed.
  let h7 := h1.left
  let h8 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h9 =>
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
  case inr h10 =>
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
theorem thm_5_vars_127801715758685153805514473875 : ((True → ((False → False) ∧ (p5 ∧ (((p4 ∧ ((p5 ∨ False) ∧ True)) → (((((p2 → p1) ∨ p3) ∨ p4) ∧ False) → p2)) ∧ False)))) → (True → p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148702716815074523180473469064 : (((((((p1 → p2) ∨ p2) ∨ p2) → p5) ∨ True) → (p3 ∧ (((p4 ∧ (p1 ∧ (p1 → p2))) ∨ p3) ∧ p5))) ∨ ((False → p4) ∨ (p1 ∧ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178498070249000719834957360249 : (((p4 ∧ ((True ∧ ((True ∨ p2) → False)) ∨ p1)) ∨ (p3 ∨ (False → p1))) ∨ ((p2 ∨ (p1 ∧ (p3 ∨ p5))) ∧ (((True → p1) → p2) ∧ p4))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_620572434036756863100140350964 : (((((p4 → False) ∨ (((p1 → p2) ∨ (p5 → ((((((p4 ∧ p5) → (p3 ∨ p2)) → p4) ∨ p5) → True) ∧ (p3 → p4)))) → False)) ∨ True) ∨ False) ∧ True) := by
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
theorem thm_5_vars_310224950566968886149741989158 : (p2 ∨ ((p5 ∨ ((p1 ∨ ((p2 ∨ (True ∨ p5)) ∧ (p5 → p3))) → p2)) ∨ (True → ((((p2 ∧ (False → (p2 → True))) → p1) → p4) → True)))) := by
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
theorem thm_5_vars_54069269583069370126458087427 : ((((p4 → (p1 → False)) ∨ ((p1 ∧ p3) ∧ (False → False))) → (p3 → ((p2 ∧ (((p1 → True) ∨ (False ∧ True)) ∨ p4)) ∨ (False ∧ p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_710159273265813617851925493005 : (((((((p4 ∧ p5) ∧ p5) → p3) ∨ p2) ∧ (p3 → (True → (p5 ∧ ((((((p3 ∧ p1) → p5) ∨ True) → p2) → p3) ∨ (p3 ∨ p4)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_343594061301678474746200624322 : (p2 → ((p2 → p5) → ((p5 → p5) → ((True → p3) → (((p5 ∧ False) ∨ ((((False ∨ (p2 ∧ p4)) → p4) ∧ (False ∨ p3)) ∨ False)) ∨ p5))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h5 : p2 := by
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h5
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119967550571133195797273553331 : ((((((((p2 ∧ False) ∧ p3) ∨ (((p3 ∨ p2) ∨ p4) ∨ p5)) ∨ (True → p5)) ∨ p1) ∨ ((p4 ∧ (p5 → p2)) ∨ p1)) ∧ p2) → (p1 ∨ p2)) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Disjunctions on the left can always be decomposed.
        cases h6
        case inl h7 =>
          -- Conjunctions on the left can always be decomposed.
          let h8 := h7.left
          let h9 := h7.right
          -- Conjunctions on the left can always be decomposed.
          let h10 := h8.left
          let h11 := h8.right
          -- False on the left can always be used.
          apply False.elim h11
        case inr h12 =>
          -- Disjunctions on the left can always be decomposed.
          cases h12
          case inl h13 =>
            -- Disjunctions on the left can always be decomposed.
            cases h13
            case inl h14 =>
              -- Disjunctions on the left can always be decomposed.
              cases h14
              case inl h15 =>
                -- Show the right disjunct based on <expert-advice>.
                apply Or.inr
                -- One of the premise coincides with the conclusion.
                exact h3
              case inr h16 =>
                -- Show the right disjunct based on <expert-advice>.
                apply Or.inr
                -- One of the premise coincides with the conclusion.
                exact h3
            case inr h17 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- One of the premise coincides with the conclusion.
              exact h3
          case inr h18 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h3
      case inr h19 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h3
    case inr h20 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h20
  case inr h21 =>
    -- Disjunctions on the left can always be decomposed.
    cases h21
    case inl h22 =>
      -- Conjunctions on the left can always be decomposed.
      let h23 := h22.left
      let h24 := h22.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h25 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h25



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161515989890411248455909124013 : ((p4 ∧ (p2 ∧ ((((p3 ∨ p2) ∧ p5) ∨ ((((p5 ∧ (p4 ∧ p4)) → True) → p4) ∨ p1)) ∨ p3))) → ((p5 ∨ ((p4 ∧ p3) ∨ True)) ∨ False)) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h10 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h9
      case inr h11 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h9
    case inr h12 =>
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h14 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h15 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347293205439776255922543897308 : (p3 → ((False ∧ (True → (((p4 ∧ p3) ∨ p2) ∧ (p3 ∧ p4)))) ∨ (((((p2 → (((False ∧ p4) ∨ p2) ∨ p3)) ∧ p1) ∨ p1) ∧ p1) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173862225572793079395067076332 : (((((True ∧ (p5 ∨ (p4 → (False ∧ (p4 → p3))))) ∨ (p1 ∧ p2)) ∧ p2) → p1) → (((False ∧ (p1 ∨ p2)) → p3) ∧ (p3 ∨ (p4 → p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h5
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52280330580570753159748197536 : (((p3 → (((p3 ∨ False) → ((p1 ∨ ((p4 → p3) ∨ (True ∨ False))) → False)) ∨ p3)) → (((p3 ∨ p3) → ((p5 ∨ p5) ∧ False)) ∨ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232018743711492077895282069762 : (((p3 ∨ True) → p1) → (p4 ∨ ((p2 ∧ (p4 ∨ (p3 ∧ p3))) ∨ (((p3 ∧ (p5 ∧ p1)) ∨ ((p1 ∨ p5) ∨ ((p5 ∧ p5) ∨ p4))) ∧ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p3 ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56196500248523030430103769895 : (((p5 ∧ (False → (p4 → p4))) ∨ ((p4 ∧ p3) ∨ (((((True ∧ True) → ((p3 ∧ (True ∧ p1)) ∨ p3)) ∨ (True ∨ p1)) ∧ p4) ∨ True))) ∨ p5) := by
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
theorem thm_5_vars_47006093925620839638960641296 : (((((False ∨ False) ∨ (p1 → (False ∨ ((p1 ∨ (((False ∨ p2) ∨ (p1 ∨ ((p4 ∨ False) ∨ p4))) → p5)) ∨ False)))) → p3) ∨ (p5 → p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174902150231836484314693237264 : (((p5 ∧ True) → (p2 → (((False ∧ (p2 → p2)) ∨ p4) → (p4 → (p1 ∧ p5))))) → ((p1 ∨ ((False ∨ False) ∧ (p1 → p5))) ∨ (True ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_306168822060106049151132500541 : (p1 ∨ (((p4 ∨ p1) → p5) ∨ ((p1 ∨ ((((p4 ∨ (p2 ∧ p1)) ∨ ((True → (p4 ∧ p2)) ∨ True)) ∨ ((p3 ∧ p5) ∧ True)) ∨ False)) ∨ p2))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_141301302882919654584113019799 : (((True ∨ ((True ∧ p3) ∨ p5)) ∧ (p2 ∨ (p4 → (p3 ∨ ((((p4 → True) ∨ (False → (True → p5))) → p5) ∧ p2))))) → (False ∨ (True ∧ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- True on the right can always be proven directly.
        apply True.intro
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- True on the right can always be proven directly.
        apply True.intro
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h13 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h14 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- True on the right can always be proven directly.
        apply True.intro
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h15 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- True on the right can always be proven directly.
        apply True.intro
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304732091925150648472423071173 : (p1 ∨ (((((((p3 → p5) → p1) → (p4 ∧ p5)) → p3) ∨ p3) → (((p3 ∨ ((False ∧ p3) ∧ p2)) ∧ p4) ∧ (p1 ∨ False))) ∨ (p2 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_688916517741095615706196621516 : ((((((p3 → p2) → ((p4 → (p4 ∨ (p4 → p3))) ∧ ((p2 ∧ False) ∧ True))) ∧ p3) ∨ (((True → ((p1 ∧ p4) ∨ p1)) ∨ p4) → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205789702638713617033293548795 : (((False ∨ p2) → ((p1 → True) → False)) ∨ (p2 → (((True → p1) → (False → p4)) ∧ ((p1 ∧ (((False ∨ True) ∨ p4) ∨ (p2 ∧ False))) ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181295184206474949250284547402 : ((p5 ∧ ((((p5 ∨ p4) → p3) ∨ p3) ∧ ((p1 ∨ (p3 ∨ p3)) ∧ p3))) → (False ∨ (p4 → (True ∨ (((p4 ∨ (p5 ∨ p5)) ∧ p1) → p2))))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
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
        -- Implications on the right can always be decomposed.
        intro h13
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h14 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h15
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h16 =>
    -- Conjunctions on the left can always be decomposed.
    let h17 := h5.left
    let h18 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h17
    case inl h19 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h20
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h21 =>
      -- Disjunctions on the left can always be decomposed.
      cases h21
      case inl h22 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h23
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h24 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h25
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249099120192729287488159587796 : ((p4 ∨ p1) ∨ (p4 → ((p5 ∨ (p5 ∨ (((True ∨ p3) ∧ True) ∧ (((p5 → (p1 ∧ (p4 ∧ p1))) ∨ p4) ∨ ((p2 → p2) ∨ p5))))) ∨ p3))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217644744625054247236111120066 : ((((p5 ∧ p5) → False) → p2) → (((p4 ∨ (p5 ∨ p3)) ∨ (p1 ∧ p2)) ∨ (False → ((((p3 → (p3 → (p3 → False))) → p5) ∧ p1) ∧ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h2
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_700804072785152182010091338579 : (((((True ∧ ((((p1 ∧ p4) ∨ p5) → False) ∨ False)) ∧ p5) ∧ (p1 ∧ (p1 ∨ (p2 ∧ ((p5 → False) ∧ ((p1 ∨ (p2 → True)) ∧ p4)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114350500735443761329216630393 : (((p1 → (False ∨ ((p2 ∧ (p1 ∧ (((p5 ∧ (p4 ∨ p2)) → p4) ∧ p5))) ∨ (p5 → p1)))) ∧ (p3 ∨ (p1 ∨ (p3 ∧ p3)))) ∨ (True ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192965363730766163496665720903 : (((False ∨ (p4 ∨ ((False → p2) → False))) ∨ (True → p3)) → ((p2 → (((((p3 ∧ (p4 ∨ p1)) → True) ∨ (p5 ∧ False)) ∨ p4) → False)) ∨ True)) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h5 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h6 =>
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
theorem thm_5_vars_124543672492464827153873268190 : (((True → ((p3 ∧ p3) → (p3 ∨ p5))) ∧ ((((p3 ∨ False) ∧ ((p2 ∨ ((p2 → p2) ∧ (False ∨ p3))) → False)) ∨ p4) ∧ p3)) → (p2 ∨ p4)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h9 =>
      -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
      have h10 : (p2 ∨ ((p2 → p2) ∧ (False ∨ p3))) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Implications on the right can always be decomposed.
        intro h11
        -- One of the premise coincides with the conclusion.
        exact h11
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h5
      -- We have shown the premise of h8, we can now drive its conclusion.
      let h12 := h8 h10
      -- False on the left can always be used.
      apply False.elim h12
    case inr h13 =>
      -- False on the left can always be used.
      apply False.elim h13
  case inr h14 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_774775729809686465143523221009 : (((False ∨ ((((p5 ∨ (p2 ∧ p1)) ∧ p3) ∨ p3) ∨ ((p5 ∧ (((p1 ∨ True) ∨ (p2 ∨ (p4 ∨ (p2 ∨ (p3 ∧ p2))))) ∧ False)) → p5))) ∨ p3) ∧ True) := by
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
      -- False on the left can always be used.
      apply False.elim h5
    case inr h8 =>
      -- False on the left can always be used.
      apply False.elim h5
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- False on the left can always be used.
      apply False.elim h5
    case inr h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- False on the left can always be used.
        apply False.elim h5
      case inr h13 =>
        -- Disjunctions on the left can always be decomposed.
        cases h13
        case inl h14 =>
          -- False on the left can always be used.
          apply False.elim h5
        case inr h15 =>
          -- Conjunctions on the left can always be decomposed.
          let h16 := h15.left
          let h17 := h15.right
          -- False on the left can always be used.
          apply False.elim h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_598436889422271111673062894964 : ((((((p5 ∨ p4) ∧ True) → ((p2 ∨ ((p2 ∨ ((True → p3) → p5)) → (((False ∨ (False → p1)) → p5) → (p5 → p4)))) → p5)) ∧ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_662410240827633591089254632622 : ((((((((p5 ∨ True) ∧ False) → (p4 ∨ p3)) ∨ p2) → ((p2 → p4) ∨ (p3 ∨ (p4 ∨ (((False → False) ∧ p5) ∨ p4))))) → (p2 ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_864544012518797784478591939569 : ((((((p3 ∨ (p2 ∨ (False ∨ True))) ∧ (False ∨ True)) ∨ ((p1 ∧ p1) → ((p1 ∧ ((p5 ∨ ((True ∨ p2) → p5)) ∨ p4)) ∧ False))) → False) → p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p3 ∨ (p2 ∨ (False ∨ True))) ∧ (False ∨ True)) ∨ ((p1 ∧ p1) → ((p1 ∧ ((p5 ∨ ((True ∨ p2) → p5)) ∨ p4)) ∧ False))) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
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
theorem thm_5_vars_44910924256914534985955262663 : ((((p1 → (p4 → p4)) → (((p5 ∧ ((((False → p5) ∨ p4) → True) → (((False ∧ (p3 ∧ False)) → p5) ∧ p5))) ∨ p4) → False)) → p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_76270876336227133387597741955 : (((((((p5 ∨ (p5 → p1)) ∧ (((((p2 ∨ p1) ∨ p3) ∧ p3) ∧ (p2 ∨ (True ∨ True))) ∧ False)) ∨ True) ∨ p4) ∨ (False → p2)) → p4) → p4) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((((p5 ∨ (p5 → p1)) ∧ (((((p2 ∨ p1) ∨ p3) ∧ p3) ∧ (p2 ∨ (True ∨ True))) ∧ False)) ∨ True) ∨ p4) ∨ (False → p2)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60951970831426769940320944861 : ((False ∧ ((((((p2 ∧ ((True ∧ True) ∨ ((p5 ∧ p5) → False))) ∨ p5) → (True ∧ ((False ∨ (p1 → False)) ∨ False))) ∧ p1) → p4) ∨ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192243337379165569659164663953 : ((((((p3 ∧ False) → p4) ∨ False) → (True → p1)) ∧ p4) → ((p5 ∧ p2) ∨ ((p5 ∧ (((p3 ∧ ((p2 ∨ p5) ∧ False)) ∧ False) → p3)) → p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
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
theorem thm_5_vars_111766055271262462740132633464 : (((((p2 → (True ∨ (p4 → p3))) ∧ ((((p2 ∨ p1) ∨ p5) ∨ ((p5 ∧ (True ∨ p5)) ∨ False)) ∨ False)) ∧ (p1 ∧ p5)) ∨ p2) ∨ (p5 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_209545344716154600352552094723 : ((p4 → (p1 → (p5 ∧ (p3 → p3)))) → (((True ∨ (True ∨ (p5 ∧ (p5 → True)))) → (False ∧ p4)) → (((p4 ∨ p2) ∨ p4) ∨ (p5 → p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (True ∨ (True ∨ (p5 ∧ (p5 → True)))) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110882346695867847132569763849 : ((((((p4 → p3) ∧ ((p4 → (p4 → p2)) ∧ (True → ((True ∧ False) ∨ True)))) ∧ ((p2 ∧ p1) → (p3 → p3))) → p2) ∧ p2) ∨ (True → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_753147281961600570768044633592 : (((False ∧ (((p3 → ((p4 ∨ ((((False ∧ True) ∨ (p4 ∨ (p5 ∧ False))) ∨ p4) ∧ (p5 → (False ∨ p5)))) ∨ p5)) → p3) ∧ (p5 ∨ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217063711756522132363762477801 : ((((p1 → p4) ∧ True) ∨ p4) → ((False ∧ False) ∨ (((p4 ∨ ((p2 ∨ ((p4 ∨ p2) → p2)) ∧ p4)) ∧ (p3 → (False → p3))) → (p4 ∨ True)))) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h13 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h14 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h15
    -- Conjunctions on the left can always be decomposed.
    let h16 := h15.left
    let h17 := h15.right
    -- Disjunctions on the left can always be decomposed.
    cases h16
    case inl h18 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h19 =>
      -- Conjunctions on the left can always be decomposed.
      let h20 := h19.left
      let h21 := h19.right
      -- Disjunctions on the left can always be decomposed.
      cases h20
      case inl h22 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h23 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234621630661528748053389876049 : ((p3 → (False → p1)) → (((p3 → ((True ∨ False) → (p3 ∧ (((p1 ∨ (p4 ∧ (p2 → p5))) ∧ p3) → ((False → p5) → p2))))) → p5) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148129197523604867943705773165 : ((((True → p5) ∧ ((((p2 → p4) ∨ (p3 → (p2 ∨ (p2 ∧ True)))) → (p5 ∨ p3)) → True)) → (p3 → p5)) ∨ (p5 ∨ (p4 ∨ (p1 ∨ p3)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h5 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h5
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_521942856389599299553454668301 : ((((p2 → p5) → ((p5 → ((True ∨ p5) → (((p4 ∨ (p1 → ((p5 ∨ (p1 ∨ p1)) ∧ p2))) ∨ False) ∨ p5))) ∧ ((False ∧ p2) → p2))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  -- Implications on the right can always be decomposed.
  intro h6
  -- Conjunctions on the left can always be decomposed.
  let h7 := h6.left
  let h8 := h6.right
  -- False on the left can always be used.
  apply False.elim h7
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172337990619993721300083157432 : ((((p1 ∨ p1) → (p2 ∨ (p2 ∨ p2))) ∧ (((True ∨ (p1 ∨ p1)) → p4) ∨ p3)) ∨ (((((p1 ∧ (p1 ∨ p3)) → p2) ∨ True) → p1) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111779386761172686890490749732 : (((((p3 ∧ (p2 ∨ (p2 → (((p4 ∧ p3) ∨ (((p2 ∨ p3) ∧ p4) → p2)) ∨ (True ∧ p3))))) ∨ p3) ∨ (p1 → p2)) ∨ True) ∨ (p1 → p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198474665556904673252911097888 : ((p5 ∧ (p3 → (((p1 → p4) ∨ False) → p1))) ∨ (False ∨ ((((p5 ∨ (p2 ∨ (p5 ∧ False))) ∧ (p5 ∨ ((p4 → p2) ∨ p1))) ∧ False) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_660057159829078162432121073436 : ((((((((p4 ∨ (p5 → (p3 ∨ ((p4 → ((p4 ∨ False) ∨ (p4 → True))) ∧ p2)))) → p3) ∨ p1) ∨ (p1 ∨ p3)) ∨ p5) → (p1 ∧ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_619074237982830324462104193353 : ((((((p3 → True) → p2) ∨ (p5 ∨ ((p5 ∨ (p3 → p3)) ∧ (((True ∧ p5) ∧ ((p1 → p4) → ((p2 → False) ∨ p4))) ∨ p2)))) ∨ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_382082896000395817258406301451 : (((((((p3 ∧ ((p1 → True) ∧ p3)) ∧ (((p1 → (p1 → p2)) ∨ False) ∨ (p1 → ((False ∨ p2) ∨ p3)))) ∧ (False ∨ False)) ∨ True) ∨ p5) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117228409094773227846522030166 : ((True ∧ (True ∧ ((((p1 → (False ∨ p2)) ∧ ((p5 → p1) ∨ p5)) ∧ (True ∧ (p5 ∧ ((False → (p1 ∨ True)) ∨ p5)))) ∧ p2))) ∨ (True ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_776769412954539916734682269613 : (((p1 ∨ ((((False → (False → p3)) ∧ (((((p2 ∨ p2) → p3) ∨ p4) → p5) → (True → False))) ∧ ((p2 ∧ p3) → (p3 ∧ False))) → p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138308670129038961167949713694 : ((p3 → ((((p4 ∧ p3) ∧ p5) ∧ p2) ∨ (p3 → (p1 ∨ ((True ∧ ((((p2 ∨ p3) ∧ p5) → p5) → p4)) ∨ True))))) ∨ ((p5 → True) ∧ p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_696391965394360489489691040851 : ((((p5 → ((p2 ∨ p4) ∨ ((p5 ∨ p3) → (((p2 ∨ p4) → p4) ∨ p5)))) → (((p5 ∧ (False ∨ p5)) ∧ p3) ∨ (p5 ∨ (p4 → True)))) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111410550247292515856308642986 : (((p2 ∨ (p1 ∨ ((False ∧ p1) ∨ (((((p1 ∧ (((False ∧ p1) → p3) ∨ False)) ∧ p1) ∨ p1) ∨ True) ∧ (p1 ∧ True))))) ∧ p2) ∨ (True ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137908395221509135849227951416 : ((p4 ∨ (((False → p2) ∧ ((p5 ∨ p2) ∧ (p2 ∧ p1))) ∨ (((p1 ∧ True) → (True → (True ∧ (p4 → p5)))) ∧ p5))) ∨ (False → (p3 → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_608471841995995228968192208607 : (((((((p4 ∨ (((((p5 ∧ True) ∧ ((True ∧ False) ∧ p1)) ∧ (p3 → p3)) → p5) ∨ False)) ∧ (p2 → (p5 → p3))) → p2) ∨ p1) ∨ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218261053210694326533679010771 : (((p1 ∨ False) ∨ (p2 ∨ p3)) → (True → (p4 ∨ (((p5 → (True ∨ ((((False ∨ p1) ∨ False) ∨ False) ∧ p5))) → (p3 ∨ (True ∨ p4))) ∨ p3)))) := by
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h5
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h6 =>
      -- False on the left can always be used.
      apply False.elim h6
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h9
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116812403331636853227397033378 : (((p3 ∨ p5) ∨ (False ∨ (((p1 ∧ p5) ∧ (p2 ∨ ((p5 ∨ (p5 ∧ p3)) ∧ (p5 ∧ ((p4 ∧ (False ∧ p4)) ∧ p3))))) ∨ p4))) ∨ (True ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149853762448215121904674164241 : ((p1 ∨ (p5 ∨ ((((p1 ∧ (((False → p1) ∧ p1) ∧ ((p3 ∧ p1) → p3))) ∨ p4) ∧ p4) ∨ (True ∨ p5)))) ∨ (p5 → ((p5 ∧ True) ∨ p2))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_784440809560976037810478873721 : (((p3 ∨ (p4 ∧ (p3 → ((p5 ∧ False) ∨ ((((p1 ∨ p4) ∨ ((p2 ∨ p5) ∧ ((p5 → ((p3 ∨ p3) ∨ True)) ∨ True))) → p4) ∧ p1))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_749473142234620012691610540314 : (((True ∧ (((p3 ∨ ((p2 ∧ (p4 ∧ True)) ∧ p2)) ∧ (p5 → (((((p4 ∧ ((p1 ∧ False) ∧ True)) ∧ p2) ∧ p2) ∧ p1) → p3))) ∧ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207759290559353523852930951632 : (((p1 ∨ (True ∨ (False ∧ p4))) → False) → ((((False → p2) ∨ ((p4 → True) → True)) ∨ ((((p2 ∨ p3) ∧ p2) ∨ (p4 → p3)) ∨ p3)) → False)) := by
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
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h5 : (p1 ∨ (True ∨ (False ∧ p4))) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h6 := h1 h5
      -- False on the left can always be used.
      apply False.elim h6
    case inr h7 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h8 : (p1 ∨ (True ∨ (False ∧ p4))) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h9 := h1 h8
      -- False on the left can always be used.
      apply False.elim h9
  case inr h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- Conjunctions on the left can always be decomposed.
        let h13 := h12.left
        let h14 := h12.right
        -- Disjunctions on the left can always be decomposed.
        cases h13
        case inl h15 =>
          -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
          have h16 : (p1 ∨ (True ∨ (False ∧ p4))) := by
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h1, we can now drive its conclusion.
          let h17 := h1 h16
          -- False on the left can always be used.
          apply False.elim h17
        case inr h18 =>
          -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
          have h19 : (p1 ∨ (True ∨ (False ∧ p4))) := by
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h1, we can now drive its conclusion.
          let h20 := h1 h19
          -- False on the left can always be used.
          apply False.elim h20
      case inr h21 =>
        -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
        have h22 : (p1 ∨ (True ∨ (False ∧ p4))) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h1, we can now drive its conclusion.
        let h23 := h1 h22
        -- False on the left can always be used.
        apply False.elim h23
    case inr h24 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h25 : (p1 ∨ (True ∨ (False ∧ p4))) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h26 := h1 h25
      -- False on the left can always be used.
      apply False.elim h26



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_787981490291977208865297742341 : (((p4 ∨ (p5 → (((p1 → (False ∧ (p5 → p5))) ∧ ((((((p5 → p4) → False) ∧ p1) ∧ p5) → p4) → (p3 ∨ p4))) ∨ (False → p2)))) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206447865119701142543765205745 : ((p4 ∨ ((p5 ∧ False) ∧ (p2 ∨ p2))) ∨ (p2 ∨ (False ∨ ((((False ∧ True) → (p4 ∧ (False ∧ p4))) ∨ ((p4 → (False ∨ p2)) ∨ p3)) ∨ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- False on the left can always be used.
  apply False.elim h4
  -- Conjunctions on the left can always be decomposed.
  let h6 := h1.left
  let h7 := h1.right
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112670180942079205524426890080 : ((((p2 → ((p3 → ((((p1 ∨ p1) → (((p4 ∨ True) ∧ p1) → True)) ∨ p5) ∧ p2)) → p3)) ∨ ((False ∧ p1) ∨ True)) → p2) ∨ (False → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



