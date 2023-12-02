variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133755557385835024021253537601 : ((((((p1 ∧ p3) ∧ p2) ∨ (False ∨ p4)) ∧ (p4 → (True ∧ ((p5 ∨ (p2 ∧ False)) ∨ ((p2 ∧ p2) ∨ True))))) ∧ True) ∨ ((True ∨ p1) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_739376609323559285012694060588 : ((((p4 ∧ p5) ∨ (((p2 ∨ p1) → ((True ∧ (False ∨ (p1 ∨ (((p1 → p1) ∨ ((p2 ∧ True) ∨ p3)) ∧ p4)))) → False)) ∧ (True ∨ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_339668992266550261189584318468 : (p1 → (p3 ∨ ((((((p2 → False) ∧ p4) ∨ (p2 → (True → ((p5 → (p1 ∨ (p3 → (p1 ∨ False)))) → p1)))) → False) ∧ (p3 ∨ True)) → p5))) := by
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
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h6 : (((p2 → False) ∧ p4) ∨ (p2 → (True → ((p5 → (p1 ∨ (p3 → (p1 ∨ False)))) → p1)))) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h7
      -- Implications on the right can always be decomposed.
      intro h8
      -- Implications on the right can always be decomposed.
      intro h9
      -- One of the premise coincides with the conclusion.
      exact h1
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h10 := h3 h6
    -- False on the left can always be used.
    apply False.elim h10
  case inr h11 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h12 : (((p2 → False) ∧ p4) ∨ (p2 → (True → ((p5 → (p1 ∨ (p3 → (p1 ∨ False)))) → p1)))) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h13
      -- Implications on the right can always be decomposed.
      intro h14
      -- Implications on the right can always be decomposed.
      intro h15
      -- One of the premise coincides with the conclusion.
      exact h1
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h16 := h3 h12
    -- False on the left can always be used.
    apply False.elim h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_626659411184622372403111798603 : ((((p4 → (p3 → (((((((False ∨ False) ∨ (p3 ∨ p4)) ∨ False) ∧ (False ∨ ((p4 → p3) → False))) → p5) → (p2 ∨ p2)) ∨ p1))) ∨ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135523458837569190741600453052 : (((((True ∧ ((p2 ∨ p3) ∧ p3)) ∨ ((False ∧ (True ∨ False)) → (p1 ∧ p3))) ∨ p4) ∧ (p2 ∨ (p3 ∧ (p1 ∨ p4)))) ∨ (p5 → (False → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199431303620106614294358171014 : (((True ∧ ((p1 ∧ p5) ∧ (p3 → p4))) ∨ True) → ((False ∨ (((p3 ∧ (((p3 ∧ True) → p2) ∧ (True ∨ (p3 ∨ p4)))) ∧ False) ∨ True)) ∨ p4)) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h9 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119468468532391449132412192074 : ((p4 → ((p3 → p2) ∨ ((p2 ∨ (((((p3 → (p3 ∨ p3)) → (True ∧ p4)) ∧ p4) → False) ∧ ((p3 ∨ p3) ∨ True))) ∨ True))) ∨ (False ∨ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111168057023692052337109485910 : ((((False ∨ (p4 ∧ (p5 → p2))) ∧ (p1 → ((((p4 → p5) ∧ ((p3 ∨ p2) ∧ p2)) ∧ (p1 → (p5 → True))) ∧ True))) ∧ p2) ∨ (p4 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_139965943941177315538677226315 : (((False ∨ ((((((p2 ∨ (True ∨ ((p3 ∧ p3) ∧ p4))) ∨ True) ∧ p4) ∨ (p1 → p5)) ∨ p2) ∧ p2)) ∧ (True ∨ p1)) → (False ∨ (p3 → True))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
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
            cases h3
            case inl h14 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- Implications on the right can always be decomposed.
              intro h15
              -- True on the right can always be proven directly.
              apply True.intro
            case inr h16 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- Implications on the right can always be decomposed.
              intro h17
              -- True on the right can always be proven directly.
              apply True.intro
          case inr h18 =>
            -- Disjunctions on the left can always be decomposed.
            cases h18
            case inl h19 =>
              -- Disjunctions on the left can always be decomposed.
              cases h3
              case inl h20 =>
                -- Show the right disjunct based on <expert-advice>.
                apply Or.inr
                -- Implications on the right can always be decomposed.
                intro h21
                -- True on the right can always be proven directly.
                apply True.intro
              case inr h22 =>
                -- Show the right disjunct based on <expert-advice>.
                apply Or.inr
                -- Implications on the right can always be decomposed.
                intro h23
                -- True on the right can always be proven directly.
                apply True.intro
            case inr h24 =>
              -- Conjunctions on the left can always be decomposed.
              let h25 := h24.left
              let h26 := h24.right
              -- Conjunctions on the left can always be decomposed.
              let h27 := h25.left
              let h28 := h25.right
              -- Disjunctions on the left can always be decomposed.
              cases h3
              case inl h29 =>
                -- Show the right disjunct based on <expert-advice>.
                apply Or.inr
                -- Implications on the right can always be decomposed.
                intro h30
                -- True on the right can always be proven directly.
                apply True.intro
              case inr h31 =>
                -- Show the right disjunct based on <expert-advice>.
                apply Or.inr
                -- Implications on the right can always be decomposed.
                intro h32
                -- True on the right can always be proven directly.
                apply True.intro
        case inr h33 =>
          -- Disjunctions on the left can always be decomposed.
          cases h3
          case inl h34 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h35
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h36 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h37
            -- True on the right can always be proven directly.
            apply True.intro
      case inr h38 =>
        -- Disjunctions on the left can always be decomposed.
        cases h3
        case inl h39 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h40
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h41 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h42
          -- True on the right can always be proven directly.
          apply True.intro
    case inr h43 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h44 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h45
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h46 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h47
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_183906518388116236299886724798 : ((((False ∨ True) → (p5 → ((p4 → p3) → (False ∨ False)))) ∧ False) ∨ (((((((p3 → p1) → (p1 ∨ p5)) ∧ p4) ∧ p5) ∧ p2) → True) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_685812730534395720293752001154 : ((((((p5 ∧ (p3 ∨ ((((p3 → p2) → p5) ∧ p2) ∧ p2))) ∨ (p3 ∨ (p3 ∨ p1))) → p3) → (((True → p1) ∧ (False → p4)) → p3)) ∨ p1) ∧ True) := by
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
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h5 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h5
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h7 : ((p5 ∧ (p3 ∨ ((((p3 → p2) → p5) ∧ p2) ∧ p2))) ∨ (p3 ∨ (p3 ∨ p1))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h6
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h8 := h1 h7
  -- One of the premise coincides with the conclusion.
  exact h8
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58668779821575167714305170524 : (((p1 → p5) ∧ (p5 ∨ ((((p5 → (True → p1)) ∨ p2) → ((p2 → p3) ∨ (p3 → p5))) → ((p2 ∨ (p2 ∧ True)) ∨ (False ∨ p1))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_800564064445712010626509287779 : (((p2 → ((((p2 → p4) ∨ ((p5 ∧ (p1 → (p5 ∨ ((False → (False ∧ p4)) ∨ (False ∨ p3))))) → False)) ∧ (False ∨ (p5 ∧ p4))) → p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48666518308251549245397550712 : ((((p2 ∧ (p4 ∨ (p2 ∨ (p5 → (False ∨ (p2 → (p2 → p1))))))) ∨ (((p4 ∨ (p4 ∧ p2)) → True) ∨ p5)) ∧ (p4 ∨ (p2 → p2))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263969106720340452390085804651 : (True ∧ ((((p2 ∨ (((False → p2) → (p1 ∨ p2)) ∧ p1)) ∨ p1) ∧ False) ∨ (((p4 ∨ (p3 → ((p5 → (p1 → p3)) ∧ p3))) ∨ p1) ∨ False))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111183831883450692612725892533 : (((((True → p5) ∨ (p2 → p2)) → (p1 → (p2 ∨ (p1 → (p3 ∨ ((((True ∨ True) → (p4 ∨ p3)) → False) → p4)))))) ∧ p1) ∨ (False → False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152106401885136896287272373140 : (((p1 → ((p1 → p3) → ((p1 → True) ∨ (p5 ∧ p2)))) → ((p1 ∨ p5) ∧ ((False ∧ p4) ∧ (p3 → p3)))) → (False ∨ ((p2 ∧ p2) ∧ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p1 → ((p1 → p3) → ((p1 → True) ∨ (p5 ∧ p2)))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h2
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- We need to get the left conjuct of h7 based on <expert-advice>.
  let h8 := h7.left
  -- We need to get the left conjuct of h8 based on <expert-advice>.
  let h9 := h8.left
  -- False on the left can always be used.
  apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134265825631506070279831917402 : ((((p2 ∨ (p3 → p5)) → (((p1 → (p5 ∧ p4)) → (True → (((p4 → p3) ∨ (True ∨ p3)) ∨ False))) ∨ p5)) ∨ False) ∨ (False ∧ (p5 → True))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h6
    -- Implications on the right can always be decomposed.
    intro h7
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62231977832659087862126843944 : ((p3 ∧ ((((((((p4 → p4) ∨ ((p1 ∨ p4) ∧ p3)) ∧ p1) ∨ (p5 ∨ False)) ∧ ((True ∧ True) ∨ p2)) ∨ p4) ∨ (p4 ∧ False)) ∨ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61936927833738149641612431954 : ((p2 ∧ (((False → p5) ∧ (p3 ∧ (((p5 ∨ p3) → ((False ∨ p1) → (False ∧ p5))) ∨ (False ∨ p2)))) → (((p5 → p4) ∨ p1) ∨ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300811894168440670650647061711 : (False ∨ (((((True ∧ ((((False → p1) ∨ p4) ∨ p4) → p5)) ∨ True) → True) ∨ (False → False)) → ((p5 ∧ (p2 ∨ True)) ∨ (True ∨ (p2 ∨ p3))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_673887571912494440389480703762 : (((((False ∨ p2) → ((p5 → (p4 ∧ p4)) ∨ ((p1 → ((True ∨ p5) ∧ False)) ∨ (p2 ∧ ((False ∨ False) ∨ p4))))) → (p3 ∧ (p2 → p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193726379795079124549251015299 : ((p2 ∧ ((False ∧ p2) → (((p5 ∧ True) ∨ False) ∨ p4))) → ((p4 ∧ (p1 ∨ p1)) ∨ ((True → (p1 → (False ∨ ((p3 ∨ True) → p4)))) ∨ True))) := by
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
theorem thm_5_vars_344638433188071762013377687499 : (p2 → (p1 → (True → (((True → p3) → p4) ∨ (((p1 ∧ (p4 ∨ p1)) ∨ (p4 ∧ (p4 → p5))) → ((True → p3) ∨ (p4 ∨ (p1 ∨ p5)))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h9
  case inr h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_674875550699767664377338036717 : ((((((p3 → (p2 ∨ (((p5 → p2) ∨ (((False → False) ∧ p3) ∧ (True ∨ p5))) → False))) ∧ p1) ∧ p2) ∧ (p1 ∨ (p4 ∧ (p5 ∨ p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215093858156628838813310158393 : (((False → p4) → (p4 → p1)) ∨ (((p4 ∧ True) → (((p5 → ((((True ∨ p1) ∨ False) → p4) → (p5 → True))) ∧ p5) ∨ (p5 → p3))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136709672576928394098307730863 : (((p2 ∧ p1) ∧ (p4 ∨ ((p1 ∨ p1) ∧ (p2 ∧ (True ∨ ((p2 ∨ (p1 → p3)) → ((p5 ∧ False) → (p2 → p2)))))))) ∨ (p2 ∨ (True ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147359976954101676783227486283 : (((((p1 ∨ (p3 ∧ ((False ∨ ((p5 ∧ (True ∧ p3)) ∧ p5)) → False))) ∨ p4) → (p2 ∨ (p2 ∨ p4))) ∨ p2) ∨ (True ∨ (p1 → (p5 → p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234670050221188480271073945326 : ((p4 → (p1 ∧ p5)) → ((((((p1 → p1) → False) ∧ p5) ∧ ((False ∨ (True ∨ p3)) → False)) ∧ ((p5 → p2) ∧ True)) → ((True → p2) ∧ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- Conjunctions on the left can always be decomposed.
  let h10 := h5.left
  let h11 := h5.right
  -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
  have h12 : (False ∨ (True ∨ p3)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h7, we can now drive its conclusion.
  let h13 := h7 h12
  -- False on the left can always be used.
  apply False.elim h13
  -- Conjunctions on the left can always be decomposed.
  let h14 := h2.left
  let h15 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h16 := h14.left
  let h17 := h14.right
  -- Conjunctions on the left can always be decomposed.
  let h18 := h16.left
  let h19 := h16.right
  -- Conjunctions on the left can always be decomposed.
  let h20 := h15.left
  let h21 := h15.right
  -- We want to use the implication h17 based on <expert-advice>. So we show its premise.
  have h22 : (False ∨ (True ∨ p3)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h17, we can now drive its conclusion.
  let h23 := h17 h22
  -- False on the left can always be used.
  apply False.elim h23



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_757199377326791168033383194369 : (((p1 ∧ ((False ∧ p4) ∧ (p3 ∨ (((p2 → ((p5 → True) ∨ ((p5 ∧ False) → (p2 ∨ False)))) → p1) ∨ (p3 → (p1 ∨ (False ∧ False))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_947516489693837052346854940107 : (((((p1 → True) ∧ (p1 ∨ True)) → ((((p1 ∨ ((True ∧ (((False ∨ p5) → (p2 ∨ p5)) → p3)) ∧ True)) → (p2 → True)) ∧ p1) ∧ p4)) → p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p1 → True) ∧ (p1 ∨ True)) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- One of the premise coincides with the conclusion.
  exact h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60695736793649457033161577953 : ((True ∧ ((((p3 ∨ p1) ∨ (p3 ∧ ((p4 ∨ False) ∨ p4))) ∧ p3) ∨ (((p5 ∧ False) ∨ (False ∧ (p2 → False))) → ((True ∧ p4) → p4)))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- False on the left can always be used.
    apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_209001021525425803802452396298 : ((False ∨ (((True ∧ False) ∧ False) → p2)) → (p1 → (True → (((p5 ∧ (((p1 ∧ True) → p3) ∨ p3)) → (p3 ∧ p3)) ∧ ((p2 ∧ p4) ∨ p1))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h8 =>
      -- False on the left can always be used.
      apply False.elim h8
    case inr h9 =>
      -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
      have h10 : (p1 ∧ True) := by
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h2
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h7, we can now drive its conclusion.
      let h11 := h7 h10
      -- One of the premise coincides with the conclusion.
      exact h11
  case inr h12 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h13 =>
      -- False on the left can always be used.
      apply False.elim h13
    case inr h14 =>
      -- One of the premise coincides with the conclusion.
      exact h12
  -- Conjunctions on the left can always be decomposed.
  let h15 := h4.left
  let h16 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h16
  case inl h17 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h18 =>
      -- False on the left can always be used.
      apply False.elim h18
    case inr h19 =>
      -- We want to use the implication h17 based on <expert-advice>. So we show its premise.
      have h20 : (p1 ∧ True) := by
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h2
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h17, we can now drive its conclusion.
      let h21 := h17 h20
      -- One of the premise coincides with the conclusion.
      exact h21
  case inr h22 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h23 =>
      -- False on the left can always be used.
      apply False.elim h23
    case inr h24 =>
      -- One of the premise coincides with the conclusion.
      exact h22
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h25 =>
    -- False on the left can always be used.
    apply False.elim h25
  case inr h26 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_344356301457590579153289702827 : (p2 → (p4 ∨ ((True → ((p1 ∨ (p2 → True)) ∧ ((((p5 ∧ (p3 ∨ True)) ∨ (p5 → p5)) → p4) ∧ ((False ∧ (False ∧ p3)) ∨ True)))) → p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h7 : ((p5 ∧ (p3 ∨ True)) ∨ (p5 → p5)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- One of the premise coincides with the conclusion.
    exact h8
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h9 := h6 h7
  -- One of the premise coincides with the conclusion.
  exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_312228236396712254670294687992 : (p2 ∨ (p1 → (((((((((p4 ∧ (p2 ∧ ((p2 → (p3 ∧ p4)) ∧ p4))) ∧ p1) → True) ∨ p1) ∨ p2) ∧ (p1 → p5)) ∨ True) → False) ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305179310328923857168661021241 : (p1 ∨ ((((p1 ∧ (p5 ∧ p5)) ∧ p5) ∧ ((p5 ∨ ((((p1 ∧ p1) ∧ p4) ∨ (p3 → True)) → p3)) ∧ p3)) ∨ (((p3 → True) ∧ p1) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_226287528285387009036578916237 : (((p4 ∨ p2) ∨ False) ∨ (((p4 → (p2 ∨ p5)) ∨ (((True ∧ (p1 → False)) ∧ p1) → (((p3 ∧ (False → p4)) → p1) → p2))) ∨ (p4 ∧ p2))) := by
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
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h7 : p1 := by
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h8 := h6 h7
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206032628436430711659409880725 : ((p2 ∧ ((p5 → p3) ∨ (p5 ∧ False))) ∨ (((((True → False) ∨ p1) → (((True ∧ p3) → p5) ∧ p3)) → (p5 ∧ p1)) ∨ ((p3 → True) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_957857564041981095591830528139 : ((((p4 ∨ (False → p4)) → ((((((True ∨ p2) → p4) ∧ (p5 → True)) ∧ p5) → (((p4 ∧ p3) ∧ p1) ∨ ((p2 ∧ p2) ∧ True))) ∧ False)) → p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p4 ∨ (False → p4)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- False on the left can always be used.
  apply False.elim h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321673621897686002736935391120 : (p4 ∨ (p4 → (((p1 ∨ (p2 ∧ ((True ∧ p5) ∨ p1))) ∧ ((False ∨ ((p2 ∨ (p4 ∨ p1)) ∧ True)) ∧ (True ∨ p5))) → ((p4 → p1) ∨ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- False on the left can always be used.
      apply False.elim h8
    case inr h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h12 =>
        -- Disjunctions on the left can always be decomposed.
        cases h7
        case inl h13 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h1
        case inr h14 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h1
      case inr h15 =>
        -- Disjunctions on the left can always be decomposed.
        cases h15
        case inl h16 =>
          -- Disjunctions on the left can always be decomposed.
          cases h7
          case inl h17 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h1
          case inr h18 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h1
        case inr h19 =>
          -- Disjunctions on the left can always be decomposed.
          cases h7
          case inl h20 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h1
          case inr h21 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h1
  case inr h22 =>
    -- Conjunctions on the left can always be decomposed.
    let h23 := h22.left
    let h24 := h22.right
    -- Disjunctions on the left can always be decomposed.
    cases h24
    case inl h25 =>
      -- Conjunctions on the left can always be decomposed.
      let h26 := h25.left
      let h27 := h25.right
      -- Conjunctions on the left can always be decomposed.
      let h28 := h4.left
      let h29 := h4.right
      -- Disjunctions on the left can always be decomposed.
      cases h28
      case inl h30 =>
        -- False on the left can always be used.
        apply False.elim h30
      case inr h31 =>
        -- Conjunctions on the left can always be decomposed.
        let h32 := h31.left
        let h33 := h31.right
        -- Disjunctions on the left can always be decomposed.
        cases h32
        case inl h34 =>
          -- Disjunctions on the left can always be decomposed.
          cases h29
          case inl h35 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h1
          case inr h36 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h1
        case inr h37 =>
          -- Disjunctions on the left can always be decomposed.
          cases h37
          case inl h38 =>
            -- Disjunctions on the left can always be decomposed.
            cases h29
            case inl h39 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- One of the premise coincides with the conclusion.
              exact h1
            case inr h40 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- One of the premise coincides with the conclusion.
              exact h1
          case inr h41 =>
            -- Disjunctions on the left can always be decomposed.
            cases h29
            case inl h42 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- One of the premise coincides with the conclusion.
              exact h1
            case inr h43 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- One of the premise coincides with the conclusion.
              exact h1
    case inr h44 =>
      -- Conjunctions on the left can always be decomposed.
      let h45 := h4.left
      let h46 := h4.right
      -- Disjunctions on the left can always be decomposed.
      cases h45
      case inl h47 =>
        -- False on the left can always be used.
        apply False.elim h47
      case inr h48 =>
        -- Conjunctions on the left can always be decomposed.
        let h49 := h48.left
        let h50 := h48.right
        -- Disjunctions on the left can always be decomposed.
        cases h49
        case inl h51 =>
          -- Disjunctions on the left can always be decomposed.
          cases h46
          case inl h52 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h1
          case inr h53 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h1
        case inr h54 =>
          -- Disjunctions on the left can always be decomposed.
          cases h54
          case inl h55 =>
            -- Disjunctions on the left can always be decomposed.
            cases h46
            case inl h56 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- One of the premise coincides with the conclusion.
              exact h1
            case inr h57 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- One of the premise coincides with the conclusion.
              exact h1
          case inr h58 =>
            -- Disjunctions on the left can always be decomposed.
            cases h46
            case inl h59 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- One of the premise coincides with the conclusion.
              exact h1
            case inr h60 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- One of the premise coincides with the conclusion.
              exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114839601078962734764237753363 : ((((((False ∨ False) → (p2 → (True → False))) ∧ (True → (True ∧ p2))) ∧ p1) ∨ (((p5 → p4) → p4) → ((False ∧ p5) ∧ p1))) ∨ (False → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184134068595778463379027343867 : (((p3 ∧ ((p2 ∧ ((p4 ∨ p4) ∨ (p2 ∧ p2))) ∧ p4)) ∨ True) ∨ (((p5 → ((p2 → False) ∧ p3)) ∨ p3) ∨ ((p2 ∧ p5) ∧ (p2 ∨ p4)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_599322717405525846403271571523 : (((((p1 ∧ p5) ∨ ((p3 ∨ (False ∨ (((p1 ∨ (p4 → p5)) → ((p4 → (True ∧ (p4 ∨ True))) ∧ p1)) ∨ (True ∧ True)))) ∧ p2)) ∧ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324370331231737458809702546508 : (p5 ∨ (((p1 ∧ p4) ∧ ((p5 → True) ∧ p4)) ∨ (((True ∧ p5) ∨ ((False ∨ (False ∨ False)) → ((p3 → p4) → p1))) ∨ ((p1 → p4) → p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- False on the left can always be used.
      apply False.elim h5
    case inr h6 =>
      -- False on the left can always be used.
      apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_708200235292749305797811650187 : ((((p2 → ((p4 ∨ (False ∨ p4)) ∧ (p2 ∧ p1))) ∨ (p5 ∨ ((p5 → p1) ∧ ((((p3 ∧ True) ∧ (False ∧ p4)) → True) → (p1 → p2))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117056955256784773144826500108 : (((p5 ∨ False) → (((True ∨ (p5 ∧ True)) ∧ (((p3 ∨ ((((p4 ∧ False) ∨ p4) → False) ∧ p2)) → p3) → (p5 → False))) ∨ p3)) ∨ (p1 → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_216343994518205317840848015639 : ((p3 → ((p4 ∧ p4) ∧ p1)) ∨ (((False → p2) → (p5 ∨ True)) → (((p3 → ((True ∨ (p1 ∨ p1)) ∨ True)) ∨ (p5 → True)) → (p2 → p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_721364138118936996070581655496 : ((((True ∧ (p5 ∨ (p2 ∨ p3))) → ((False ∨ (p3 ∧ p5)) → ((False ∨ ((((p2 ∧ True) ∧ True) ∧ False) ∧ (p1 ∨ p3))) ∨ (True ∧ p5)))) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- One of the premise coincides with the conclusion.
      exact h9
    case inr h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- True on the right can always be proven directly.
        apply True.intro
        -- One of the premise coincides with the conclusion.
        exact h6
      case inr h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- True on the right can always be proven directly.
        apply True.intro
        -- One of the premise coincides with the conclusion.
        exact h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178312599535867406660413323843 : (((((p4 ∧ p1) ∨ (p3 → (False ∧ (p3 ∧ False)))) ∨ p5) ∨ (True ∨ False)) ∨ (((((p2 ∧ True) → p3) ∨ p5) ∧ p1) ∨ ((False ∧ p2) → False))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_641452851240909205353044205947 : (((((True ∧ True) → (p5 ∨ ((False → ((p5 ∧ (False → True)) ∧ p2)) ∧ (((False ∨ (p1 ∧ (p2 ∨ (p5 ∧ False)))) → p4) ∨ p2)))) → p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192843117218206498805114704859 : (((((p3 ∨ p4) ∨ (p1 ∨ p3)) ∨ p1) ∧ (False → p2)) → (((p2 ∧ ((True → p5) ∧ (p2 ∨ p3))) ∨ (p5 → p5)) → (p3 ∨ (p3 → p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h1.left
      let h10 := h1.right
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h11 =>
        -- Disjunctions on the left can always be decomposed.
        cases h11
        case inl h12 =>
          -- Disjunctions on the left can always be decomposed.
          cases h12
          case inl h13 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h13
          case inr h14 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h15
            -- One of the premise coincides with the conclusion.
            exact h15
        case inr h16 =>
          -- Disjunctions on the left can always be decomposed.
          cases h16
          case inl h17 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h18
            -- One of the premise coincides with the conclusion.
            exact h18
          case inr h19 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h19
      case inr h20 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h21
        -- One of the premise coincides with the conclusion.
        exact h21
    case inr h22 =>
      -- Conjunctions on the left can always be decomposed.
      let h23 := h1.left
      let h24 := h1.right
      -- Disjunctions on the left can always be decomposed.
      cases h23
      case inl h25 =>
        -- Disjunctions on the left can always be decomposed.
        cases h25
        case inl h26 =>
          -- Disjunctions on the left can always be decomposed.
          cases h26
          case inl h27 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h27
          case inr h28 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h22
        case inr h29 =>
          -- Disjunctions on the left can always be decomposed.
          cases h29
          case inl h30 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h22
          case inr h31 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h31
      case inr h32 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h22
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
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h38
        case inr h39 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h40
          -- One of the premise coincides with the conclusion.
          exact h40
      case inr h41 =>
        -- Disjunctions on the left can always be decomposed.
        cases h41
        case inl h42 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h43
          -- One of the premise coincides with the conclusion.
          exact h43
        case inr h44 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h44
    case inr h45 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h46
      -- One of the premise coincides with the conclusion.
      exact h46



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_760844456698820015310417035932 : (((p2 ∧ (p3 ∨ (((False ∧ (p1 ∧ p4)) ∨ ((p2 ∨ (p1 ∨ ((p5 ∨ (p4 ∨ p1)) ∧ ((p5 → True) → True)))) ∧ p5)) ∧ (True ∨ p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165235762271242764229843991120 : ((((p5 → p3) → ((p5 → ((True ∧ (p4 ∨ p1)) ∧ p3)) → (False ∧ True))) ∨ (True → p2)) ∨ (p1 ∨ (False → ((False → p3) ∧ (p5 → p4))))) := by
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
  -- False on the left can always be used.
  apply False.elim h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_669149512300687126814205952159 : (((((((((p3 ∧ p5) ∧ p4) ∨ p1) → p3) → (p3 ∧ (((False → p1) → (False ∧ False)) ∧ (p2 → p2)))) → p1) ∨ (p4 → (p2 → p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148667884388189742300933832496 : (((((p2 ∨ ((p5 ∧ p1) ∨ p1)) ∧ False) ∧ p5) ∨ (p3 ∨ ((True ∨ ((p3 ∧ (False ∧ p1)) ∧ True)) ∨ p5))) ∨ (True ∨ (p5 ∧ (p2 → p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_785055491171837146847766041309 : (((p4 ∨ (((p5 ∨ (((p3 ∧ ((p5 ∧ p2) ∧ p4)) ∨ ((((True ∨ p3) → p2) ∧ p4) ∧ ((p3 ∨ p1) ∨ p1))) → False)) ∧ p2) ∧ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342011590180703941485021982045 : (p2 → ((p4 ∧ ((p4 → (False ∨ p2)) → (((p4 ∧ (p5 ∧ ((p5 ∨ (p2 ∨ (True ∧ True))) ∨ p3))) ∨ p2) ∧ False))) ∨ ((p1 → p1) ∧ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42360149793030672142657934020 : (((p3 ∧ (p5 ∧ (True ∧ (((p4 ∧ p2) ∨ p1) ∧ (((p3 ∧ ((p2 ∨ (True ∧ p1)) ∨ (False ∧ p3))) ∧ p3) ∨ (p3 ∨ p5)))))) ∨ True) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309611268842464978767241331904 : (p2 ∨ (((((p2 ∧ p5) → ((p1 ∨ (((True ∨ p3) → (p4 → (p3 ∨ True))) ∨ p4)) → (True ∧ p5))) ∨ p5) → p5) ∨ (p3 → (False → p1)))) := by
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
theorem thm_5_vars_744746178541986865926103071419 : ((((p3 ∧ p1) → ((p1 → p1) → (((p5 ∧ (p2 ∧ (p2 ∧ (p4 ∨ (p4 ∨ (p4 ∧ ((p3 ∨ p4) ∧ True))))))) ∨ (p4 ∨ p2)) ∨ p1))) ∨ p4) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38857656566263526541162832163 : ((((p1 ∧ (p4 → p2)) ∧ ((True ∧ p5) ∧ (p4 ∨ ((p2 ∧ (True → ((p1 ∧ (False ∧ p5)) ∨ p2))) ∧ ((False ∨ p4) ∧ p3))))) ∧ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186072680433083355091553128974 : ((((((((p4 ∨ p3) ∧ p3) ∧ p1) ∧ p1) ∨ p2) → p2) ∨ p1) → (p1 ∨ (p2 ∨ ((((p1 ∧ (p4 → p2)) → p4) ∧ False) ∨ (True ∨ False))))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190352959307536975280139538330 : (((((False ∨ p1) → p3) → ((False ∧ p1) ∧ p1)) ∨ True) ∨ (True ∧ (p5 → (True → (((False → ((True ∧ p2) ∨ (p5 ∨ p5))) → p4) ∧ p5))))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42695874010668753113505509348 : (((p5 ∨ (((((((p3 ∧ p3) ∧ (p1 ∨ p2)) ∨ (p5 ∧ p3)) ∨ False) ∧ (False ∨ (p4 ∧ (p1 ∨ p5)))) → False) → (p5 ∨ p1))) ∨ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43151527511338580288152235221 : ((((((p4 → p4) ∨ ((p5 → p4) ∨ False)) → (p5 ∧ ((True → p3) ∧ (p1 ∧ (False ∨ ((p5 ∧ True) ∧ (p5 ∧ p2))))))) ∧ p3) → p2) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : ((p4 → p4) ∨ ((p5 → p4) ∨ False)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h4
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- Disjunctions on the left can always be decomposed.
  cases h9
  case inl h10 =>
    -- False on the left can always be used.
    apply False.elim h10
  case inr h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- Conjunctions on the left can always be decomposed.
    let h14 := h12.left
    let h15 := h12.right
    -- Conjunctions on the left can always be decomposed.
    let h16 := h13.left
    let h17 := h13.right
    -- One of the premise coincides with the conclusion.
    exact h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_229894335345679474381385838351 : ((p5 → (True → p3)) ∨ ((((p3 → (False ∧ True)) ∧ p3) → (((False ∨ True) ∧ ((p4 → p5) ∧ (True → False))) ∨ (p1 ∧ False))) ∧ (True ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : p3 := by
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- False on the left can always be used.
  apply False.elim h6
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_972194662864951112149130521275 : ((((True ∨ p4) → (((p4 ∨ False) → (((p3 ∧ (False ∧ ((p1 ∧ p4) → (p1 ∨ p4)))) ∨ ((p4 ∧ p2) ∧ p5)) ∧ (p5 ∨ p4))) ∧ False)) → False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (True ∨ p4) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- False on the left can always be used.
  apply False.elim h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193783626238891617626760400849 : ((p4 ∧ (((True → p4) ∨ (True → p1)) ∨ (p4 ∧ p3))) → (((((True → (((False ∧ p5) ∧ (True ∧ True)) ∨ True)) ∨ True) → p4) → p3) ∨ True)) := by
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
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230905715358018714602053463733 : (((p2 ∧ p4) ∨ p2) → ((((p4 ∨ True) → p5) ∨ (((((p4 → p4) ∧ p1) → (p4 ∨ (True → (False → p1)))) ∨ p1) ∧ p1)) ∨ (False ∨ True))) := by
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
theorem thm_5_vars_56373968921737698114641634786 : (((((p5 ∧ p3) ∧ p1) → p4) → (p5 → ((((((p2 → ((p5 ∨ p5) ∧ p1)) ∧ ((p4 ∨ p4) → False)) → p2) ∨ p4) ∨ True) ∧ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166157368840233735795079318606 : ((False ∧ ((p5 ∧ (((p5 ∧ (True ∧ p4)) → p3) → (p2 ∧ (p1 ∨ p4)))) ∨ (p5 ∨ p4))) ∨ (True ∨ ((p3 ∧ (p1 ∨ (p5 → p4))) ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_664710728387659540908620228944 : ((((False → ((((True ∧ ((p5 ∧ p3) → False)) ∨ p5) ∧ p4) ∨ ((p5 ∧ True) ∨ (p4 → (p1 → ((p4 → p2) ∨ False)))))) → (True → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206112488991152627746881814005 : ((p4 ∧ ((p5 ∨ (False ∧ True)) ∨ True)) ∨ ((True ∧ (p4 ∨ ((p5 → ((p3 ∧ p5) ∧ False)) ∧ ((p2 → (p3 → True)) ∨ p1)))) ∨ (False ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187792955097589606663820328841 : ((p3 → ((p2 ∧ p3) → (p3 → (p5 → (p4 ∨ (p1 ∧ p5)))))) → ((((True ∧ True) ∧ (((True ∧ False) ∨ p5) ∧ p4)) ∧ (p5 → p3)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244357608853205490966190965962 : ((False ∧ False) ∨ (p5 ∨ (((((True → p2) → p2) ∨ ((p4 → (p5 ∧ p5)) ∧ (p5 → p3))) ∨ False) → ((p2 ∧ p4) ∨ (p3 → (p4 ∨ p3)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
      -- Implications on the right can always be decomposed.
      intro h4
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h8
  case inr h9 =>
    -- False on the left can always be used.
    apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_726681650204047051879531184193 : (((((p3 ∧ p2) → p5) ∨ ((((p2 ∧ ((p4 → (p4 ∧ p1)) ∧ (p1 ∨ (p1 → p5)))) ∨ p2) ∧ p1) ∨ (((p5 ∨ p5) ∧ p5) → False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_104548753903145279857773685180 : (((((((p2 ∨ p5) ∧ p4) → p4) → (p3 ∨ ((p4 ∧ False) ∧ ((p3 → (False ∧ p5)) → False)))) ∧ (p4 → False)) ∨ (p5 ∨ True)) ∧ (False → p5)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137946120828839455603022458228 : ((p5 ∨ ((p5 ∨ ((((p2 ∧ p1) ∨ p5) ∨ ((p3 → p1) → (False ∨ False))) ∧ ((p5 ∨ (p5 → p4)) ∨ p5))) ∧ True)) ∨ ((p5 ∧ p5) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322381385090513750733577468553 : (p5 ∨ ((((((p2 ∧ p3) → True) ∨ (False ∨ True)) → (((True ∧ True) → (False ∧ p3)) ∨ p1)) ∧ (True ∧ (p3 ∧ ((p2 → p5) → p4)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213897783463759276214795074606 : (((p4 ∨ (p5 ∧ p4)) ∨ p1) ∨ ((p4 ∨ (((p2 ∨ p1) → (False → p1)) ∨ (((p2 ∨ False) → p2) → (False → (p5 → (p2 ∧ p2)))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_705586774691123299509986307444 : (((((p2 ∧ (((p4 ∧ False) ∧ False) ∨ p3)) → p1) ∧ (True → (p3 ∨ ((((p1 ∨ ((p1 ∧ p3) ∨ (False ∨ p4))) ∧ p5) → p3) ∧ p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172964993047178685493099755624 : ((p4 ∧ (((p3 ∧ p2) ∨ (False ∨ (p2 ∨ (True ∧ (p1 → False))))) ∨ (True ∧ p4))) ∨ ((((p3 → p2) ∧ ((p3 → p2) → p1)) ∧ p2) → p2)) := by
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
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148018143412835028000619782031 : ((((((p2 ∧ (p4 ∨ (p2 ∧ p5))) ∧ p3) → (False ∨ p3)) → ((p5 → p1) → (p2 ∨ p3))) ∨ (p2 → p4)) ∨ ((p5 ∧ p2) ∨ (True ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165387158763456910786394840840 : ((((False ∨ p5) ∧ (((p4 ∧ p1) → p5) → (True ∧ (False ∧ p5)))) ∨ (p3 ∧ (p3 ∧ p4))) ∨ (((True ∨ (False ∧ p2)) → (False → p3)) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44805858635357115825498356506 : (((((p5 → False) → p3) ∧ (((((p1 ∧ (p4 → p2)) → p5) ∧ (p1 → (p2 ∧ p3))) ∧ (False ∨ True)) → ((p5 ∧ p1) → False))) → p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1993756174068162491277817282 : (((((((False ∨ (p1 ∧ (p1 ∧ p3))) ∨ p1) → p2) → p1) ∧ ((True → p4) ∧ (p5 → False))) → p2) → ((p3 ∨ (p1 → p4)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2068037280318747304576886958 : ((((True ∨ ((True ∨ (((p1 ∧ p3) → ((False → p3) ∨ p3)) ∨ False)) ∨ False)) → p2) ∧ False) ∨ ((False ∨ (True ∨ (p2 ∧ False))) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_673133305816219256570969176133 : ((((((False → (p5 → (p2 → p1))) ∨ (p1 ∨ ((False → p4) ∧ p2))) → ((p3 ∨ (p4 → (p2 → p3))) → True)) → ((p2 ∧ True) ∨ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_699038019144602946614971774189 : ((((p2 ∨ (((((p3 → p3) → (p5 ∨ p3)) ∧ p5) → p2) ∨ p1)) ∨ ((p5 ∧ (p3 ∧ p2)) → ((((p5 → p5) ∨ p4) ∨ p5) ∨ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191220796641488205146954347081 : (((p5 ∧ (p1 → p5)) → ((False → (False → p4)) ∧ p2)) ∨ ((p4 ∨ (p4 ∨ ((p1 → ((p5 ∨ (p5 → p1)) ∧ p5)) → (p5 ∨ p4)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158050335748547948003237749971 : ((((p5 ∨ p2) ∧ ((False ∨ False) ∧ p5)) ∨ (p3 ∧ (p1 ∨ (p5 ∨ ((p5 ∨ (p3 ∧ True)) → p2))))) ∨ ((((p5 ∨ False) ∧ p2) ∨ p5) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198647588537710574659596242808 : ((p3 ∨ ((True → p3) ∨ ((p5 ∨ True) ∧ p1))) ∨ ((False → p3) ∧ (((p1 ∨ p4) → (p5 ∧ p2)) ∨ ((p2 ∧ p4) ∨ (True ∨ (p3 → p1)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346339993995283089673485972608 : (p3 → ((((p2 ∧ False) → ((p2 → ((p2 ∨ p3) → p3)) → p3)) → (((((False ∨ p4) → p1) ∨ p5) ∧ (p4 ∨ p1)) ∨ True)) ∨ (False ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_85470912368298373733015435944 : (((p1 → (((p5 ∨ ((p1 ∨ p4) → (p2 ∧ False))) ∨ False) ∨ p5)) ∧ ((p3 → p3) → (((p5 ∨ p5) ∨ p4) ∧ (False ∧ (p4 → False))))) → False) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : (p3 → p3) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h4
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- We need to get the left conjuct of h7 based on <expert-advice>.
  let h8 := h7.left
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_676866280089886508219427911690 : ((((p4 ∨ ((True ∧ (((p1 ∨ (p4 ∨ p3)) ∨ (p5 ∧ (p1 ∧ False))) ∨ ((True ∨ p2) ∨ p3))) ∧ p2)) ∧ (True ∨ ((p3 ∧ True) ∧ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324122818620496757361171456928 : (p5 ∨ ((p4 ∨ (((False ∨ p5) → (False ∧ ((p1 ∧ False) → True))) ∧ p4)) → (False ∨ ((True → (((p4 ∧ (p1 ∨ True)) → p2) ∧ True)) → p2)))) := by
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
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h4 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h5 := h3 h4
    -- We need to get the left conjuct of h5 based on <expert-advice>.
    let h6 := h5.left
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h7 : (p4 ∧ (p1 ∨ True)) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h2
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h8 := h6 h7
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h12
    -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
    have h13 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h12, we can now drive its conclusion.
    let h14 := h12 h13
    -- We need to get the left conjuct of h14 based on <expert-advice>.
    let h15 := h14.left
    -- We want to use the implication h15 based on <expert-advice>. So we show its premise.
    have h16 : (p4 ∧ (p1 ∨ True)) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h11
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h15, we can now drive its conclusion.
    let h17 := h15 h16
    -- One of the premise coincides with the conclusion.
    exact h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113994765136643800802344711302 : (((p2 → ((p4 → (p1 ∧ True)) ∨ (((p2 ∨ (p1 ∨ (False → (p1 ∨ p1)))) ∨ p5) → (p3 ∨ p3)))) ∧ (False → (p4 ∧ p1))) ∨ (True ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156878062980273078257496905782 : ((((p5 → ((p1 ∨ (False ∧ ((p2 ∧ (p5 → (p1 ∨ False))) ∧ (p3 → p3)))) ∨ p2)) ∧ p3) ∨ True) ∨ (p1 → ((False → p1) → (p3 → True)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_224659924213085504785154415829 : ((p3 → (True ∨ p4)) ∧ ((p2 → (((((False ∨ ((p1 ∧ p5) ∧ (p1 ∨ True))) ∨ p2) → p5) → p3) ∨ (p5 ∨ ((False → p2) → p2)))) ∨ p2)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148004228386017153749356541122 : (((((p4 ∨ p1) ∨ ((True ∧ (p2 ∧ False)) → (False → (p5 ∧ (p1 → p3))))) ∧ (p5 ∨ p2)) ∨ (p5 → p3)) ∨ (False ∨ ((False ∧ p4) → p2))) := by
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



