variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177967549602843833073680464921 : ((((p1 ∨ p4) → ((p1 ∨ (p1 ∧ (p3 ∧ (False ∨ p1)))) ∨ p5)) ∨ False) ∨ (((True ∧ True) ∧ p4) ∨ (p4 → (p4 ∧ (p4 ∨ (False → True)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309038447434849440734337092179 : (p2 ∨ (((p1 ∧ False) ∨ ((((p2 ∨ p4) ∨ p5) → ((False ∨ ((p1 ∧ p5) ∨ ((False → True) ∨ True))) → (False ∨ True))) → (p5 ∧ False))) → p4)) := by
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
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h6 : (((p2 ∨ p4) ∨ p5) → ((False ∨ ((p1 ∧ p5) ∨ ((False → True) ∨ True))) → (False ∨ True))) := by
      -- Implications on the right can always be decomposed.
      intro h7
      -- Implications on the right can always be decomposed.
      intro h8
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- False on the left can always be used.
        apply False.elim h9
      case inr h10 =>
        -- Disjunctions on the left can always be decomposed.
        cases h10
        case inl h11 =>
          -- Conjunctions on the left can always be decomposed.
          let h12 := h11.left
          let h13 := h11.right
          -- Disjunctions on the left can always be decomposed.
          cases h7
          case inl h14 =>
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
        case inr h18 =>
          -- Disjunctions on the left can always be decomposed.
          cases h18
          case inl h19 =>
            -- Disjunctions on the left can always be decomposed.
            cases h7
            case inl h20 =>
              -- Disjunctions on the left can always be decomposed.
              cases h20
              case inl h21 =>
                -- Show the right disjunct based on <expert-advice>.
                apply Or.inr
                -- True on the right can always be proven directly.
                apply True.intro
              case inr h22 =>
                -- Show the right disjunct based on <expert-advice>.
                apply Or.inr
                -- True on the right can always be proven directly.
                apply True.intro
            case inr h23 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- True on the right can always be proven directly.
              apply True.intro
          case inr h24 =>
            -- Disjunctions on the left can always be decomposed.
            cases h7
            case inl h25 =>
              -- Disjunctions on the left can always be decomposed.
              cases h25
              case inl h26 =>
                -- Show the right disjunct based on <expert-advice>.
                apply Or.inr
                -- True on the right can always be proven directly.
                apply True.intro
              case inr h27 =>
                -- Show the right disjunct based on <expert-advice>.
                apply Or.inr
                -- True on the right can always be proven directly.
                apply True.intro
            case inr h28 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- True on the right can always be proven directly.
              apply True.intro
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h29 := h5 h6
    -- We need to get the right conjuct of h29 based on <expert-advice>.
    let h30 := h29.right
    -- False on the left can always be used.
    apply False.elim h30



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_131591498238795288446467715853 : ((((p5 → p2) ∧ p3) ∨ (p3 → ((((p2 ∧ (p1 ∨ p1)) → p4) → (((p3 → p1) → (p1 ∨ p2)) ∨ p4)) ∧ True))) ∧ ((True ∨ False) ∨ p5)) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : p3 := by
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h5
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_678603014655636387115333034290 : (((((p3 ∧ False) ∧ ((((p4 ∧ (p1 ∨ p3)) → p3) ∨ p1) ∨ (p5 ∧ ((p2 ∧ p5) → (p2 ∨ False))))) ∨ (((True → p4) ∧ True) → p4)) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_656149448532421556612083539404 : ((((((((True ∨ ((False ∧ False) → p5)) → (p5 ∨ (p4 → p3))) → p4) ∨ p4) ∨ (p5 ∧ ((p2 ∨ p2) ∨ (p5 ∧ True)))) ∨ (False → True)) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_702784566255329929561568152418 : (((((p2 ∨ (True ∨ ((p4 ∧ p3) ∧ False))) → (p4 ∨ p1)) ∨ ((p2 ∧ p5) ∧ ((p1 ∧ p1) ∧ (((p5 → p1) ∧ (False ∧ p2)) ∨ p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152127475666411902415843262495 : ((((False → p5) ∨ (p1 ∨ (p2 ∧ (True ∨ p2)))) ∧ (p3 ∧ (((p1 ∨ (p5 ∨ p4)) → (False ∧ True)) ∧ p5))) → ((p5 ∧ p3) → (p4 ∧ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h1.left
  let h6 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h6.left
    let h9 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
    have h12 : (p1 ∨ (p5 ∨ p4)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h11
    -- We have shown the premise of h10, we can now drive its conclusion.
    let h13 := h10 h12
    -- We need to get the left conjuct of h13 based on <expert-advice>.
    let h14 := h13.left
    -- False on the left can always be used.
    apply False.elim h14
  case inr h15 =>
    -- Disjunctions on the left can always be decomposed.
    cases h15
    case inl h16 =>
      -- Conjunctions on the left can always be decomposed.
      let h17 := h6.left
      let h18 := h6.right
      -- Conjunctions on the left can always be decomposed.
      let h19 := h18.left
      let h20 := h18.right
      -- We want to use the implication h19 based on <expert-advice>. So we show its premise.
      have h21 : (p1 ∨ (p5 ∨ p4)) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h16
      -- We have shown the premise of h19, we can now drive its conclusion.
      let h22 := h19 h21
      -- We need to get the left conjuct of h22 based on <expert-advice>.
      let h23 := h22.left
      -- False on the left can always be used.
      apply False.elim h23
    case inr h24 =>
      -- Conjunctions on the left can always be decomposed.
      let h25 := h24.left
      let h26 := h24.right
      -- Disjunctions on the left can always be decomposed.
      cases h26
      case inl h27 =>
        -- Conjunctions on the left can always be decomposed.
        let h28 := h6.left
        let h29 := h6.right
        -- Conjunctions on the left can always be decomposed.
        let h30 := h29.left
        let h31 := h29.right
        -- We want to use the implication h30 based on <expert-advice>. So we show its premise.
        have h32 : (p1 ∨ (p5 ∨ p4)) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h31
        -- We have shown the premise of h30, we can now drive its conclusion.
        let h33 := h30 h32
        -- We need to get the left conjuct of h33 based on <expert-advice>.
        let h34 := h33.left
        -- False on the left can always be used.
        apply False.elim h34
      case inr h35 =>
        -- Conjunctions on the left can always be decomposed.
        let h36 := h6.left
        let h37 := h6.right
        -- Conjunctions on the left can always be decomposed.
        let h38 := h37.left
        let h39 := h37.right
        -- We want to use the implication h38 based on <expert-advice>. So we show its premise.
        have h40 : (p1 ∨ (p5 ∨ p4)) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h39
        -- We have shown the premise of h38, we can now drive its conclusion.
        let h41 := h38 h40
        -- We need to get the left conjuct of h41 based on <expert-advice>.
        let h42 := h41.left
        -- False on the left can always be used.
        apply False.elim h42
  -- Conjunctions on the left can always be decomposed.
  let h43 := h2.left
  let h44 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h45 := h1.left
  let h46 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h45
  case inl h47 =>
    -- Conjunctions on the left can always be decomposed.
    let h48 := h46.left
    let h49 := h46.right
    -- Conjunctions on the left can always be decomposed.
    let h50 := h49.left
    let h51 := h49.right
    -- We want to use the implication h50 based on <expert-advice>. So we show its premise.
    have h52 : (p1 ∨ (p5 ∨ p4)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h51
    -- We have shown the premise of h50, we can now drive its conclusion.
    let h53 := h50 h52
    -- We need to get the left conjuct of h53 based on <expert-advice>.
    let h54 := h53.left
    -- False on the left can always be used.
    apply False.elim h54
  case inr h55 =>
    -- Disjunctions on the left can always be decomposed.
    cases h55
    case inl h56 =>
      -- Conjunctions on the left can always be decomposed.
      let h57 := h46.left
      let h58 := h46.right
      -- Conjunctions on the left can always be decomposed.
      let h59 := h58.left
      let h60 := h58.right
      -- One of the premise coincides with the conclusion.
      exact h56
    case inr h61 =>
      -- Conjunctions on the left can always be decomposed.
      let h62 := h61.left
      let h63 := h61.right
      -- Disjunctions on the left can always be decomposed.
      cases h63
      case inl h64 =>
        -- Conjunctions on the left can always be decomposed.
        let h65 := h46.left
        let h66 := h46.right
        -- Conjunctions on the left can always be decomposed.
        let h67 := h66.left
        let h68 := h66.right
        -- We want to use the implication h67 based on <expert-advice>. So we show its premise.
        have h69 : (p1 ∨ (p5 ∨ p4)) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h68
        -- We have shown the premise of h67, we can now drive its conclusion.
        let h70 := h67 h69
        -- We need to get the left conjuct of h70 based on <expert-advice>.
        let h71 := h70.left
        -- False on the left can always be used.
        apply False.elim h71
      case inr h72 =>
        -- Conjunctions on the left can always be decomposed.
        let h73 := h46.left
        let h74 := h46.right
        -- Conjunctions on the left can always be decomposed.
        let h75 := h74.left
        let h76 := h74.right
        -- We want to use the implication h75 based on <expert-advice>. So we show its premise.
        have h77 : (p1 ∨ (p5 ∨ p4)) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h76
        -- We have shown the premise of h75, we can now drive its conclusion.
        let h78 := h75 h77
        -- We need to get the left conjuct of h78 based on <expert-advice>.
        let h79 := h78.left
        -- False on the left can always be used.
        apply False.elim h79



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322446976481228980007893112482 : (p5 ∨ (((p3 → (False ∨ (p4 ∨ False))) ∨ ((True ∨ p1) → ((p1 ∧ ((p2 → (True ∨ (p1 ∨ (p4 ∨ p4)))) ∨ p4)) → (p5 ∨ p1)))) ∨ p5)) := by
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
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h7
  case inr h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160779320682418410591405827217 : (((False → (((True ∧ True) ∨ True) ∧ p1)) ∧ (False → (p2 ∧ (True → (((p4 → p4) ∧ p1) → p5))))) → ((((p1 ∨ p5) ∧ p2) ∨ True) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50655175937568134487703673434 : ((((((False ∨ ((p1 ∧ p2) ∧ p4)) ∨ p2) → p1) ∧ (((p5 ∨ (True ∧ (p3 ∧ p5))) → p3) ∧ p3)) → ((True ∨ p1) → (p1 ∧ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64795877478771086808561650216 : ((p2 ∨ (((p3 ∧ p2) ∧ ((True ∨ (p5 → p5)) ∧ (((((p1 ∧ ((p1 ∨ p4) ∧ False)) ∧ (p1 ∧ True)) → True) ∨ False) → p1))) ∨ True)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50667810118759668794217086780 : ((((((p3 ∧ p2) ∨ (True → p5)) ∧ p3) ∨ (((False ∧ False) → ((True ∧ p4) → p4)) ∧ (p5 → p1))) → (p2 → ((p5 ∨ p5) ∨ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39070751573049871033519121563 : ((((False ∨ False) ∨ ((((p2 ∨ True) ∧ ((((p5 → p3) ∧ (p5 ∧ (p4 ∧ p4))) ∨ ((p1 ∧ p1) ∧ True)) → False)) ∨ p5) ∨ p3)) ∧ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117228940897172822443211465140 : ((True ∧ (True ∧ (((p2 ∨ (((p1 → (p4 → True)) → (p1 → p2)) ∧ (p5 → p2))) ∧ (p1 ∧ p2)) ∨ ((p2 ∨ p4) → p4)))) ∨ (p3 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47692495417779439845512526443 : ((((p2 ∨ ((((p3 ∨ ((p3 ∧ p3) ∨ (p1 ∨ (p4 ∧ (True → p1))))) ∨ p1) ∨ p4) ∧ ((True ∨ p5) ∨ True))) ∧ p4) → (p2 ∧ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205061304754289558856480574891 : (((p2 → (p1 ∧ (p1 → False))) → p3) ∨ ((((True ∨ p1) ∨ p2) ∧ p5) ∨ ((p2 ∨ p3) → (((p5 ∨ (True ∧ True)) ∨ (True ∨ p5)) ∨ p4)))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157477976775615130080429202113 : (((((p1 ∨ p4) ∧ ((p1 → (p3 ∨ p1)) → ((p2 ∨ p1) ∧ p1))) ∨ (False → False)) ∨ (p5 → True)) ∨ (((p3 ∧ (p3 ∧ p5)) ∨ p3) ∧ p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167603898675631213206221889488 : (((True → (((p2 ∧ (p2 ∧ (((False → p3) → p2) ∧ False))) ∧ p1) ∧ True)) ∨ (p4 ∨ True)) → ((((p3 ∧ p2) → p3) → p4) ∨ (False → p3))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- False on the left can always be used.
      apply False.elim h6
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- False on the left can always be used.
      apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161076011933604237824168431134 : (((True ∧ p3) ∧ (((p3 ∨ p3) ∨ (False ∧ (p4 ∧ (False ∨ p2)))) ∨ (p5 → (p3 → (p3 ∧ p4))))) → ((p3 → ((True ∧ p1) ∨ p2)) ∨ True)) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
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
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- False on the left can always be used.
      apply False.elim h11
  case inr h13 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_183987236073120189907237620405 : (((((((False → True) ∨ p2) ∨ False) → (False ∧ p2)) ∧ p2) ∨ p4) ∨ (False → (p5 ∧ ((((p1 ∧ (p4 ∨ p2)) → p4) ∨ p3) → (p1 ∧ True))))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- False on the left can always be used.
    apply False.elim h1
  case inr h4 =>
    -- False on the left can always be used.
    apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_856499915203724931823623778657 : (((((((p4 ∨ False) ∨ (p2 ∨ p5)) ∧ ((p1 → False) ∨ ((p2 ∧ (p3 → p3)) ∧ (True → (((p2 ∧ p1) ∨ False) ∧ False))))) ∨ True) → False) → p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((((p4 ∨ False) ∨ (p2 ∨ p5)) ∧ ((p1 → False) ∨ ((p2 ∧ (p3 → p3)) ∧ (True → (((p2 ∧ p1) ∨ False) ∧ False))))) ∨ True) := by
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
theorem thm_5_vars_709778675313528393838394894821 : ((((p1 → (p1 → (((p5 → p3) → True) ∨ p1))) → (((p3 → False) ∨ (p5 → p5)) ∨ (True ∧ (p2 ∧ ((p3 ∧ (p3 ∨ p3)) → p4))))) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115757594613851027453252874069 : (((p5 ∧ ((False ∨ p3) → (p4 ∨ p5))) → (False ∨ ((p2 → p1) → (((p1 ∧ p1) → (False ∧ (False → (False ∨ True)))) ∧ p1)))) ∨ (False ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147471934180231346420666747471 : (((p1 ∧ ((p4 ∨ ((((False ∧ p5) ∨ p2) ∧ p3) ∨ ((p1 ∨ (True ∧ p1)) ∧ p5))) ∨ (p3 ∨ p5))) ∨ True) ∨ ((p4 ∨ p1) ∧ (False ∨ p4))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_790373853515862663456786629441 : (((p5 ∨ (p4 ∧ (((((p2 ∨ p3) → True) ∨ False) → ((p1 ∧ p1) ∧ p5)) ∨ (p2 ∧ (((p1 ∧ p5) ∨ p3) ∧ (p4 → (p4 → True))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_229169213525079381678424787893 : ((True → (p3 ∨ p3)) ∨ ((p2 ∧ (p3 ∧ False)) ∨ (((False → (False ∧ ((p3 ∧ False) ∨ p4))) ∨ True) ∨ (p4 ∧ (p5 → ((p1 → p4) ∨ True)))))) := by
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
theorem thm_5_vars_137874443796236816051490072437 : ((p4 ∨ (((((p1 ∧ p1) → (False ∨ (p1 ∧ ((((p5 ∧ False) ∨ p5) ∨ False) ∧ (False ∨ p2))))) ∧ True) ∧ p1) ∧ True)) ∨ (False → (p3 ∧ p2))) := by
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
theorem thm_5_vars_148208541116081563944068306337 : (((p2 ∨ ((p1 ∨ (p3 ∧ True)) → (((p4 ∨ (p4 ∨ (False → False))) ∧ p5) ∨ p1))) ∧ (p2 ∧ (p2 → False))) ∨ (True ∧ (False ∨ (p2 → True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_348502191018593997123029804151 : (p3 → (p3 ∧ (((p5 ∧ (((((False → ((p4 → True) ∨ (p4 ∨ False))) ∧ p1) ∧ p1) → True) ∨ p5)) → False) ∨ (p3 ∨ ((False ∧ p4) → p1))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119227698180897119902250235721 : ((p2 → ((False ∨ p2) ∧ ((((p2 → (True ∧ (((p4 ∧ p4) ∧ True) ∨ p3))) ∨ ((False ∨ p3) → (p5 → p1))) ∨ p4) ∨ True))) ∨ (p1 ∧ p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113491081493602003798014342647 : ((((p4 → (p3 ∧ ((False → ((p3 ∧ p2) → False)) → (((p2 ∨ p4) → (False ∧ p3)) ∨ p4)))) → (p1 ∧ False)) ∨ (p1 ∨ p2)) ∨ (True ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45349480772824308191197396933 : (((p4 ∧ (((False → p1) ∧ ((((((p2 ∧ p3) ∨ p2) ∨ (((p5 ∨ (p2 ∧ p3)) ∨ True) ∨ p5)) ∨ False) → p3) ∨ p5)) ∨ p1)) → p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_662106105925280795400094811107 : (((((((p4 → True) → p4) ∨ ((p4 → p1) ∧ (p1 ∧ (p1 ∧ p3)))) ∨ (p5 → ((False ∨ (p2 ∧ p3)) ∨ (p3 ∧ p4)))) → (False ∧ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50730410629069718358771629574 : (((True ∧ (((((False → p4) → p4) → (p5 → (True ∨ p5))) ∧ ((p4 ∨ (p4 → True)) ∧ p2)) → p1)) → ((p1 ∧ (p4 ∨ p3)) → p1)) ∨ p1) := by
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
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h1.left
    let h10 := h1.right
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49674685169439317730077848198 : ((((p1 ∧ True) ∧ (((p3 ∨ ((((True ∨ p1) ∧ ((True ∧ p3) ∨ p4)) ∧ p1) → p1)) ∧ p1) ∨ (p2 → p5))) → ((p5 ∨ p4) → p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340884987537726303363316453671 : (p2 → (((p3 ∧ (False ∧ (((True → p1) ∧ True) ∨ (p3 ∧ (p3 → (p5 ∨ p4)))))) ∧ ((((p4 → False) ∨ p4) → (True ∨ p2)) ∧ p3)) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310404536474393598532061808069 : (p2 ∨ ((p4 ∧ (False ∧ (p3 ∧ (p2 ∧ (True ∧ p4))))) ∨ ((((p5 ∧ (True ∨ (((p2 ∧ p2) ∧ p3) ∨ (p1 → True)))) ∧ p4) ∨ p4) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_591824809446688022486143562 : ((((p2 ∧ p4) ∨ ((False ∧ ((((((p3 → False) ∧ (p3 ∨ (True ∨ p5))) ∧ p5) → p1) → (False ∧ p3)) ∨ p5)) → True)) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49957395626391951895315308650 : ((((((p4 → (p4 ∧ (p5 ∧ p1))) → (True → p1)) → ((True ∧ (p2 → False)) ∧ False)) → (p1 → p2)) ∧ ((p5 → p2) → (p3 ∨ True))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : ((p4 → (p4 ∧ (p5 ∧ p1))) → (True → p1)) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h3
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- False on the left can always be used.
  apply False.elim h7
  -- Implications on the right can always be decomposed.
  intro h8
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53919337822558023503307436357 : (((p2 ∨ (((p1 ∨ p4) ∧ ((p1 → p1) → p2)) ∨ True)) ∨ (((p3 ∧ (p5 ∨ (((p4 ∨ (p3 ∨ p4)) ∧ p5) → True))) ∧ p5) → p2)) ∨ p1) := by
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
theorem thm_5_vars_149315555083961515865575144232 : (((p2 ∧ p5) → ((p1 → (p5 ∨ p5)) → (((True → p2) → False) ∨ ((p1 ∨ True) ∨ (p2 ∧ (p3 ∧ p2)))))) ∨ (False ∨ (p5 → (True → p4)))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_209268886405311102834180906323 : ((True → (((True ∧ False) ∧ True) ∧ p3)) → ((((((((p4 → p3) ∨ p4) ∨ (p1 ∧ p5)) ∨ True) → p5) ∨ p2) ∧ True) ∧ (True ∧ (p2 ∧ False)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the left conjuct of h3 based on <expert-advice>.
  let h4 := h3.left
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- False on the left can always be used.
  apply False.elim h6
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h7 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h8 := h1 h7
  -- We need to get the left conjuct of h8 based on <expert-advice>.
  let h9 := h8.left
  -- We need to get the left conjuct of h9 based on <expert-advice>.
  let h10 := h9.left
  -- We need to get the right conjuct of h10 based on <expert-advice>.
  let h11 := h10.right
  -- False on the left can always be used.
  apply False.elim h11
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h12 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h13 := h1 h12
  -- We need to get the left conjuct of h13 based on <expert-advice>.
  let h14 := h13.left
  -- We need to get the left conjuct of h14 based on <expert-advice>.
  let h15 := h14.left
  -- We need to get the right conjuct of h15 based on <expert-advice>.
  let h16 := h15.right
  -- False on the left can always be used.
  apply False.elim h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_621790803071509471289185882005 : ((((p1 ∧ (((True ∨ (((p5 ∨ ((p5 ∧ p1) ∧ False)) → p1) ∧ (p5 → p5))) → ((p1 → (p2 → False)) ∧ p2)) ∧ (p2 → p1))) ∨ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67330440313832982583978374659 : ((p1 → (((((p4 ∨ (p4 ∨ (p2 ∨ p5))) → False) → ((((p5 → p5) ∨ p2) ∨ (p3 → (p5 → p3))) → (p2 ∨ p2))) → False) ∨ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2661468776273142481058107686 : (((p4 ∨ p3) ∧ ((p2 ∨ p1) ∨ False)) ∨ (False → ((p4 ∨ p4) → ((p2 → (p3 → (False ∧ (p5 → ((False ∨ True) → False))))) ∨ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- False on the left can always be used.
    apply False.elim h1
  case inr h4 =>
    -- False on the left can always be used.
    apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_893109219898022943018530677539 : (((((((p5 ∨ p5) → ((((True ∧ True) ∨ p2) ∨ p4) → p2)) ∨ p4) ∧ ((True ∧ p2) ∧ (True → (p1 ∨ False)))) ∧ (p5 → (p2 ∨ p4))) → p1) ∧ True) := by
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
  cases h4
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h7.left
    let h10 := h7.right
    -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
    have h11 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h8, we can now drive its conclusion.
    let h12 := h8 h11
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h13 =>
      -- One of the premise coincides with the conclusion.
      exact h13
    case inr h14 =>
      -- False on the left can always be used.
      apply False.elim h14
  case inr h15 =>
    -- Conjunctions on the left can always be decomposed.
    let h16 := h5.left
    let h17 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h18 := h16.left
    let h19 := h16.right
    -- We want to use the implication h17 based on <expert-advice>. So we show its premise.
    have h20 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h17, we can now drive its conclusion.
    let h21 := h17 h20
    -- Disjunctions on the left can always be decomposed.
    cases h21
    case inl h22 =>
      -- One of the premise coincides with the conclusion.
      exact h22
    case inr h23 =>
      -- False on the left can always be used.
      apply False.elim h23
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263730645801189104608828369984 : (True ∧ (((((p4 ∧ p2) → (p1 ∧ p3)) ∨ (p4 ∧ (True ∧ p1))) ∧ ((p3 ∧ p3) → (p5 ∨ p1))) → (((p1 → p3) ∨ True) ∨ (p3 ∨ False)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345269285230729777000428681245 : (p3 → ((p5 ∨ (((p1 ∧ p3) ∨ ((p5 ∧ (p5 ∧ False)) ∨ ((True ∨ False) ∧ p4))) ∨ (p3 ∨ ((p1 ∧ p4) ∧ ((p2 ∨ p1) ∨ False))))) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_667074836545292839287869060858 : (((((p2 ∧ (p2 ∧ p3)) ∧ ((p4 → ((p3 ∨ (False ∨ ((p4 ∨ (p1 ∧ p5)) ∧ p5))) ∨ (p2 → p4))) → p3)) ∧ (p5 → (False ∧ True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_201062923142797041227483766761 : ((p5 ∨ ((p4 ∧ ((False ∧ p2) ∨ False)) ∨ p4)) → ((p1 ∨ (False ∨ (True ∧ p2))) ∨ ((False ∨ ((p1 → (p3 ∨ (p5 ∨ p5))) → True)) ∨ p2))) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Conjunctions on the left can always be decomposed.
        let h9 := h8.left
        let h10 := h8.right
        -- False on the left can always be used.
        apply False.elim h9
      case inr h11 =>
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
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156734141823526047204093076610 : ((((p1 ∨ (p3 ∨ (True → p1))) ∧ ((False ∧ (False → (p4 ∨ ((p2 → p3) → p1)))) ∧ p1)) ∧ False) ∨ ((p5 → (p4 ∧ p1)) ∨ (True ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_614280985634119917090675301702 : (((((((p2 ∧ (p5 → (False → (p4 ∧ p5)))) → p2) ∧ ((p1 ∨ ((p1 ∨ True) → p4)) ∨ (True ∧ p3))) → ((False ∨ p4) ∨ p4)) ∨ True) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_84758067024066356133137472018 : ((((p3 ∧ (p4 → (True ∧ p2))) ∧ ((p1 ∨ True) ∧ (p4 → (True ∧ p1)))) ∧ ((True → ((p2 ∧ p3) ∧ (p4 ∧ p1))) ∧ (p5 ∧ p5))) → p1) := by
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
  let h8 := h5.left
  let h9 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h3.left
    let h12 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h13 := h12.left
    let h14 := h12.right
    -- One of the premise coincides with the conclusion.
    exact h10
  case inr h15 =>
    -- Conjunctions on the left can always be decomposed.
    let h16 := h3.left
    let h17 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h18 := h17.left
    let h19 := h17.right
    -- We want to use the implication h16 based on <expert-advice>. So we show its premise.
    have h20 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h16, we can now drive its conclusion.
    let h21 := h16 h20
    -- We need to get the right conjuct of h21 based on <expert-advice>.
    let h22 := h21.right
    -- We need to get the right conjuct of h22 based on <expert-advice>.
    let h23 := h22.right
    -- One of the premise coincides with the conclusion.
    exact h23



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300683437591869551568880245778 : (False ∨ (((p1 ∨ (p3 ∨ p3)) ∧ ((p3 ∧ (p4 ∧ ((False ∧ ((p3 ∨ False) → p2)) ∧ p2))) ∧ p5)) ∨ (((p2 ∧ False) ∧ (False → p5)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_719451532601970295802350981277 : ((((p1 ∨ ((p1 → True) → False)) ∨ (False ∨ (((True ∨ p3) → (False ∨ (p2 ∧ ((p5 ∧ (p4 ∧ (p5 ∧ False))) ∨ (False ∧ p2))))) → p2))) ∨ p2) ∧ True) := by
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
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (True ∨ p3) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
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
    cases h7
    case inl h8 =>
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
    case inr h15 =>
      -- Conjunctions on the left can always be decomposed.
      let h16 := h15.left
      let h17 := h15.right
      -- False on the left can always be used.
      apply False.elim h16
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_3985665072749903213314884990 : (p1 ∨ ((p3 ∧ (((((p5 ∨ p2) ∧ (True ∨ p2)) ∨ p1) ∨ p5) ∨ p3)) ∨ (True ∧ ((False ∧ (p4 ∨ (False ∨ p1))) ∨ (True ∨ False))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_457278853766290633773204902484 : ((((((False → ((p4 → ((False ∨ p4) ∧ p4)) ∧ (p4 → p4))) → (False ∧ (p2 → True))) ∨ True) ∨ (((p1 ∨ False) ∧ (p2 ∧ p5)) ∨ p4)) ∧ True) ∧ True) := by
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
theorem thm_5_vars_668923655633097995329799733700 : (((((p5 ∧ (((((((((p1 ∨ p3) ∨ p5) → p1) ∨ p3) ∨ p1) → (p5 ∨ p4)) → p2) ∨ p5) → p3)) ∨ p4) ∨ ((False ∧ False) → True)) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219829781935671646485246523561 : ((p3 → ((p3 ∨ p3) ∨ True)) → ((p2 → ((p1 → False) ∧ False)) ∨ ((p2 → (False → (p1 ∨ p4))) → ((p2 → ((p2 → p2) ∨ False)) ∨ p5)))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h4
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321508449189593406876372516421 : (p4 ∨ (p1 → ((False ∧ p5) ∨ ((False ∧ (((p5 ∨ p4) ∨ True) ∧ ((True ∧ ((True ∨ p5) ∨ (p5 → p3))) ∧ True))) ∨ ((True ∨ True) ∨ p1))))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_738854629658223777189524136894 : ((((p3 ∧ True) ∨ ((((((((False ∧ (False ∧ False)) ∧ False) → p3) ∧ True) → True) ∨ (True ∨ (p2 → False))) → ((p5 ∨ True) ∧ p4)) ∧ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41405960777383569476783703775 : (((((p5 ∧ (((False → ((True ∧ p2) ∨ (p4 ∨ p4))) ∨ p2) ∧ False)) ∨ p3) ∨ (False ∧ ((p4 → (p1 → (p4 → True))) → p3))) ∨ True) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_254348437354391196033418062802 : ((p2 ∧ p4) → ((((((((p1 ∨ p5) ∧ (p4 → (p2 ∧ False))) → p4) → False) ∨ p2) ∧ p1) ∨ (True ∧ p2)) ∨ (((p2 → p3) ∨ p5) ∧ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51087745475864130018290391458 : ((((((((p5 ∧ p4) ∧ ((p5 → (False ∨ p3)) ∨ p2)) ∨ p1) ∨ (p5 ∧ p3)) ∨ p3) ∧ p5) ∨ (((False ∧ p5) ∨ (False → p3)) ∨ p4)) ∨ False) := by
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
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150148388714495637642172366958 : ((p1 → (((((((((p4 ∨ p1) ∧ p2) → p1) → False) ∧ ((True ∨ p2) ∧ False)) ∨ p1) → False) ∨ p4) → p2)) ∨ ((p4 ∧ (p1 ∨ p3)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191117016704773516593188789508 : (((p2 ∨ (p3 ∧ p5)) ∧ (((p4 ∧ p3) → p5) ∧ p1)) ∨ (True → ((False ∧ p4) → (p4 ∨ (((((p4 ∨ True) → p3) ∨ p1) ∧ p4) → True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47783526408843663503060948603 : (((((((p3 ∧ ((False → p4) ∨ ((p2 → p5) ∨ p3))) ∨ (False → (p4 → p5))) ∨ ((p1 ∨ p5) ∧ p1)) ∧ p2) → p1) → (p1 ∧ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185357317942316727010527140424 : ((p4 ∧ (p1 ∧ (p3 ∨ (p3 ∨ (p1 ∨ (p2 ∨ (p1 ∧ True))))))) ∨ ((p5 ∧ (((((p5 ∨ (False ∨ p2)) ∧ p3) → p2) → False) → False)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_182936671824166594040905095250 : (((p5 → (False ∨ p2)) → ((p3 ∨ ((True → False) ∧ p5)) ∨ True)) ∧ ((((((p3 ∧ p1) ∨ ((p3 → p5) → p2)) → p5) ∧ False) → p4) ∨ p2)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137197198719602054566904777152 : ((False ∧ (p2 ∧ (((p4 ∧ (p1 ∧ ((((p3 ∧ p5) ∧ ((p3 ∧ (False → False)) → True)) ∧ p2) → False))) ∧ p5) ∨ p2))) ∨ (p4 → (True ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134182138056473071670548941107 : ((((p5 ∧ (p4 ∨ (True ∧ ((True → ((p3 ∧ p2) ∧ True)) ∧ p3)))) ∧ (p1 ∨ ((True ∧ False) ∨ (True → p5)))) ∨ p3) ∨ (p4 ∨ (False → False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168731894572764898136228867336 : ((False ∨ (((((False → p2) → (p1 ∧ (p1 ∨ ((p2 → p3) ∧ p5)))) ∧ p1) → p3) ∨ p2)) → (p5 ∨ ((p1 ∨ False) ∨ (p5 ∨ (True ∨ p5))))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
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
theorem thm_5_vars_702202262311508256713739659608 : ((((((p5 ∨ (((p4 ∨ p2) ∧ False) ∨ p1)) ∨ False) ∧ p4) ∨ (False → (p3 ∨ ((True ∧ p1) → (p1 ∧ (p2 → (p3 ∧ (p4 → p1)))))))) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40630605589291699791316575690 : (((((((p2 → p2) ∧ ((p3 ∨ (p3 → True)) ∧ ((p2 ∧ (((p2 ∧ False) → p3) ∨ (p2 → p4))) ∨ True))) → p2) → p2) → p3) ∨ True) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260771855676532774807887564299 : ((p3 → p5) → ((p5 → ((((((False → (p5 ∧ False)) ∧ p5) ∨ ((True ∨ p1) → False)) ∧ (((p5 ∨ p2) → False) ∧ p3)) ∨ p5) ∧ True)) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174965925773247028850759717234 : ((True ∧ ((True ∧ p2) ∨ ((True → (((p2 ∨ p1) → (p4 ∨ True)) ∨ p5)) ∨ False))) → (((True ∨ p4) ∨ p3) → (((p1 ∧ p4) ∨ p2) ∨ True))) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h5 := h1.left
      let h6 := h1.right
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Conjunctions on the left can always be decomposed.
        let h8 := h7.left
        let h9 := h7.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h10 =>
        -- Disjunctions on the left can always be decomposed.
        cases h10
        case inl h11 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h12 =>
          -- False on the left can always be used.
          apply False.elim h12
    case inr h13 =>
      -- Conjunctions on the left can always be decomposed.
      let h14 := h1.left
      let h15 := h1.right
      -- Disjunctions on the left can always be decomposed.
      cases h15
      case inl h16 =>
        -- Conjunctions on the left can always be decomposed.
        let h17 := h16.left
        let h18 := h16.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h19 =>
        -- Disjunctions on the left can always be decomposed.
        cases h19
        case inl h20 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h21 =>
          -- False on the left can always be used.
          apply False.elim h21
  case inr h22 =>
    -- Conjunctions on the left can always be decomposed.
    let h23 := h1.left
    let h24 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h24
    case inl h25 =>
      -- Conjunctions on the left can always be decomposed.
      let h26 := h25.left
      let h27 := h25.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h28 =>
      -- Disjunctions on the left can always be decomposed.
      cases h28
      case inl h29 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h30 =>
        -- False on the left can always be used.
        apply False.elim h30



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313047439978851361299616465302 : (p3 ∨ (((((p4 ∨ p5) ∧ ((p1 ∧ (p5 ∧ (p2 → (p5 ∨ True)))) → p5)) ∧ ((p5 ∧ (p3 ∨ True)) ∨ (True → (True ∨ p1)))) → p1) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199821028576082143074264091521 : ((((p2 → (p4 → p4)) → False) ∧ (p3 ∨ p4)) → (((((p1 → p5) ∧ p1) ∨ (p3 ∧ ((p2 ∨ p4) → p3))) ∨ (True ∨ p4)) ∨ (p3 ∨ p2))) := by
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
    exact h4
  case inr h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317824498840249628825225499930 : (p4 ∨ ((((p4 ∧ (p3 ∨ p2)) ∧ p4) → ((((p1 ∨ p4) → (p2 ∨ p2)) ∨ (True → True)) → (p1 ∨ (p1 → (False ∨ (p4 → p4)))))) ∨ p1)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h4 := h1.left
    let h5 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h9
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- One of the premise coincides with the conclusion.
      exact h10
    case inr h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h12
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h13
      -- One of the premise coincides with the conclusion.
      exact h13
  case inr h14 =>
    -- Conjunctions on the left can always be decomposed.
    let h15 := h1.left
    let h16 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h17 := h15.left
    let h18 := h15.right
    -- Disjunctions on the left can always be decomposed.
    cases h18
    case inl h19 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h20
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h21
      -- One of the premise coincides with the conclusion.
      exact h21
    case inr h22 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h23
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h24
      -- One of the premise coincides with the conclusion.
      exact h24



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_33520119275067732320739665457 : ((p4 ∨ ((True ∨ p5) → ((False ∧ (p3 ∨ (True ∨ True))) ∨ ((p1 ∨ p1) ∨ ((((p1 ∧ p2) → p1) ∨ ((p2 ∨ False) → True)) ∨ p5))))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340811834599966111858620770203 : (p2 → ((((p1 → ((((p1 ∧ p1) ∧ p2) ∧ (p1 → (p4 ∧ True))) → p3)) → (((p3 ∧ (p2 ∨ False)) ∧ p4) → p4)) ∧ (False → p4)) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h9 =>
    -- False on the left can always be used.
    apply False.elim h9
  -- Implications on the right can always be decomposed.
  intro h10
  -- False on the left can always be used.
  apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_680812372087245810539264169200 : ((((((p1 ∧ p3) ∨ False) ∨ ((p3 ∨ (True → (True ∧ False))) → ((False ∧ p2) ∨ ((True ∧ False) → False)))) → (((p4 ∨ True) ∧ p2) ∨ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_140127532627022432701732845350 : ((((((p1 ∧ p4) → p5) → (p3 → (p5 ∨ (p2 → ((p1 ∨ (p1 → p1)) ∨ (p5 ∨ False)))))) ∧ False) → (p5 ∨ p3)) → (p5 ∨ (p1 → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157231773575670063630562170856 : (((((False ∧ p5) → ((((p2 ∧ p5) ∨ False) → True) → p1)) ∨ ((p1 → (p5 ∨ False)) ∨ p4)) → False) ∨ (p4 → ((p4 → p1) → (p1 ∨ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : p4 := by
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135211302016082614868878055876 : (((((p1 → (p4 ∨ (p4 ∧ ((p4 ∨ False) ∨ (True ∧ p5))))) ∧ (p4 → p4)) ∨ ((p1 ∧ p4) → p4)) → (p3 ∧ p5)) ∨ (True ∨ (p3 ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_139447141577342677578321095278 : (((((p3 → (p3 → (((p2 ∧ (p1 ∧ False)) ∨ p3) ∧ (((p3 ∨ p1) ∧ (True ∧ p3)) ∧ True)))) ∨ p5) ∨ False) → p4) → ((p4 → False) → p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : p4 := by
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h4 : (((p3 → (p3 → (((p2 ∧ (p1 ∧ False)) ∨ p3) ∧ (((p3 ∨ p1) ∧ (True ∧ p3)) ∧ True)))) ∨ p5) ∨ False) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h5
      -- Implications on the right can always be decomposed.
      intro h6
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h5
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- One of the premise coincides with the conclusion.
      exact h5
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h7 := h1 h4
    -- One of the premise coincides with the conclusion.
    exact h7
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h8 := h2 h3
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61259284161793191709447930123 : ((False ∧ (False ∨ ((p5 ∨ ((False → p5) ∧ (False ∧ (p4 → (p1 → (((p2 → (p3 ∨ p4)) → p5) → p3)))))) ∨ (p4 ∧ (False → p2))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308611895286666515844692408996 : (p2 ∨ (((p5 → p2) ∧ ((p1 → ((True → (True → (p5 ∧ (p2 ∧ (True → p1))))) ∧ (((False ∨ (False ∧ p4)) ∨ False) ∨ False))) ∧ p1)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231469500482786114308294903479 : (((p3 → True) ∨ p4) → (((False ∨ p5) ∨ ((p2 ∧ (p3 ∨ (((p1 ∧ p5) ∧ ((True ∧ p3) → (p3 ∨ p2))) → True))) ∨ (p3 ∨ True))) ∨ p5)) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
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
theorem thm_5_vars_324305769928876356249430139105 : (p5 ∨ ((p3 ∧ (p3 → (True ∧ (True ∨ (p3 ∨ p2))))) → ((((((True ∨ p5) ∨ (p4 ∨ p4)) → ((True ∨ True) ∧ p1)) ∨ True) → p4) → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h5 : ((((True ∨ p5) ∨ (p4 ∨ p4)) → ((True ∨ True) ∧ p1)) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h5
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165864738400468410576966839470 : (((p4 ∨ (p4 ∧ p2)) ∨ ((((p3 → (True ∧ (p1 → p4))) ∨ False) ∨ False) ∨ (False → False))) ∨ (((((p2 → True) ∨ p3) ∨ p5) ∨ False) ∧ p1)) := by
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
theorem thm_5_vars_328311152076862495183319645080 : (True → ((p5 ∨ (p2 ∨ ((((p3 ∨ False) ∨ (p2 ∧ (p1 ∨ (p2 ∨ True)))) → (False ∧ p4)) ∨ (p3 ∨ True)))) ∨ ((p4 ∧ p1) ∧ (True ∧ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
theorem thm_5_vars_311220547683634051446848675230 : (p2 ∨ ((False → p4) → ((p5 → ((p5 ∧ False) ∨ (p4 → p1))) ∨ (((True ∧ (p2 ∧ (((p1 ∧ p3) → (p1 ∧ p4)) ∧ p1))) ∧ True) → True)))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213410866572420570706149575309 : (((p2 ∨ (p1 ∧ p5)) ∧ p5) ∨ ((((p5 → (p3 ∧ False)) → ((p1 → ((p3 ∨ p5) ∧ (p2 ∧ p3))) ∨ p1)) → p4) → ((False ∧ p2) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161611642759021647189643726073 : ((False ∨ ((p1 ∨ (((p1 ∨ ((p1 ∨ p3) → p2)) → p3) ∨ ((True ∧ p1) → True))) ∧ (p4 ∧ True))) → (True → (((p4 → p5) → p2) ∨ True))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h6.left
      let h9 := h6.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- Conjunctions on the left can always be decomposed.
        let h12 := h6.left
        let h13 := h6.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h14 =>
        -- Conjunctions on the left can always be decomposed.
        let h15 := h6.left
        let h16 := h6.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_69390993557122858979609714070 : ((p5 → (p3 → (((False ∧ ((p4 ∨ (False ∨ ((((p3 ∨ p1) → ((p2 ∨ True) ∧ p2)) ∧ True) ∨ p3))) → (p1 ∨ p2))) ∨ True) ∨ p4))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200348346326825717199940062372 : (((p5 ∨ p1) ∧ (((p1 ∧ True) ∧ p5) ∨ p1)) → ((True → (p4 → (False ∨ ((p2 ∧ ((p4 ∧ (p1 ∧ (p1 ∧ p4))) ∨ True)) ∧ False)))) ∨ True)) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Conjunctions on the left can always be decomposed.
      let h8 := h6.left
      let h9 := h6.right
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
    cases h3
    case inl h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h12.left
      let h14 := h12.right
      -- Conjunctions on the left can always be decomposed.
      let h15 := h13.left
      let h16 := h13.right
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
theorem thm_5_vars_111854732325785841342437730817 : ((((p1 ∨ ((True → p4) ∨ (p3 → (p3 ∨ (True ∧ ((p5 ∧ (p1 ∧ p4)) → (p4 ∧ p3))))))) → ((True → False) → p1)) ∨ p4) ∨ (p2 ∧ True)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h6 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h7 := h2 h6
      -- False on the left can always be used.
      apply False.elim h7
    case inr h8 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h9 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h10 := h2 h9
      -- False on the left can always be used.
      apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305488206359568974929649357213 : (p1 ∨ ((((p1 ∨ (p2 → (p1 ∧ p3))) ∨ ((True ∧ False) ∧ (p4 ∨ p3))) ∧ p5) ∨ ((p5 ∧ True) ∨ (False → ((p5 ∧ True) ∧ (True ∨ p2)))))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_349079506301962705766221040403 : (p3 → (p5 ∨ (True → (p4 ∨ (((((p1 ∧ p1) ∧ (p5 ∨ p2)) ∧ ((p2 ∧ p2) → (p5 ∨ (False ∨ True)))) ∧ p3) ∨ ((p5 → p5) ∨ p2)))))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h3



