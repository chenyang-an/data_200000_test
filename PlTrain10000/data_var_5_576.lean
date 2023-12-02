variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205856085939890236060253342380 : (((p4 → False) → ((p5 ∧ p5) ∧ p4)) ∨ ((p1 ∧ p5) → ((p5 ∧ p2) → (((p4 ∨ (p1 ∨ ((p5 ∧ True) → (False → False)))) ∨ p3) ∨ p3)))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_711699744951640712490713628670 : ((((p5 → ((p3 ∨ False) → (True ∨ p1))) ∧ (((False ∨ (p1 → (True ∨ (p5 ∧ ((True ∨ p3) ∨ (p4 ∨ p3)))))) ∨ p5) → (False ∨ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47069352954121508030185684871 : ((((p1 ∧ ((p3 → (((p3 ∧ p2) → p4) ∧ False)) ∧ (((p5 ∧ False) ∧ (True ∨ (False ∨ False))) ∧ p2))) ∨ (p4 ∧ p3)) ∨ (True ∨ p3)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_661710265393882799703678181483 : (((((((((((p1 → p5) → True) ∧ True) ∧ (p5 → p4)) ∧ p2) ∨ True) → (False ∨ True)) ∧ (((p4 → p3) → p3) → p4)) → (p3 → p3)) ∨ p4) ∧ True) := by
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
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138388341446960816164459044770 : ((p4 → (p3 ∧ (((False ∨ ((((p5 ∨ False) ∧ p2) → p5) ∧ p3)) → ((p2 ∧ p5) → ((p2 ∧ True) ∧ False))) ∧ p1))) ∨ (p3 → (p4 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317881299610724551659123907818 : (p4 ∨ ((True ∧ ((p2 ∨ ((p3 → ((((p1 ∧ False) ∧ (((p1 ∧ (p4 → False)) ∧ p3) → p4)) ∨ p1) ∧ (p5 ∧ p3))) → False)) ∨ p2)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324667944047774144867458473484 : (p5 ∨ ((False ∧ (p3 ∨ p1)) ∨ ((p3 → (False ∧ ((p3 → True) ∧ (p4 → (p2 → (False ∨ p1)))))) → ((p5 ∨ p2) ∨ ((True → False) → True))))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_808467879081267155678007030874 : (((p4 → (p3 ∨ ((p4 → ((p3 ∧ p3) ∨ False)) ∨ (p5 ∧ ((p2 → p1) → (p3 ∧ (p3 ∧ (True ∧ (((False ∨ p3) → True) ∨ p2))))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_950041624235510855274803101476 : (((((True ∨ p1) → False) ∧ ((p1 ∧ (p5 ∨ (p1 → p1))) ∧ ((p3 ∧ (p2 ∨ ((p4 → p1) ∨ ((p1 → p1) ∨ True)))) ∨ (p2 ∨ p1)))) → p4) ∧ True) := by
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
  cases h7
  case inl h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h13 : (True ∨ p1) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h14 := h2 h13
        -- False on the left can always be used.
        apply False.elim h14
      case inr h15 =>
        -- Disjunctions on the left can always be decomposed.
        cases h15
        case inl h16 =>
          -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
          have h17 : (True ∨ p1) := by
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h2, we can now drive its conclusion.
          let h18 := h2 h17
          -- False on the left can always be used.
          apply False.elim h18
        case inr h19 =>
          -- Disjunctions on the left can always be decomposed.
          cases h19
          case inl h20 =>
            -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
            have h21 : (True ∨ p1) := by
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h2, we can now drive its conclusion.
            let h22 := h2 h21
            -- False on the left can always be used.
            apply False.elim h22
          case inr h23 =>
            -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
            have h24 : (True ∨ p1) := by
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h2, we can now drive its conclusion.
            let h25 := h2 h24
            -- False on the left can always be used.
            apply False.elim h25
    case inr h26 =>
      -- Disjunctions on the left can always be decomposed.
      cases h26
      case inl h27 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h28 : (True ∨ p1) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h29 := h2 h28
        -- False on the left can always be used.
        apply False.elim h29
      case inr h30 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h31 : (True ∨ p1) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h32 := h2 h31
        -- False on the left can always be used.
        apply False.elim h32
  case inr h33 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h34 =>
      -- Conjunctions on the left can always be decomposed.
      let h35 := h34.left
      let h36 := h34.right
      -- Disjunctions on the left can always be decomposed.
      cases h36
      case inl h37 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h38 : (True ∨ p1) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h39 := h2 h38
        -- False on the left can always be used.
        apply False.elim h39
      case inr h40 =>
        -- Disjunctions on the left can always be decomposed.
        cases h40
        case inl h41 =>
          -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
          have h42 : (True ∨ p1) := by
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h2, we can now drive its conclusion.
          let h43 := h2 h42
          -- False on the left can always be used.
          apply False.elim h43
        case inr h44 =>
          -- Disjunctions on the left can always be decomposed.
          cases h44
          case inl h45 =>
            -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
            have h46 : (True ∨ p1) := by
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h2, we can now drive its conclusion.
            let h47 := h2 h46
            -- False on the left can always be used.
            apply False.elim h47
          case inr h48 =>
            -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
            have h49 : (True ∨ p1) := by
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h2, we can now drive its conclusion.
            let h50 := h2 h49
            -- False on the left can always be used.
            apply False.elim h50
    case inr h51 =>
      -- Disjunctions on the left can always be decomposed.
      cases h51
      case inl h52 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h53 : (True ∨ p1) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h54 := h2 h53
        -- False on the left can always be used.
        apply False.elim h54
      case inr h55 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h56 : (True ∨ p1) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h57 := h2 h56
        -- False on the left can always be used.
        apply False.elim h57
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300152683251242259089493737803 : (False ∨ ((p3 ∨ ((False → (p4 ∨ (p4 ∧ p5))) → ((p1 ∨ (p2 ∧ ((((p5 ∨ False) → p2) ∧ (p3 ∨ True)) ∧ p4))) → p1))) ∨ (p4 → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191322760012139608973797901969 : (((p1 ∧ False) ∨ (((p5 → p5) ∧ False) ∨ (p5 ∧ p5))) ∨ (((((p3 → p1) ∧ True) ∨ (True ∧ (p2 → p2))) ∧ (False ∧ True)) → (True ∨ p2))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h7 := h3.left
    let h8 := h3.right
    -- False on the left can always be used.
    apply False.elim h7
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Conjunctions on the left can always be decomposed.
    let h12 := h3.left
    let h13 := h3.right
    -- False on the left can always be used.
    apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164713233330207564402901998129 : (((((((((p3 ∧ p3) → True) ∨ p4) ∨ p2) ∧ ((p1 ∨ p2) ∧ True)) ∧ p5) → p1) ∨ True) ∨ ((p1 ∧ True) ∧ (((True ∧ p3) → False) → p2))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111632523940619744499064636834 : (((((((True ∧ p1) ∨ (p3 → (p4 ∧ p4))) ∧ (p2 ∨ (p5 → (p4 ∧ p5)))) ∨ ((p2 → (p3 ∨ True)) ∧ p2)) ∨ p5) ∨ p2) ∨ (False → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53162818784833530941030273793 : ((((p2 ∨ ((p3 ∧ (False ∨ (p5 ∨ p5))) ∧ (p3 ∨ p5))) ∨ p3) ∨ (((False ∨ p5) ∨ ((True → True) ∨ ((p5 ∨ p4) ∨ p4))) ∨ p4)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148597660054479708999059588420 : (((p2 ∧ (((p4 → (False ∨ p4)) ∨ p2) → (p4 ∨ False))) ∨ ((((p1 ∨ p1) ∧ True) ∧ (p5 ∧ p1)) ∧ p5)) ∨ (p1 ∨ ((p2 ∨ p2) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51813478703982061124052402695 : (((True → (((p4 ∨ p2) ∧ ((p2 ∧ (p2 → p2)) → ((p4 ∨ p2) → p1))) → p5)) ∧ ((((p2 → (p4 ∨ p1)) ∧ p5) ∨ False) ∧ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64415029949447032373244538840 : ((p1 ∨ ((p2 ∧ (True ∨ (True → ((p3 ∨ ((p1 ∨ True) ∧ (p4 → (p5 ∨ p4)))) → ((((p3 ∨ False) → True) ∨ p4) → p5))))) → p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_247850849045025916981290124003 : ((p1 ∨ p2) ∨ (((p5 ∨ (((((p3 ∨ True) ∧ ((False → (p5 ∧ p4)) ∨ True)) ∧ True) ∨ False) ∨ p1)) ∧ p3) → (((True → p4) ∧ False) ∨ p3))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
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
        -- Conjunctions on the left can always be decomposed.
        let h10 := h8.left
        let h11 := h8.right
        -- Disjunctions on the left can always be decomposed.
        cases h10
        case inl h12 =>
          -- Disjunctions on the left can always be decomposed.
          cases h11
          case inl h13 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h3
          case inr h14 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h3
        case inr h15 =>
          -- Disjunctions on the left can always be decomposed.
          cases h11
          case inl h16 =>
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
        -- False on the left can always be used.
        apply False.elim h18
    case inr h19 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_752745544130219416810445205409 : (((False ∧ (((p4 ∧ (False ∧ p1)) ∨ (p4 ∧ ((p4 ∨ p2) ∧ (False ∧ ((p2 → False) ∧ (((False ∨ (p5 ∧ p5)) ∨ p5) → True)))))) ∨ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173173718127502653844269207417 : ((p4 ∨ (((p4 → (((p2 ∨ (p2 ∨ p1)) ∨ True) ∨ p5)) ∨ p4) ∧ (p1 → False))) ∨ ((((p3 ∧ p3) → p2) → ((False ∧ True) ∨ p3)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_679801754425553033622380573184 : ((((((p3 ∧ True) → (p4 ∧ (False ∧ ((((p5 → (p2 → False)) ∨ p3) ∨ p4) ∧ (False → False))))) ∨ p2) → ((p5 ∨ (False ∧ True)) ∨ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160263364997882250758564093037 : (((p1 ∨ (p5 → (True → ((p3 ∧ ((p3 ∨ p4) → ((p5 ∨ p3) ∨ p1))) ∨ p1)))) ∨ (p5 ∨ p4)) → (((p1 ∨ (p3 ∨ p1)) ∨ True) ∨ False)) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h4 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_932024101312238679951203628631 : (((((((p1 ∧ p5) ∨ (p1 ∨ True)) ∨ p4) → p3) ∧ ((((p1 ∧ (p2 → p2)) → (p4 ∧ ((False ∨ (False ∧ p5)) → p2))) ∨ p3) ∨ p5)) → p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h6 : (((p1 ∧ p5) ∨ (p1 ∨ True)) ∨ p4) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h7 := h2 h6
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h8 =>
      -- One of the premise coincides with the conclusion.
      exact h8
  case inr h9 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h10 : (((p1 ∧ p5) ∨ (p1 ∨ True)) ∨ p4) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h11 := h2 h10
    -- One of the premise coincides with the conclusion.
    exact h11
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37090386903325239315280069061 : (((((True ∧ (p3 ∨ ((((True ∧ (((p1 → p1) ∨ (p1 ∨ False)) → (p5 → p1))) ∨ p5) ∧ (p5 ∨ p1)) → p3))) ∨ False) ∧ True) ∧ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309922132858143019406142567940 : (p2 ∨ (((p1 ∨ ((p5 → (p4 ∧ (p4 ∨ (p1 → (p3 ∧ p3))))) → False)) ∧ (p3 ∨ (p5 → p2))) ∨ ((p3 → p3) ∨ ((True → p2) ∨ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_265729077418148380813277958660 : (True ∧ (p3 ∨ ((p5 ∨ False) ∨ (((((p1 → True) ∧ (p1 ∧ p5)) ∨ False) ∨ (p1 ∧ ((p1 → p4) → (p2 → ((True → p2) ∧ True))))) ∨ True)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180473638707744930404516216077 : (((p3 → (p3 ∨ (((p4 ∨ False) → (False ∧ False)) ∧ p4))) → (p2 ∧ p2)) → ((((p4 ∨ p1) → p3) → p1) ∨ (p2 ∨ (p4 ∨ (p4 ∨ p2))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p3 → (p3 ∨ (((p4 ∨ False) → (False ∧ False)) ∧ p4))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231605902183889088853713276260 : (((True ∧ p2) → p5) → (p2 → (p5 ∧ (p5 ∧ (p3 ∨ (((False ∨ False) ∧ ((True ∧ ((p3 ∨ p5) ∨ p1)) → (p4 → p3))) ∨ (p2 ∨ True))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : (True ∧ p2) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- One of the premise coincides with the conclusion.
  exact h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h5 : (True ∧ p2) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h5
  -- One of the premise coincides with the conclusion.
  exact h6
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158745988922186713423590802313 : ((p4 ∧ ((((p1 → p5) ∧ ((False → p1) → False)) ∧ ((True ∧ (p3 ∨ False)) → (p4 ∨ p3))) ∨ True)) ∨ (((True ∧ p4) ∨ p4) → (True → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258807947970281901855845565280 : ((True → False) → (p1 ∨ (((((p1 ∧ p2) ∨ (((p4 ∧ p4) ∨ p2) ∧ p2)) ∧ (p5 ∨ (p1 → p1))) ∧ (False ∧ (False → p1))) ∨ (p5 → False)))) := by
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
theorem thm_5_vars_64763748209868018749260927041 : ((p2 ∨ ((False ∨ ((p4 ∨ ((p3 → (False → (((p4 → ((False ∧ True) ∧ ((p4 ∧ False) → False))) → p2) ∧ p2))) ∨ p3)) → False)) ∧ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341704904346455028033191721180 : (p2 → (((((((True → p3) → p1) ∨ False) ∧ (True → (p5 → (p5 → (p4 → True))))) → p1) ∧ (False ∧ (True ∧ (p4 → p3)))) ∨ (p5 → p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_713290127004234370865710758980 : ((((p4 ∨ (p4 ∨ ((p2 ∧ p1) ∧ p1))) ∨ (True ∨ (((False → ((((p1 ∧ False) ∨ p1) ∧ (p3 ∨ (p5 → p2))) ∧ p5)) → p3) ∧ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59257419955195857074096268076 : (((p2 ∨ p5) ∨ ((p5 ∧ ((p1 → False) → p4)) ∨ ((False ∨ ((True → (p4 → p2)) ∨ (p4 → p2))) ∨ (((p1 ∨ p1) → p5) ∨ True)))) ∨ False) := by
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
theorem thm_5_vars_317917971511308621043333427335 : (p4 ∨ ((p5 ∧ ((True ∧ p5) → (p1 ∧ ((p4 ∨ p2) → ((((p1 → False) → p1) → ((p4 → p4) → (p5 ∧ (False ∧ False)))) ∨ False))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46317725841885393054440429995 : (((((((p1 ∨ p3) ∨ (p1 → (p2 → p5))) ∧ (((p4 ∧ p2) ∨ False) ∨ False)) ∨ p2) ∨ (False → (False ∨ (p2 ∨ p5)))) ∧ (p1 ∨ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60470296019104573208182079287 : (((p5 → p4) → ((p3 → (((p2 → ((True ∧ (p5 ∨ ((p3 → (p5 ∧ (True ∨ (False ∨ False)))) → p1))) ∨ p4)) → p1) ∧ p5)) → p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_610564480608866094796904155730 : ((((((((p5 ∨ (((True → (p3 ∧ p1)) ∨ (p1 → p1)) ∨ ((p5 → p1) → (p1 ∧ p3)))) ∨ False) ∧ p1) ∨ (p5 ∧ p3)) → False) ∨ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149991600481544030772881584776 : ((p4 ∨ (p1 ∨ ((p4 ∧ p5) ∨ (((p3 ∧ True) ∨ True) ∨ ((p2 ∧ (p4 ∨ (p2 ∧ (p1 ∧ p1)))) ∨ p2))))) ∨ (p2 → (p2 ∧ (p1 ∧ p5)))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42194754440791740344824537844 : (((True ∧ ((p4 ∨ (True → p4)) ∧ (p2 ∨ (True → (((((p3 ∧ ((False → (p2 → p3)) → p4)) ∧ p4) ∧ True) ∨ p2) → p4))))) ∨ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41056301699444382308757031148 : (((((p3 ∧ p3) → (((False ∧ p3) → (p5 → ((p2 ∨ p5) ∨ p4))) ∨ (p2 ∨ (False ∧ (p4 → (p3 ∨ p3)))))) → (True ∧ p4)) ∨ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258933506739501571762621768366 : ((True → p2) → (True → ((((((False ∧ (False ∨ (False ∨ p3))) ∧ p3) ∨ True) ∨ p5) ∧ (p2 ∧ (False → p1))) ∨ (p5 ∨ ((p3 ∨ True) ∨ False))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
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
theorem thm_5_vars_322704641052835828950752684796 : (p5 ∨ ((((((False ∨ ((p3 → (((p3 → (p5 → p5)) ∧ ((p5 → (False → p1)) ∨ p4)) ∧ True)) ∨ False)) → p2) → p3) ∨ True) → False) → False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((((False ∨ ((p3 → (((p3 → (p5 → p5)) ∧ ((p5 → (False → p1)) ∨ p4)) ∧ True)) ∨ False)) → p2) → p3) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215163552677851076304969475345 : ((True ∧ ((p2 ∧ p2) ∨ p5)) ∨ (((p1 ∨ p4) ∨ ((True ∧ (((p2 → (p1 → p1)) ∨ False) ∨ True)) ∨ (((p4 ∨ p1) → p1) ∨ False))) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52319179798091640577198575436 : (((((p1 ∧ (True ∨ ((True ∨ p1) ∨ p1))) ∧ ((p5 → p3) ∧ True)) ∨ p2) ∧ ((p2 ∧ p2) ∨ (p4 ∧ ((False ∧ (p4 ∨ True)) ∨ p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_105141909114170871684297871133 : ((((p4 ∧ (((False ∧ True) ∧ p5) ∧ p1)) ∧ (True ∨ ((p1 ∨ ((p4 ∨ p2) → (True ∧ p3))) ∨ p2))) ∨ ((True ∧ True) ∨ p3)) ∧ (p2 ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57339388738940250802880633487 : (((p2 ∧ (True ∧ p5)) ∨ ((((p1 → (p4 → p3)) → p1) → ((((p3 ∨ p1) ∨ p3) ∨ (p1 ∨ (p3 ∨ p4))) → p1)) ∨ (p2 → True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152898208485859759795818373405 : ((True ∧ (p1 ∧ ((p4 → False) ∧ ((p5 → (False ∧ p5)) ∨ (p1 ∨ ((p1 ∧ (False → (p3 ∨ p2))) ∧ p5)))))) → (((p1 ∧ p4) → p2) ∨ p4)) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h9
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h12 : p4 := by
      -- One of the premise coincides with the conclusion.
      exact h11
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h13 := h6 h12
    -- False on the left can always be used.
    apply False.elim h13
  case inr h14 =>
    -- Disjunctions on the left can always be decomposed.
    cases h14
    case inl h15 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h16
      -- Conjunctions on the left can always be decomposed.
      let h17 := h16.left
      let h18 := h16.right
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h19 : p4 := by
        -- One of the premise coincides with the conclusion.
        exact h18
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h20 := h6 h19
      -- False on the left can always be used.
      apply False.elim h20
    case inr h21 =>
      -- Conjunctions on the left can always be decomposed.
      let h22 := h21.left
      let h23 := h21.right
      -- Conjunctions on the left can always be decomposed.
      let h24 := h22.left
      let h25 := h22.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h26
      -- Conjunctions on the left can always be decomposed.
      let h27 := h26.left
      let h28 := h26.right
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h29 : p4 := by
        -- One of the premise coincides with the conclusion.
        exact h28
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h30 := h6 h29
      -- False on the left can always be used.
      apply False.elim h30



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118104037874057413138717287139 : ((False ∨ (((((p5 ∧ (p1 ∧ ((p2 → p3) → (p3 → False)))) ∨ p1) ∨ True) ∨ ((((p2 ∨ p5) ∧ False) ∨ p2) → p1)) ∨ False)) ∨ (p5 ∧ True)) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260196196043344346621719092191 : ((p2 → p2) → ((p5 ∧ p5) → (p4 ∨ (((p5 ∧ (p3 → True)) → (p2 → ((p4 → False) → (p3 ∨ (False ∧ p3))))) ∨ (True ∨ (p1 → p2)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307308497185496230719136271692 : (p1 ∨ (p3 ∨ (((False ∨ ((p4 ∨ ((((False ∨ True) → (p4 ∨ (p5 ∨ True))) ∨ p1) ∨ True)) ∨ False)) → (p2 ∧ (p5 ∨ (True ∨ p4)))) → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (False ∨ ((p4 ∨ ((((False ∨ True) → (p4 ∨ (p5 ∨ True))) ∨ p1) ∨ True)) ∨ False)) := by
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
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the left conjuct of h3 based on <expert-advice>.
  let h4 := h3.left
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59080046154923663497604834879 : (((p5 ∧ p2) ∨ (((p2 ∨ (((p4 ∧ p3) → ((p3 ∨ p5) → ((p3 ∧ (p3 ∨ p2)) ∧ p1))) ∨ p3)) → (False ∧ (p2 ∨ p1))) ∧ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118606718854529378094722624580 : ((p4 ∨ (((((False ∨ (((p4 ∨ p4) → False) ∨ p2)) ∧ (True → p4)) ∧ (p2 ∨ (p3 → True))) → False) → (p3 → (True → p2)))) ∨ (p5 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_686947147910918286791572665072 : ((((p2 ∨ ((p4 → (False ∨ ((False ∧ ((p5 → p4) ∧ ((True ∨ p3) ∧ p3))) ∧ p4))) → False)) → ((p1 → (p5 ∨ (False → p4))) → p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44444542640419664719038957993 : ((((((p5 → (True → p1)) → (p5 → (p2 ∧ (p5 ∨ p4)))) ∧ False) ∨ (p5 → (((p5 ∨ (True → p3)) ∧ True) ∨ (True ∨ True)))) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166256216282834984664036458448 : ((p3 ∧ ((((p1 ∧ True) → p5) ∨ ((p4 ∨ p1) ∨ (False ∨ True))) ∧ (True → (p2 → True)))) ∨ ((p3 → (p2 → (p1 ∨ (p2 ∨ p5)))) ∨ p3)) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_610333281949212954290210159702 : ((((((((((True → (((p5 ∨ p2) ∨ p1) ∨ (p1 ∧ (p4 ∨ p5)))) ∨ (p2 ∨ p5)) → (p5 ∧ False)) ∧ False) ∧ p2) → True) → False) ∨ True) ∨ False) ∧ True) := by
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
theorem thm_5_vars_135375282131028162864470008113 : ((((((p4 ∧ ((True ∨ p1) ∨ (p2 → p4))) ∧ (p3 ∧ (False ∧ p5))) ∧ (False → p5)) ∨ p4) ∨ (False → (False ∧ p3))) ∨ ((p1 ∧ p1) ∨ p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_184428186805590181059463920732 : (((((True ∧ p3) ∧ p3) ∧ (p2 ∧ (p5 ∨ p1))) ∧ (False ∧ True)) ∨ (False → ((p3 → (p3 → (p4 → ((p2 ∨ p4) → (p5 ∧ True))))) ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136467710460621432791579921310 : ((((p4 ∧ p5) ∧ p5) ∧ ((p3 ∧ (p3 ∧ (True → p3))) → (((p1 ∨ p2) ∧ p5) ∨ (((p1 ∨ p2) ∧ False) → p4)))) ∨ ((True → True) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171596587718885786431865168577 : ((((p5 ∨ (p4 → (p3 ∧ (True ∧ (False → True))))) → (p4 ∨ (p1 ∧ p3))) ∨ True) ∨ ((p5 ∧ ((p3 ∧ ((p5 → p1) → p1)) ∨ p5)) ∨ p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62897080973829259387536417251 : ((p4 ∧ ((p4 ∨ p2) ∨ ((p2 ∨ p1) ∨ ((p1 → (True ∧ p4)) ∧ ((((p5 ∨ p3) ∧ True) → (p4 ∧ (True ∧ (p4 ∨ True)))) ∨ False))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150300837975670879451232769566 : ((p4 → (((((p5 ∨ p1) ∧ False) ∨ (p2 ∨ (p3 ∨ p4))) ∧ True) ∨ (p1 → ((p1 ∧ p1) ∧ (p1 ∨ True))))) ∨ ((False → (p5 → p3)) ∧ p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
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
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228964296135349372755235273862 : ((p4 ∨ (p2 → False)) ∨ ((p3 ∧ ((p3 → p1) → (p3 ∧ (p2 → p4)))) ∨ (p3 ∨ ((((False ∨ p5) → p5) ∧ False) → ((p4 ∧ True) ∧ p1))))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h3
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_189319326646301007372074083130 : (((p4 → p3) → (True → ((False ∧ (True → p3)) → p3))) ∧ ((False ∨ (((p2 ∧ (p4 ∨ p2)) ∧ (p2 ∨ p4)) ∨ True)) ∨ (p4 ∧ (p2 ∨ p2)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- False on the left can always be used.
  apply False.elim h4
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_657244978493239402134563171141 : (((((False ∨ (p3 → p1)) → (((((p5 → p5) → ((p2 ∧ ((True ∨ p1) ∧ p1)) ∨ p5)) ∧ p1) ∧ (False → p5)) ∨ p2)) ∨ (p2 ∨ True)) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_802583375293808969738802877974 : (((p2 → (p5 ∨ ((((p4 → p4) ∧ ((True → (False ∨ ((p1 → p2) ∨ p3))) → (p5 ∧ (True ∧ (p4 ∧ p5))))) → p3) ∧ (p2 ∧ p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_797342369920826285751179208336 : (((p1 → (((((p2 ∨ p2) ∧ p3) → (((p5 ∨ False) ∧ p3) ∨ (False ∨ p2))) ∨ (p3 → ((p5 → (p1 ∨ (False ∧ False))) → p3))) ∨ p5)) ∨ p1) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54818014246941938175970306394 : (((p5 ∨ ((True ∨ (False ∨ False)) ∧ (p5 ∨ p3))) → ((((p2 ∧ p3) ∧ (p3 → (p1 ∨ (((True ∨ p5) ∧ p1) → p5)))) ∨ False) ∨ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115340399933146116503194000364 : (((p4 ∨ ((p1 → (p3 → True)) ∨ (False ∨ (True ∨ p1)))) → (p3 ∧ ((True ∨ (True → (p5 ∧ (p5 ∨ p3)))) → (True → p3)))) ∨ (True ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161556453458024248989479545822 : ((p5 ∧ (p1 ∨ ((((((p1 → p5) ∨ True) ∨ p4) ∧ False) → (p2 ∨ ((True ∧ p1) ∨ p2))) ∨ False))) → (((True → p2) ∧ p1) ∨ (p3 → p5))) := by
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
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h9 =>
      -- False on the left can always be used.
      apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174802473553743897060213021953 : (((True → p5) ∧ ((False ∨ ((p2 → (p4 ∨ (True ∧ False))) ∧ p2)) → (p1 ∨ p3))) → (p5 ∨ (((p3 → True) ∨ (p4 ∨ p2)) ∧ (True ∧ False)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_170561886682668662354194347676 : (((False ∨ p2) ∨ (p2 → (((p1 ∨ p4) → (p4 → (True ∨ p4))) → (p3 ∨ p2)))) ∧ ((((p2 ∨ (p1 ∧ p1)) ∧ True) → p2) ∨ (p4 ∨ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_655351594178252182585510791459 : ((((((((p4 ∨ p1) ∨ ((p2 ∨ False) → (((True → False) ∨ ((p5 ∧ True) → p4)) ∧ False))) ∨ p5) ∨ True) ∨ (p4 → p1)) ∨ (p2 ∨ p4)) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_136899976253513597612133584133 : (((p4 ∨ p5) ∨ (False ∧ (((p2 ∨ ((p1 ∧ p2) → (p3 ∨ p2))) → (p2 ∧ ((p3 ∧ p3) ∨ (p3 ∨ p2)))) ∨ p1))) ∨ (p5 → (True → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246455193919596296586182422326 : ((p5 ∧ False) ∨ ((((False ∨ False) ∧ ((p3 ∨ p4) ∧ (False ∧ (p5 → ((True → False) → True))))) ∧ p2) ∨ ((((False ∧ True) → p5) ∨ p1) ∨ p1))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45910745877312290085465375994 : (((p4 → ((p2 ∨ (p2 ∨ (((p4 ∧ (p2 ∧ p4)) ∧ ((True ∨ (p5 ∨ False)) → False)) → p5))) ∧ ((p5 ∧ (p4 ∧ p2)) ∨ p3))) → p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54200029525466679563242726465 : (((((p3 ∧ (True → True)) ∨ (p5 → p1)) ∨ p4) ∧ (((p4 → (False → True)) → p5) ∧ (p2 ∨ ((p2 → (p1 → p5)) ∧ (p2 → False))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_316473344339452965703894511257 : (p3 ∨ (p1 ∨ (p4 ∨ (((((p5 ∨ (p3 → True)) ∨ p2) ∧ (p3 → p3)) ∧ p1) → ((p5 → (p5 → ((p2 → (p4 ∨ p2)) ∧ p2))) ∨ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  let h4 := h2.left
  let h5 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
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
theorem thm_5_vars_877617662642511491962494751504 : (((((True → (False ∧ (p2 → p5))) ∧ (True ∧ ((p5 ∧ (((p2 ∧ p4) → p5) → p3)) ∧ (p5 → ((p1 ∨ p1) → p1))))) ∧ (p1 ∧ True)) → False) ∧ True) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h8 := h7.left
  let h9 := h7.right
  -- Conjunctions on the left can always be decomposed.
  let h10 := h8.left
  let h11 := h8.right
  -- Conjunctions on the left can always be decomposed.
  let h12 := h3.left
  let h13 := h3.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h14 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h15 := h4 h14
  -- We need to get the left conjuct of h15 based on <expert-advice>.
  let h16 := h15.left
  -- False on the left can always be used.
  apply False.elim h16
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190405327094244699817050986243 : (((p4 ∧ (p2 ∨ ((False ∧ p2) ∧ (False ∨ p2)))) ∨ True) ∨ ((p1 ∧ (((p1 → (p4 ∨ (p3 ∨ p5))) → p2) ∨ (p4 ∧ (p2 ∨ False)))) → p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258764589073134927972968018105 : ((True → False) → (((((p5 ∨ (((p5 ∨ p1) ∧ p2) ∧ p3)) → False) ∧ (p5 ∨ ((p3 → p5) ∧ p3))) ∨ ((True ∧ (True ∨ True)) ∧ False)) ∨ p4)) := by
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
theorem thm_5_vars_252138049986465864581557547672 : ((p4 → p3) ∨ (((p3 ∨ ((((p4 → p2) → (p5 → ((((False ∨ p3) ∨ p5) ∧ p1) ∨ False))) ∧ p1) ∨ ((p3 → True) → True))) ∨ p3) ∧ True)) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_4105637289389243342422885807 : (p3 ∨ ((((p1 → p2) ∨ ((p3 → p2) → (p1 ∧ (p1 ∨ p2)))) → (p5 ∨ p4)) ∨ (((True → (p2 ∧ False)) → p3) ∨ (p2 → False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_113491838746286946150581804157 : (((((p1 ∨ (p5 → (p4 → (p1 ∨ (p1 → (p3 ∨ (True ∧ (True ∧ False)))))))) ∨ p5) ∧ ((True → p2) ∧ False)) ∨ (True ∨ p2)) ∨ (p2 ∧ p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40504232540216358507588326115 : ((((p1 ∧ ((((True → p3) → (p4 ∧ p5)) → ((True ∧ ((True ∨ p1) ∨ ((p1 ∨ p5) ∨ p3))) ∨ p5)) → (p2 → p4))) ∨ p1) ∨ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45053515270433436322669982253 : ((((p1 → p3) ∨ ((p4 → p1) ∧ (((p5 ∨ p1) → (((p1 ∧ ((p4 ∧ p4) ∨ p4)) ∨ (p5 → p2)) → (False ∧ p2))) → p4))) → p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179341588098408681750897296890 : ((p1 ∨ (True ∧ ((p2 ∧ (p1 ∧ (p4 ∧ (True → (p1 ∨ True))))) ∧ False))) ∨ ((p2 ∧ (True → True)) ∨ ((p3 ∧ ((True ∧ False) → p1)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165723684257057455764098433138 : (((False ∨ ((p3 ∧ p1) ∨ p3)) ∧ ((True ∧ (((True ∨ (p2 → p4)) ∧ p5) → p2)) ∨ p5)) ∨ ((False ∧ (p4 → ((p1 ∨ p3) ∨ p4))) → p1)) := by
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
theorem thm_5_vars_654505294007274731063532937601 : (((((p1 ∧ ((True → ((((p1 → ((p4 → (True → p3)) ∧ p3)) ∨ False) → (p3 ∨ False)) → (p1 ∧ p1))) ∨ False)) ∨ True) ∨ (p4 ∧ p5)) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_171999228343358766355948941118 : (((((((p2 ∧ p4) → (False ∧ True)) ∧ (True ∧ True)) ∨ p3) → False) ∨ (p3 → True)) ∨ (p5 ∨ (((True ∧ True) → p5) ∨ (p2 ∧ (p1 ∧ False))))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53933447030429217180517956789 : (((True → ((False ∨ False) ∨ (False ∨ ((p5 → False) ∧ p3)))) ∨ (p4 → ((((p1 ∨ p2) → p3) → True) → (p4 ∨ ((True → p3) ∨ False))))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166561248136264187248933615641 : ((p5 ∨ (p4 ∧ (p4 → ((p2 ∧ ((p2 ∧ p1) → (((p3 ∨ False) → p1) ∧ p1))) → p1)))) ∨ (False → (p2 ∧ (p2 ∧ ((p5 ∨ p3) ∨ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232163536609342345080302252184 : (((True → p4) → False) → (((p2 ∨ (((p1 ∧ p5) ∧ ((True ∨ False) ∨ p4)) ∨ (p3 → (True ∨ p5)))) → (False ∧ (p1 → (p5 ∨ p3)))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51712176166555362712750628853 : (((((p1 ∨ p3) ∨ (p1 → ((p4 ∧ p4) ∨ p1))) ∨ (p3 ∧ (False → (p3 ∧ False)))) ∧ ((p5 ∧ (True ∨ p3)) ∧ ((p1 ∨ True) → p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301568623929403706781611612487 : (False ∨ ((p3 ∨ (p5 ∨ p3)) ∨ (((p3 ∨ p5) ∨ ((p3 → (False ∨ p2)) → ((False ∨ p1) ∨ p1))) → (((p4 → (p1 ∧ True)) → p2) ∨ True)))) := by
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
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h4 =>
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
theorem thm_5_vars_148856094657631417313646024904 : (((p2 ∧ (p3 ∧ (p5 → p3))) ∧ ((((((p1 → p1) → p5) ∧ p3) ∧ True) ∧ (p2 → p4)) → (p1 → False))) ∨ ((True ∨ p5) ∧ (True ∨ p1))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111981892864848229800817989743 : (((((False ∨ ((True → p1) → False)) ∨ p1) → ((((True ∧ (p4 ∧ p4)) → p5) ∨ ((p3 ∨ p2) ∧ (p1 → p2))) ∨ False)) ∨ True) ∨ (p2 ∧ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225768418020277547922731043050 : (((p5 → False) ∧ p5) ∨ (((((p5 ∨ ((p5 → False) ∨ p2)) → (p3 ∧ (p4 ∨ (False → (p4 ∨ ((False → p5) ∧ p1)))))) ∧ p1) ∨ True) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_806511939301222587491340109842 : (((p4 → (((p4 ∨ (True ∧ ((((False → ((p2 ∨ p5) ∨ True)) ∧ (p1 ∨ (p1 ∨ (p1 ∧ False)))) ∧ p1) ∨ p2))) → (p4 ∨ p4)) → p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



