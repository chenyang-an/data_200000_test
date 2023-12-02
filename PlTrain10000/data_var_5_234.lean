variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_358523450530699310422113365166 : (p5 → (p2 → ((True → ((p2 → ((p4 → (((p5 ∨ ((True → p2) ∧ p3)) ∧ (p3 ∨ False)) ∧ p3)) ∧ (p1 ∨ p1))) → (p4 ∧ p5))) ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257183534482940171044082089015 : ((p2 ∨ p2) → (((((p3 ∨ p5) ∨ (False ∨ (p3 ∨ p4))) ∧ (p3 ∨ (((p2 ∧ (False ∧ ((p3 → True) → False))) ∧ p5) → p1))) ∧ p5) ∨ True)) := by
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
theorem thm_5_vars_65882106472692785448579081469 : ((p4 ∨ ((p1 ∨ False) → ((p5 ∧ (((False → p5) → ((((p1 → False) ∨ ((p4 ∧ p1) ∨ p2)) ∧ p5) ∨ p1)) ∨ p3)) ∨ (True ∧ True)))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- False on the left can always be used.
    apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_619469896996159701778525647219 : (((((p3 ∨ (p1 ∨ p4)) → ((p5 → p2) → (p2 ∧ (p5 ∨ (True ∨ (False ∨ ((p5 ∨ p1) ∨ (p2 → (p1 ∨ (p5 → True)))))))))) ∨ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_626828253028135011623471377781 : ((((p5 → ((((p5 ∨ p1) → p1) ∧ p3) ∨ ((p2 → p5) ∧ (((p4 → p2) ∨ (p5 ∨ (p2 ∧ (p3 ∨ (p3 → p3))))) → False)))) ∨ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227262166715255174434964241636 : (((p1 → False) → p2) ∨ (((False ∨ False) ∧ p3) ∨ ((True ∧ (p1 ∨ ((p3 ∨ p2) ∧ ((p5 → p4) ∧ ((p5 → (p1 ∧ True)) ∨ p5))))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257697144971256104466642907707 : ((p3 ∨ p3) → ((((p5 ∨ (p3 ∧ p2)) → p4) → p1) ∨ ((((True ∧ p4) ∧ True) → ((p5 → ((p5 ∧ p2) → p3)) → (p1 → p3))) ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the left can always be decomposed.
    let h6 := h3.left
    let h7 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h6.left
    let h9 := h6.right
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h10 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h11
    -- Implications on the right can always be decomposed.
    intro h12
    -- Implications on the right can always be decomposed.
    intro h13
    -- Conjunctions on the left can always be decomposed.
    let h14 := h11.left
    let h15 := h11.right
    -- Conjunctions on the left can always be decomposed.
    let h16 := h14.left
    let h17 := h14.right
    -- One of the premise coincides with the conclusion.
    exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_649683492279495565836445557798 : (((((p4 ∨ (((((p3 ∧ p4) → p4) → p3) → (p1 ∨ p5)) → ((((p2 → True) ∧ True) ∧ p3) ∨ False))) ∨ (p3 → False)) ∧ (p2 ∨ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_75743928923056437154571981819 : ((((((p4 ∨ (False ∨ (p2 ∧ p2))) → (p5 ∨ ((False ∧ p1) ∧ (p2 ∨ ((p1 ∨ False) → p3))))) → ((p2 → False) ∨ p4)) ∨ True) → p3) → p3) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((((p4 ∨ (False ∨ (p2 ∧ p2))) → (p5 ∨ ((False ∧ p1) ∧ (p2 ∨ ((p1 ∨ False) → p3))))) → ((p2 → False) ∨ p4)) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48845604438699105201310122529 : (((p1 ∨ (True ∧ (((((True ∧ p2) ∨ (p3 ∨ p5)) ∧ ((True ∨ p5) ∨ p3)) → p5) ∧ (True ∧ (p2 → False))))) ∧ (p1 → (True ∨ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_655685291261847573621957955907 : ((((((p1 ∧ (p3 ∧ ((p4 ∧ p2) ∧ False))) ∨ ((p1 → (p3 ∧ ((False ∨ p4) ∨ True))) ∧ p4)) ∧ ((p1 ∨ p4) ∧ True)) ∨ (p1 ∧ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115831046564922535607310698817 : ((((p1 → p5) → (False ∨ p4)) ∧ ((((p1 ∨ ((False ∨ p5) → (True ∨ p3))) ∧ (p5 ∧ p3)) ∧ (p5 ∨ p5)) → (p5 ∧ p2))) ∨ (True ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301906268903799532548753244487 : (False ∨ ((p2 ∧ p3) → ((p4 ∧ p1) ∨ ((((((p4 ∨ (p5 ∧ (p2 ∧ (p3 ∨ False)))) ∨ (p4 → p1)) ∧ p4) → (p2 → p1)) ∨ p2) ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_39399913708762307217280604351 : (((p4 ∧ (((p3 → (((p4 ∧ (True ∨ (p5 ∨ False))) → ((p5 ∧ (True → (p5 → p2))) ∨ (p1 ∨ p1))) → p3)) ∨ p5) → p5)) ∧ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51477531509626480488016715866 : (((((False ∨ ((False → p2) ∧ True)) ∨ False) ∧ ((p4 → p4) ∧ ((p1 ∨ False) → (True → p3)))) → (((p5 ∧ True) ∨ p2) → (p3 ∧ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_123363373066173483781192845281 : (((p2 ∨ (p1 ∧ (((p4 ∨ p1) ∨ p1) ∧ ((p2 ∧ True) ∨ (p4 ∨ ((False ∧ False) → p1)))))) ∨ (((p5 ∨ p5) ∨ False) → p5)) → (p5 ∨ True)) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h9 =>
        -- Disjunctions on the left can always be decomposed.
        cases h9
        case inl h10 =>
          -- Disjunctions on the left can always be decomposed.
          cases h8
          case inl h11 =>
            -- Conjunctions on the left can always be decomposed.
            let h12 := h11.left
            let h13 := h11.right
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h14 =>
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
          -- Disjunctions on the left can always be decomposed.
          cases h8
          case inl h18 =>
            -- Conjunctions on the left can always be decomposed.
            let h19 := h18.left
            let h20 := h18.right
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h21 =>
            -- Disjunctions on the left can always be decomposed.
            cases h21
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
      case inr h24 =>
        -- Disjunctions on the left can always be decomposed.
        cases h8
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
theorem thm_5_vars_191317596889076304992291205868 : (((True ∧ p4) ∨ ((p1 ∨ (p3 ∧ p1)) ∧ (p2 ∧ False))) ∨ ((False → (p4 ∧ (False ∨ (True ∧ ((p1 ∨ p5) → p4))))) ∧ (True ∧ (p4 ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177925595010925918860431067281 : ((((p3 → ((True ∨ p1) ∨ (p2 ∧ p5))) → ((p3 ∨ p2) ∧ p4)) ∨ True) ∨ ((p2 ∨ (p3 ∨ ((p1 → p2) ∧ ((p5 → p5) ∧ p3)))) ∧ p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_928543515824636101442226572573 : ((((True → (((p3 ∧ (p3 → (p3 ∧ p2))) ∧ p1) ∧ p3)) ∧ ((((False ∨ (p1 ∧ p1)) ∧ (p1 ∧ (p4 ∧ (p5 ∨ p2)))) ∨ p2) ∧ p3)) → p1) ∧ True) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h9 =>
      -- False on the left can always be used.
      apply False.elim h9
    case inr h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- Conjunctions on the left can always be decomposed.
      let h13 := h8.left
      let h14 := h8.right
      -- Conjunctions on the left can always be decomposed.
      let h15 := h14.left
      let h16 := h14.right
      -- Disjunctions on the left can always be decomposed.
      cases h16
      case inl h17 =>
        -- One of the premise coincides with the conclusion.
        exact h13
      case inr h18 =>
        -- One of the premise coincides with the conclusion.
        exact h13
  case inr h19 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h20 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h21 := h2 h20
    -- We need to get the left conjuct of h21 based on <expert-advice>.
    let h22 := h21.left
    -- We need to get the right conjuct of h22 based on <expert-advice>.
    let h23 := h22.right
    -- One of the premise coincides with the conclusion.
    exact h23
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213573466938396267107862066314 : ((((p3 ∨ p3) ∧ p4) ∨ p3) ∨ ((((False ∧ p1) ∧ ((p2 → p4) ∨ p5)) ∧ p2) ∨ (p2 → (((p4 ∨ (p1 → (p4 ∧ True))) ∨ p2) ∨ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_622721776160386007880828309529 : ((((p4 ∧ ((p1 ∧ p4) ∨ ((((p2 ∧ (p5 ∧ (p1 ∧ p3))) ∧ False) ∧ (((p3 ∧ p2) → (p3 ∧ p2)) → p2)) ∧ (False → True)))) ∨ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_748597340930493491972040766176 : ((((p3 → p1) → (((((p4 ∧ p3) ∨ p5) ∨ p3) ∧ p3) → ((p2 ∧ (p1 → (((p5 ∨ (p5 ∨ (p4 ∨ p3))) ∨ p5) ∧ p3))) ∨ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137050151595492709191725287222 : (((p1 → True) → (((False ∨ p5) → (p1 ∧ (((False → False) ∨ True) → p3))) → ((((False ∨ p5) → False) ∧ p1) → p3))) ∨ ((p3 ∨ False) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234001750952672004890033334611 : ((p5 ∨ (p2 ∨ True)) → ((((True ∧ (p2 ∧ p1)) ∧ ((p1 ∧ ((p2 ∨ p5) → p5)) → True)) ∧ p3) → ((((p5 ∨ True) → True) → False) ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- Conjunctions on the left can always be decomposed.
  let h9 := h8.left
  let h10 := h8.right
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h11 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h10
  case inr h12 =>
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h13 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h10
    case inr h14 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112363623083969085039641675063 : ((((((((False ∨ p5) ∨ (((p2 ∧ p4) → (p5 ∨ (p2 ∨ p3))) → ((p5 ∨ True) ∧ p3))) ∧ p2) ∧ p5) → p3) ∧ p3) → p4) ∨ (p2 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_151007792094577394667964013699 : (((p1 → (p2 ∧ ((((p1 → True) → (True ∧ p3)) ∨ False) ∧ (False ∧ (p5 ∨ (True → (p1 → p5))))))) ∨ p1) → ((p4 → (p5 ∧ p3)) ∨ True)) := by
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
theorem thm_5_vars_151678262814405530214371577584 : (((True ∨ (p4 → (((p3 ∧ (((True ∨ True) → p5) ∨ (p5 → p4))) ∨ p5) ∨ p1))) ∧ (p1 ∧ (p2 ∧ p1))) → (p1 ∧ ((p3 → False) ∨ p2))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h3.left
    let h6 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h3.left
    let h11 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- One of the premise coincides with the conclusion.
    exact h13
  -- Conjunctions on the left can always be decomposed.
  let h14 := h1.left
  let h15 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h14
  case inl h16 =>
    -- Conjunctions on the left can always be decomposed.
    let h17 := h15.left
    let h18 := h15.right
    -- Conjunctions on the left can always be decomposed.
    let h19 := h18.left
    let h20 := h18.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h19
  case inr h21 =>
    -- Conjunctions on the left can always be decomposed.
    let h22 := h15.left
    let h23 := h15.right
    -- Conjunctions on the left can always be decomposed.
    let h24 := h23.left
    let h25 := h23.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h24



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_139795386984122299629571184033 : (((p2 ∨ (True → (((((p5 → p5) ∧ ((p2 ∧ p3) ∨ p1)) → (p4 ∨ p2)) ∨ True) ∨ ((False ∨ p1) ∨ p2)))) → False) → ((p5 ∧ p5) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p2 ∨ (True → (((((p5 → p5) ∧ ((p2 ∧ p3) ∨ p1)) → (p4 ∨ p2)) ∨ True) ∨ ((False ∨ p1) ∨ p2)))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_243425124657071946887705952611 : ((p5 → True) ∧ (((False → (True ∨ (p4 → p2))) ∨ p3) ∧ (p2 → (((p3 ∨ (((False ∨ p4) → (p3 ∨ (p5 ∧ p3))) → p5)) ∨ p5) ∨ p2)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347877411098404083194474611031 : (p3 → ((p4 → (False ∨ False)) → ((((p3 → (p2 ∨ (False ∨ (p2 ∨ p1)))) ∧ p1) ∨ (p2 → (p3 ∨ (p2 ∨ (p1 → p2))))) ∧ (p3 ∨ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_678346196914486741654088336919 : (((((p2 → (False → (p1 ∨ (p2 → p4)))) ∧ (((p3 ∧ (p2 → p3)) → ((p1 ∧ p1) ∧ p3)) ∧ p1)) ∨ (True ∧ ((p4 → p3) → True))) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_949682103518519400963744980162 : (((((True → p1) ∨ p1) ∧ (((False ∨ p3) → (p1 ∨ (True ∨ p4))) ∧ ((((p1 ∧ (p5 ∨ (False → (p2 ∧ p3)))) → p2) ∨ False) ∧ p5))) → p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h3.left
    let h6 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h9 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h10 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h11 := h4 h10
      -- One of the premise coincides with the conclusion.
      exact h11
    case inr h12 =>
      -- False on the left can always be used.
      apply False.elim h12
  case inr h13 =>
    -- Conjunctions on the left can always be decomposed.
    let h14 := h3.left
    let h15 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h16 := h15.left
    let h17 := h15.right
    -- Disjunctions on the left can always be decomposed.
    cases h16
    case inl h18 =>
      -- One of the premise coincides with the conclusion.
      exact h13
    case inr h19 =>
      -- False on the left can always be used.
      apply False.elim h19
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114003998046188896253927075339 : ((((((True ∨ p2) ∨ (p3 → (True ∨ (False ∨ ((p1 ∧ p4) ∧ ((p5 ∧ False) ∧ p1)))))) → p2) ∧ p4) ∨ (p3 ∨ (p5 → True))) ∨ (p3 ∨ p1)) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228988413276660397009244169680 : ((p5 ∨ (True ∧ p2)) ∨ ((((p2 ∨ p2) ∨ p4) ∧ (True ∧ False)) ∨ ((p3 → (p4 ∧ (p2 → True))) → ((p1 ∧ ((p3 → p1) ∧ p1)) → True)))) := by
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
theorem thm_5_vars_5224990265964594262899213613 : ((((p3 → ((((p2 ∧ (((p5 ∨ (p5 ∧ (p4 ∧ p2))) ∧ False) → (p3 → (p2 → (p3 ∨ p5))))) → p1) ∧ p2) ∨ p4)) ∨ True) ∧ True) ∧ True) := by
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
theorem thm_5_vars_157062431898475963877989866958 : (((p5 ∧ ((((p3 ∧ True) ∧ (p2 ∧ False)) ∨ p5) ∨ ((p4 ∨ (p4 ∧ p4)) → (p5 ∨ p1)))) ∨ p2) ∨ (((p4 → (True → False)) → p2) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54111885828659611407915839162 : (((p3 ∧ (True ∧ ((p4 ∨ p2) → (p4 ∨ (p3 ∨ True))))) → (((p4 → ((p4 ∨ p2) → ((False ∧ p4) ∨ False))) ∧ (p2 ∨ p3)) ∧ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200888655759886320523122523822 : ((False ∨ ((p2 → p2) ∧ (False ∨ (p4 ∨ p3)))) → (((((True ∨ p4) → (p3 ∧ p1)) ∨ p2) ∧ p3) ∨ ((((p4 ∧ True) ∧ p4) ∧ p2) → p4))) := by
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
    cases h5
    case inl h6 =>
      -- False on the left can always be used.
      apply False.elim h6
    case inr h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h9
        -- Conjunctions on the left can always be decomposed.
        let h10 := h9.left
        let h11 := h9.right
        -- Conjunctions on the left can always be decomposed.
        let h12 := h10.left
        let h13 := h10.right
        -- Conjunctions on the left can always be decomposed.
        let h14 := h12.left
        let h15 := h12.right
        -- One of the premise coincides with the conclusion.
        exact h13
      case inr h16 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h17
        -- Conjunctions on the left can always be decomposed.
        let h18 := h17.left
        let h19 := h17.right
        -- Conjunctions on the left can always be decomposed.
        let h20 := h18.left
        let h21 := h18.right
        -- Conjunctions on the left can always be decomposed.
        let h22 := h20.left
        let h23 := h20.right
        -- One of the premise coincides with the conclusion.
        exact h21



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41923260227782648379313487276 : ((((p4 ∧ (p1 ∨ p4)) → (p5 → (((False → ((p4 ∨ (p3 ∨ p4)) → p3)) ∧ p2) ∨ (p2 ∨ ((p5 → p1) → (p5 → p1)))))) ∨ False) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- Implications on the right can always be decomposed.
    intro h7
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- Implications on the right can always be decomposed.
    intro h10
    -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
    have h11 : p5 := by
      -- One of the premise coincides with the conclusion.
      exact h10
    -- We have shown the premise of h9, we can now drive its conclusion.
    let h12 := h9 h11
    -- One of the premise coincides with the conclusion.
    exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61853158344071057627145239807 : ((p2 ∧ (((True ∧ ((((True ∨ (p5 ∨ (p5 ∨ p4))) → p5) → p1) → False)) → (p2 → (p5 → ((True ∧ (p1 ∨ p5)) ∧ True)))) → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41526537719742668371466995650 : ((((False ∨ ((p4 → (False ∨ (False ∧ p3))) ∧ (p3 ∧ p4))) ∧ (p2 → (True ∧ (((p4 ∧ (p2 ∧ p1)) → p1) ∧ (p4 → p2))))) ∨ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_194013455842809762101215592557 : ((p4 ∨ ((True ∨ (False → True)) ∧ (False → (True ∧ p2)))) → ((p4 ∧ ((p4 → p4) ∧ False)) ∨ ((p3 ∧ p4) ∨ (((False → True) ∧ p5) ∨ True)))) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192800564191893355246513667791 : (((p4 ∨ (p3 → (p5 ∧ ((p3 → p5) ∨ p4)))) → p3) → ((((p3 → True) ∨ ((p3 → ((p5 ∨ (p5 ∨ p5)) → p2)) ∨ p2)) → p3) → p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : ((p3 → True) ∨ ((p3 → ((p5 ∨ (p5 ∨ p5)) → p2)) ∨ p2)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h4
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h3
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_799345544748517521736268759493 : (((p1 → (p5 ∧ (((False ∧ p5) ∨ p1) → ((p2 → ((p5 → ((p3 ∧ (p5 ∨ p5)) → False)) → p1)) → (p2 ∧ ((p3 ∧ p4) ∧ p1)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137884519085881405210228008426 : ((p4 ∨ (((True ∧ (True ∨ p4)) → (p4 → (((p1 ∧ p3) ∨ ((True ∨ p4) → (True ∨ (p2 ∧ p1)))) ∨ True))) ∨ p4)) ∨ (True ∨ (True → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_606697446578345744045344419471 : ((((((False ∨ (((False ∨ p3) ∨ ((p2 ∨ False) ∨ (False → (True → p1)))) ∨ ((p3 → True) → (False → p4)))) ∧ (p5 ∧ p5)) ∧ p3) ∨ True) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_149135898090606873863667991679 : (((p4 ∧ p2) ∧ (p5 → ((((p1 → p3) → p1) ∨ (p3 ∧ (p1 ∨ (p3 → p4)))) ∧ ((p4 → False) ∧ True)))) ∨ (True → (p2 ∨ (False → False)))) := by
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
theorem thm_5_vars_116670068002285121240921742338 : (((p5 → True) ∧ (((p5 ∧ ((True → (p5 → (p1 ∧ False))) → (p2 ∧ p3))) ∧ (False ∨ p2)) ∨ ((p1 ∧ (p4 ∧ p5)) → p1))) ∨ (p3 ∧ p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234249346985707861028980438427 : ((False → (p4 ∨ True)) → ((False ∨ p3) ∨ (((p2 ∨ p2) ∨ (p3 ∧ (p3 ∨ (False → False)))) ∨ ((((p3 → True) ∧ (p4 ∧ p3)) ∧ False) → p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h6.left
  let h8 := h6.right
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1475368478397261798440808382 : (((p2 ∨ ((((p2 ∨ ((p2 ∧ False) ∨ ((p4 ∨ p1) ∧ False))) ∧ (True ∨ (p4 → p1))) ∨ (p2 ∧ p3)) ∧ p3)) ∨ p2) ∨ (p3 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_618292289587724259891743142538 : ((((((p3 ∧ p2) ∨ (p3 → p4)) ∨ (((p5 ∨ (p5 → ((((p3 ∧ True) ∨ p1) → (p5 ∨ False)) ∧ p1))) ∨ (p1 ∨ True)) → p4)) ∨ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112809206380258660208628475406 : ((((((p3 ∨ p2) → (False ∨ p2)) → p2) → (((False → (p2 ∨ (p3 ∧ p3))) ∧ (p2 ∧ ((p3 → True) ∧ p2))) → False)) → False) ∨ (p1 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49253260586765788626929720887 : (((True ∧ (p2 ∨ (((True → ((((p3 → ((p1 ∨ (False ∧ p3)) ∧ p5)) ∧ True) ∧ p2) → True)) → p2) ∨ True))) ∨ (p5 ∨ (p1 ∧ True))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_65433243336300615482546321734 : ((p3 ∨ ((p4 ∧ p5) ∧ (((False ∨ (p3 ∧ True)) ∨ (((p4 ∧ p2) ∨ False) ∨ p4)) ∨ ((True → ((p3 ∧ p1) ∨ p3)) → (p3 → p2))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174236629347320430165573996502 : (((p1 ∧ (((True ∧ False) ∧ p2) → (p5 → ((True → p1) ∨ p3)))) → (p3 ∧ True)) → (((p1 → p5) → p3) ∨ ((p3 ∨ (True ∧ True)) ∧ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116250028301109362795522208517 : ((((p3 → p1) → p3) ∨ (p4 ∧ ((True ∧ p1) ∧ (p1 → (p5 ∧ ((p2 → (((p5 ∨ (p3 ∧ p3)) ∧ p4) → p1)) → p3)))))) ∨ (False → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_188857808356498190840559351594 : ((((False → p1) → (True ∨ False)) ∨ ((p3 ∧ False) → True)) ∧ (((((True ∧ (p5 ∨ True)) → False) → (p2 ∨ ((p1 ∨ p3) ∧ p3))) ∨ p1) ∨ p3)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (True ∧ (p5 ∨ True)) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37476918128127025004203174498 : ((((((p1 → (p3 ∨ False)) ∧ p2) ∧ (p1 ∧ ((((p1 ∨ p1) ∨ (True ∧ p4)) → p2) → (True → (p1 → (p2 ∧ p3)))))) ∨ p1) ∧ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147761405141740001311247951431 : ((((p5 → (p3 ∧ False)) → ((p4 ∨ ((p1 ∨ (False ∧ ((p5 ∧ p2) → (p4 ∨ p3)))) → p2)) ∨ p5)) → p2) ∨ (((p3 → p5) → True) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317955835779015683592792154601 : (p4 ∨ ((p5 ∨ ((((p3 → (((((True → p5) ∨ True) ∨ p3) ∧ True) ∨ (p3 ∨ True))) ∨ p5) → p1) → ((p4 ∧ False) ∨ (p4 → p2)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_751006543105636035857601294346 : (((True ∧ (((p4 → p1) ∨ (p3 ∨ (False → p3))) → (p2 → ((True ∧ (p1 ∨ True)) → ((p1 ∧ p5) ∨ (((p3 → True) → p1) ∨ p3)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_264277980028866946852973699745 : (True ∧ ((p2 ∧ ((p3 → (False ∧ p4)) → p2)) ∨ ((p2 → p3) ∨ (p3 ∨ ((p3 ∨ (p4 ∧ p1)) → ((p2 → ((p5 → p2) ∨ p1)) ∨ False)))))) := by
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
    -- Implications on the right can always be decomposed.
    intro h4
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h8
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65211500437729126169283090545 : ((p3 ∨ (((((((p3 ∨ p3) ∧ ((p4 ∨ True) ∨ False)) → ((p1 → True) ∧ False)) ∨ True) ∨ p4) ∧ ((p1 ∨ p3) → (False ∧ p2))) ∨ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111833860219234511740667065045 : (((((p1 ∧ (p5 ∨ (((p3 ∨ (p3 ∧ True)) → True) → (False ∨ (p5 ∨ (p1 → p2)))))) ∨ True) ∨ (p1 → (p4 → p3))) ∨ p5) ∨ (False → p5)) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199688805664376671165430312983 : ((((p2 → True) → (p1 ∨ (p1 ∧ p1))) → p5) → (((p5 ∨ (p4 ∨ (False → p4))) ∨ (((p4 ∨ p5) ∨ p2) ∧ (p3 ∧ False))) ∨ (True → p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147387145192093466643185961822 : (((((p3 ∧ ((p4 → (p4 → p5)) ∨ p2)) ∨ False) ∧ ((p1 ∧ (p3 → ((True → p3) → p1))) ∧ p2)) ∨ True) ∨ ((False → p5) ∨ (True → True))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64112837080296345337891238050 : ((False ∨ (((((True → p1) → True) ∧ True) → False) ∧ (p3 → (p4 ∨ (((p4 ∧ p3) ∧ ((p1 ∧ p3) ∧ ((True ∧ p5) ∧ True))) → p2))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158249390828323855859843742594 : ((((p4 ∨ p4) ∨ p4) ∨ (((p1 ∨ False) → p3) ∨ (((p2 ∧ (True ∧ False)) ∧ (p2 ∨ True)) ∨ p4))) ∨ (True ∧ (p2 → (p4 → (True ∨ False))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42921339793423053936105046390 : (((p4 → (((p5 → p1) → ((p1 → p5) ∨ ((((p3 → p3) ∨ (p4 → p3)) ∨ True) ∧ ((p3 ∧ (p3 ∨ p2)) ∨ True)))) ∧ p3)) ∨ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345692386766441690804429818098 : (p3 → ((p5 ∨ ((((False → (True ∧ ((((p4 ∧ p4) ∨ False) ∧ False) ∧ (((p5 → p1) → True) → True)))) → p2) ∧ (p1 → p2)) ∨ p3)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_726508910399150566398204324915 : (((((p3 → p4) ∨ p5) ∨ (((((p4 ∨ p1) ∧ (p3 ∨ (p5 → (p5 ∨ ((True ∨ p2) ∨ p5))))) ∨ (p5 → p2)) ∧ True) ∧ (False ∨ True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_876878596947796566489438949030 : (((((p2 ∨ (p3 → (p1 ∧ (((p3 → (p3 ∧ True)) → p4) → (True ∧ False))))) ∧ (p5 → ((p4 → (p4 → True)) ∧ False))) ∧ (p4 ∧ p3)) → p2) ∧ True) := by
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
    let h7 := h3.left
    let h8 := h3.right
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h3.left
    let h11 := h3.right
    -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
    have h12 : p3 := by
      -- One of the premise coincides with the conclusion.
      exact h11
    -- We have shown the premise of h9, we can now drive its conclusion.
    let h13 := h9 h12
    -- We need to get the right conjuct of h13 based on <expert-advice>.
    let h14 := h13.right
    -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
    have h15 : ((p3 → (p3 ∧ True)) → p4) := by
      -- Implications on the right can always be decomposed.
      intro h16
      -- One of the premise coincides with the conclusion.
      exact h10
    -- We have shown the premise of h14, we can now drive its conclusion.
    let h17 := h14 h15
    -- We need to get the right conjuct of h17 based on <expert-advice>.
    let h18 := h17.right
    -- False on the left can always be used.
    apply False.elim h18
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52828789502003955892026425554 : ((((p5 → (p3 → True)) ∧ ((((p5 ∧ p5) ∨ p1) ∧ (p2 ∧ p2)) ∨ p5)) → ((((p1 ∨ (p1 ∧ True)) ∧ p1) ∨ (p2 → p5)) ∨ True)) ∨ p3) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Conjunctions on the left can always be decomposed.
      let h10 := h6.left
      let h11 := h6.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h6.left
      let h14 := h6.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h15 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_140008400743829897961134815929 : (((((((p1 → p3) → p1) → True) ∨ ((p1 → (((p4 ∧ (False → p2)) ∧ p3) ∨ p5)) ∧ False)) ∨ p5) ∨ (True ∨ p2)) → ((p2 ∧ p4) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h3 =>
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
        -- False on the left can always be used.
        apply False.elim h7
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h9 =>
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_624305673907192373126022591865 : ((((p3 ∨ ((((p3 ∨ (p4 ∧ (p1 → ((p2 ∧ (False ∨ p3)) ∧ p5)))) → False) → (p2 → p2)) ∨ (((p1 ∧ p4) ∨ p5) ∧ p2))) ∨ p3) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53068967028283182305267409996 : (((p1 ∧ ((p1 ∨ p1) ∧ (p4 → (p5 → ((p5 ∧ False) ∧ True))))) ∧ ((((p4 ∧ True) ∧ p5) ∨ (p5 ∧ (p3 → True))) ∨ (p1 ∧ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_262398295499678981169854715965 : (True ∧ (((p2 ∨ p3) → (((p1 ∧ ((True → (p5 ∧ (p2 → (((True ∧ p3) ∧ p3) → False)))) → p1)) ∨ ((False → p1) ∧ True)) ∨ p4)) ∨ p2)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h5
    -- False on the left can always be used.
    apply False.elim h5
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_194826039368511099804842870472 : (((((False ∧ True) ∧ (p4 → p5)) ∧ p5) → True) ∧ (((((p3 → p4) ∧ ((p1 ∧ (True ∧ (p5 → p4))) ∧ (p4 ∧ p2))) ∧ True) ∧ p5) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114494958529500544522228123419 : (((((((p1 → (p1 ∧ p3)) → p1) ∧ p1) ∧ False) → ((((False ∨ True) ∧ p3) ∨ False) ∧ p5)) → ((p5 → False) ∨ (True ∨ p1))) ∨ (p4 → p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204637802490247545311994935686 : (((p1 ∧ ((p2 ∨ p1) ∧ p1)) ∨ False) ∨ (False → (p2 ∨ ((((p5 → p4) ∧ p3) → True) ∨ (p4 ∨ (((p2 ∧ p1) → (p2 → p3)) ∨ p5)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1856724676663066614553515398 : ((((p5 ∨ (p3 → p5)) ∧ (p3 ∧ (True ∨ p4))) ∧ (((p2 ∧ p2) ∨ (p4 → True)) ∧ ((False ∨ p4) ∧ p4))) → ((p2 ∧ p5) ∨ p3)) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h3.left
      let h11 := h3.right
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h12 =>
        -- Conjunctions on the left can always be decomposed.
        let h13 := h12.left
        let h14 := h12.right
        -- Conjunctions on the left can always be decomposed.
        let h15 := h11.left
        let h16 := h11.right
        -- Disjunctions on the left can always be decomposed.
        cases h15
        case inl h17 =>
          -- False on the left can always be used.
          apply False.elim h17
        case inr h18 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h7
      case inr h19 =>
        -- Conjunctions on the left can always be decomposed.
        let h20 := h11.left
        let h21 := h11.right
        -- Disjunctions on the left can always be decomposed.
        cases h20
        case inl h22 =>
          -- False on the left can always be used.
          apply False.elim h22
        case inr h23 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h7
    case inr h24 =>
      -- Conjunctions on the left can always be decomposed.
      let h25 := h3.left
      let h26 := h3.right
      -- Disjunctions on the left can always be decomposed.
      cases h25
      case inl h27 =>
        -- Conjunctions on the left can always be decomposed.
        let h28 := h27.left
        let h29 := h27.right
        -- Conjunctions on the left can always be decomposed.
        let h30 := h26.left
        let h31 := h26.right
        -- Disjunctions on the left can always be decomposed.
        cases h30
        case inl h32 =>
          -- False on the left can always be used.
          apply False.elim h32
        case inr h33 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h7
      case inr h34 =>
        -- Conjunctions on the left can always be decomposed.
        let h35 := h26.left
        let h36 := h26.right
        -- Disjunctions on the left can always be decomposed.
        cases h35
        case inl h37 =>
          -- False on the left can always be used.
          apply False.elim h37
        case inr h38 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h7
  case inr h39 =>
    -- Conjunctions on the left can always be decomposed.
    let h40 := h5.left
    let h41 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h41
    case inl h42 =>
      -- Conjunctions on the left can always be decomposed.
      let h43 := h3.left
      let h44 := h3.right
      -- Disjunctions on the left can always be decomposed.
      cases h43
      case inl h45 =>
        -- Conjunctions on the left can always be decomposed.
        let h46 := h45.left
        let h47 := h45.right
        -- Conjunctions on the left can always be decomposed.
        let h48 := h44.left
        let h49 := h44.right
        -- Disjunctions on the left can always be decomposed.
        cases h48
        case inl h50 =>
          -- False on the left can always be used.
          apply False.elim h50
        case inr h51 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h40
      case inr h52 =>
        -- Conjunctions on the left can always be decomposed.
        let h53 := h44.left
        let h54 := h44.right
        -- Disjunctions on the left can always be decomposed.
        cases h53
        case inl h55 =>
          -- False on the left can always be used.
          apply False.elim h55
        case inr h56 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h40
    case inr h57 =>
      -- Conjunctions on the left can always be decomposed.
      let h58 := h3.left
      let h59 := h3.right
      -- Disjunctions on the left can always be decomposed.
      cases h58
      case inl h60 =>
        -- Conjunctions on the left can always be decomposed.
        let h61 := h60.left
        let h62 := h60.right
        -- Conjunctions on the left can always be decomposed.
        let h63 := h59.left
        let h64 := h59.right
        -- Disjunctions on the left can always be decomposed.
        cases h63
        case inl h65 =>
          -- False on the left can always be used.
          apply False.elim h65
        case inr h66 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h40
      case inr h67 =>
        -- Conjunctions on the left can always be decomposed.
        let h68 := h59.left
        let h69 := h59.right
        -- Disjunctions on the left can always be decomposed.
        cases h68
        case inl h70 =>
          -- False on the left can always be used.
          apply False.elim h70
        case inr h71 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h40



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354735471255220157787884383245 : (p5 → (((p4 ∧ ((p4 ∨ ((p2 ∨ p3) ∧ p1)) → (p2 ∨ ((((p2 ∧ p2) ∧ p2) ∧ p1) ∨ False)))) ∨ ((False ∨ p1) → (p2 ∨ p1))) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351257363964383467178554727170 : (p4 → ((p4 ∧ ((p1 ∨ (((p3 → p1) ∨ ((p5 → p4) ∨ p2)) ∧ (True ∨ (((p2 ∨ False) → p5) ∨ p4)))) → False)) ∨ ((False → p4) ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149063874287198917659692032502 : ((((False → p5) ∧ p4) → (False ∨ ((((False ∧ False) → ((p3 ∧ (True → p3)) ∨ p3)) → p5) ∨ (p5 → p4)))) ∨ (False ∧ (p1 → (p5 ∨ p2)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150677410257935380466918319542 : (((p1 → (((False → ((False ∨ ((p4 → False) ∧ p4)) → (p1 → ((p5 ∧ p1) ∨ p5)))) ∧ p1) ∧ p5)) ∧ p5) → ((p4 ∧ (True → p3)) → p3)) := by
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
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h7 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h8 := h4 h7
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62059674105463789017002435115 : ((p2 ∧ ((False → p5) → ((True → ((p3 → p1) ∧ (p3 → (False ∨ p2)))) ∨ ((False ∧ True) ∧ ((p4 ∧ p4) ∨ ((p4 ∧ p2) ∨ True)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66516552944687036826772782015 : ((True → (((True ∧ (((((p4 → p5) → p1) ∨ p1) ∧ (((False ∨ p2) ∧ p1) → p4)) → (p4 ∨ ((p2 ∧ p2) → p3)))) ∨ p3) → p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44286825775946626036929084005 : (((((p3 ∨ (((p4 → (p5 → p4)) ∨ False) ∨ ((p2 → (True → p4)) ∨ p3))) → p5) ∧ ((p4 ∨ ((p4 → p4) ∧ p4)) ∨ False)) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_657224638451802096414591616638 : ((((((p3 → False) → p3) → ((((((True → False) ∨ p5) ∨ ((p2 ∧ (p3 ∧ (p1 ∨ p3))) ∧ True)) ∨ True) ∧ p3) → p2)) ∨ (p3 → p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_711890069254092358806529084564 : (((((p3 ∨ ((p3 ∨ p5) ∧ p5)) ∧ False) ∨ (((((False ∨ p1) ∨ p2) ∧ p4) ∧ ((p4 ∨ False) → (((p3 ∨ p4) → p1) ∧ p5))) ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167307736748426003196155207894 : (((((False → (p1 ∧ p3)) → (((p2 ∨ True) → (p1 ∨ False)) ∨ (False → False))) → False) → True) → (p3 → ((p1 ∧ (p2 ∧ (True → False))) → p3))) := by
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
  let h6 := h5.left
  let h7 := h5.right
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_349214372926577051973419662473 : (p3 → (p1 → (((p4 ∨ (p2 ∧ (p5 ∧ (p4 → (p5 ∨ (p3 → False)))))) → (True → (((p2 → p4) ∧ (p3 ∧ (False ∨ True))) ∧ p1))) ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_352667924651440058327103458395 : (p4 → ((False ∨ p1) ∨ (((((((False ∧ (True ∧ False)) → (False ∨ (p1 ∧ p4))) ∧ True) ∧ True) → p1) ∧ (True ∨ (p1 ∧ p1))) ∨ (p4 ∨ p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_589840790770333163614303284422 : (((((((((((p5 → (p3 → p4)) ∧ (p1 → p3)) → True) → (p4 ∨ (p2 ∧ True))) ∧ True) → p3) ∧ ((True ∨ True) → p2)) → p5) ∧ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_513481833438174494883960528418 : ((((False ∨ False) ∨ ((((False ∨ (p4 → ((((False → p2) ∧ p1) ∨ True) ∧ True))) ∧ p5) → (False ∧ p1)) ∨ (p5 ∨ (True ∧ (True ∨ p1))))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213524602614969866054160191662 : (((p5 → (p1 ∨ p3)) ∧ p5) ∨ ((((((p1 ∨ p5) → p3) ∧ p5) → (p5 ∧ (((p4 → (False ∨ False)) ∨ p1) ∨ p3))) ∨ p5) ∨ (False → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_798086719301090764978096568212 : (((p1 → ((((((p1 → (False → True)) ∧ ((p4 ∨ p4) ∧ p1)) ∨ p3) ∨ (p5 ∧ (p3 ∨ (p3 ∧ p2)))) ∨ p1) → ((False ∨ False) ∨ p1))) ∨ False) ∧ True) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h5 =>
        -- Conjunctions on the left can always be decomposed.
        let h6 := h5.left
        let h7 := h5.right
        -- Conjunctions on the left can always be decomposed.
        let h8 := h7.left
        let h9 := h7.right
        -- Disjunctions on the left can always be decomposed.
        cases h8
        case inl h10 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h1
        case inr h11 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h1
      case inr h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h1
    case inr h13 =>
      -- Conjunctions on the left can always be decomposed.
      let h14 := h13.left
      let h15 := h13.right
      -- Disjunctions on the left can always be decomposed.
      cases h15
      case inl h16 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h1
      case inr h17 =>
        -- Conjunctions on the left can always be decomposed.
        let h18 := h17.left
        let h19 := h17.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h1
  case inr h20 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180900242633972765361174968389 : (((p2 ∧ (True → p4)) → (((p5 ∧ False) ∨ p5) → (True ∨ (p4 ∨ p2)))) → (((False ∨ (((p5 ∨ p3) ∧ (p4 ∨ p3)) → False)) ∧ p4) → p4)) := by
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
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47494188353310427529252613875 : (((p1 ∨ ((((p4 → (p1 ∧ p1)) → (False → (p1 ∨ ((((True → True) ∨ (p1 ∨ False)) → True) ∧ p4)))) ∧ p4) ∧ False)) ∨ (p5 ∨ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40527702763662360457289860243 : ((((False ∨ (False ∧ ((True → True) → (p4 ∨ (p3 ∨ ((False → p1) → (((p3 → False) ∨ (p5 ∨ (False ∨ p5))) ∨ p5))))))) ∨ p5) ∨ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



