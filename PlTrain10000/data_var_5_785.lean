variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118833557152111462003390569186 : ((True → (((False → (((p1 ∨ (False ∧ ((False ∨ p3) ∨ (p4 ∨ False)))) → (p3 ∨ False)) ∧ (p1 → False))) → p5) ∨ (p4 ∨ p4))) ∨ (True → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40003236377835982079725381828 : (((p5 → (((p1 → (False → (p1 ∧ p2))) → (True → True)) → ((((p5 ∧ p4) ∧ True) → True) ∧ (p1 ∨ (p1 ∧ (False ∨ True)))))) ∧ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115994352313300805361862746874 : ((((True ∧ (p1 ∨ True)) → p5) → (p4 ∨ ((((True ∨ p5) ∧ ((((p4 ∧ p5) → p5) ∧ False) ∧ p4)) ∨ p4) ∨ (False ∧ True)))) ∨ (p4 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48042584964814185973530474115 : ((((p2 → ((p5 ∨ p1) → ((p2 ∧ (False ∨ False)) ∨ p2))) ∨ ((p4 → p2) ∨ ((p2 → p4) ∨ (False → (p3 ∨ p4))))) → (p1 ∧ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_24168410043907224922607697924 : (((True ∨ (False → (True → p5))) → ((((p4 ∧ (True ∨ p1)) ∨ False) ∨ (p1 → True)) → ((p5 → False) → ((p1 → (False ∨ True)) ∨ True)))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Disjunctions on the left can always be decomposed.
        cases h1
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
      case inr h11 =>
        -- Disjunctions on the left can always be decomposed.
        cases h1
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
      -- False on the left can always be used.
      apply False.elim h14
  case inr h15 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h16 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h17 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_663150507672441833666667670842 : (((((p4 ∨ p5) ∧ ((True ∧ p3) → ((((p3 → p3) ∨ (p4 → False)) ∨ (False ∨ p3)) → ((p1 → p1) ∧ (True → p3))))) → (p3 ∨ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156969558256593513765116409877 : ((((((p3 ∨ (p3 ∨ p5)) ∨ p2) → ((p5 → p1) → p5)) ∨ ((p2 ∧ (p4 ∨ p1)) ∨ True)) ∨ True) ∨ ((((p1 → p4) ∨ p4) → p4) → p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_787902859976926111361362238449 : (((p4 ∨ (p3 → (((p4 ∨ True) ∧ (p5 ∧ (p4 ∧ (((p1 ∧ p5) ∨ p3) ∧ ((True ∧ (p3 → p2)) ∧ (p1 ∨ p5)))))) ∨ (p5 → p3)))) ∨ p2) ∧ True) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185305858596210060180504154141 : ((p3 ∧ (((p3 ∨ (p4 → (p1 ∨ (p3 ∨ p2)))) ∧ p5) ∧ p3)) ∨ ((((p3 → (True → (p4 ∧ p2))) → (False ∧ p4)) ∧ p1) ∨ (True ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65299316285170335797995388564 : ((p3 ∨ (((p5 ∨ (p1 ∨ (p2 ∨ ((p1 → (((p2 ∧ p3) ∧ (True → True)) ∧ p5)) ∧ (p1 ∧ (False ∧ True)))))) → True) → (p1 → p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301059874921494427589326650605 : (False ∨ (((p1 ∧ p2) ∨ (((p2 ∧ (p2 → True)) → p5) → p3)) ∨ ((((False ∧ (True → (False ∨ True))) ∧ (True ∧ False)) ∧ (p3 ∨ p3)) → p3))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232388022962642930473972264767 : (((p5 → p2) → True) → (((False → (p1 ∧ p2)) → p1) → ((p3 → ((p4 → True) ∧ ((p2 ∧ p5) ∨ p1))) ∨ (((p1 ∨ p4) ∨ p5) ∧ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h5 : (False → (p1 ∧ p2)) := by
    -- Implications on the right can always be decomposed.
    intro h6
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- False on the left can always be used.
    apply False.elim h6
    -- False on the left can always be used.
    apply False.elim h6
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h7 := h2 h5
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180662074863806369034732145608 : (((p4 → (p4 ∧ ((p1 → True) ∨ p3))) ∨ (False → (p5 ∧ (p2 ∨ p3)))) → ((p2 ∨ (p2 ∨ (((p1 ∨ p5) ∨ (p2 ∨ p3)) ∨ True))) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_141164029391928881882196979593 : (((p2 ∨ (((False → p1) ∧ p2) ∧ p2)) ∧ (((p5 ∨ (p1 → p5)) ∧ ((False → (p4 ∧ p5)) ∧ p1)) ∧ (p3 ∨ p3))) → (p1 ∧ (p5 ∨ False))) := by
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
    let h7 := h5.left
    let h8 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h8.left
      let h11 := h8.right
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h12 =>
        -- One of the premise coincides with the conclusion.
        exact h11
      case inr h13 =>
        -- One of the premise coincides with the conclusion.
        exact h11
    case inr h14 =>
      -- Conjunctions on the left can always be decomposed.
      let h15 := h8.left
      let h16 := h8.right
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h17 =>
        -- One of the premise coincides with the conclusion.
        exact h16
      case inr h18 =>
        -- One of the premise coincides with the conclusion.
        exact h16
  case inr h19 =>
    -- Conjunctions on the left can always be decomposed.
    let h20 := h19.left
    let h21 := h19.right
    -- Conjunctions on the left can always be decomposed.
    let h22 := h20.left
    let h23 := h20.right
    -- Conjunctions on the left can always be decomposed.
    let h24 := h3.left
    let h25 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h26 := h24.left
    let h27 := h24.right
    -- Disjunctions on the left can always be decomposed.
    cases h26
    case inl h28 =>
      -- Conjunctions on the left can always be decomposed.
      let h29 := h27.left
      let h30 := h27.right
      -- Disjunctions on the left can always be decomposed.
      cases h25
      case inl h31 =>
        -- One of the premise coincides with the conclusion.
        exact h30
      case inr h32 =>
        -- One of the premise coincides with the conclusion.
        exact h30
    case inr h33 =>
      -- Conjunctions on the left can always be decomposed.
      let h34 := h27.left
      let h35 := h27.right
      -- Disjunctions on the left can always be decomposed.
      cases h25
      case inl h36 =>
        -- One of the premise coincides with the conclusion.
        exact h35
      case inr h37 =>
        -- One of the premise coincides with the conclusion.
        exact h35
  -- Conjunctions on the left can always be decomposed.
  let h38 := h1.left
  let h39 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h38
  case inl h40 =>
    -- Conjunctions on the left can always be decomposed.
    let h41 := h39.left
    let h42 := h39.right
    -- Conjunctions on the left can always be decomposed.
    let h43 := h41.left
    let h44 := h41.right
    -- Disjunctions on the left can always be decomposed.
    cases h43
    case inl h45 =>
      -- Conjunctions on the left can always be decomposed.
      let h46 := h44.left
      let h47 := h44.right
      -- Disjunctions on the left can always be decomposed.
      cases h42
      case inl h48 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h45
      case inr h49 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h45
    case inr h50 =>
      -- Conjunctions on the left can always be decomposed.
      let h51 := h44.left
      let h52 := h44.right
      -- Disjunctions on the left can always be decomposed.
      cases h42
      case inl h53 =>
        -- We want to use the implication h50 based on <expert-advice>. So we show its premise.
        have h54 : p1 := by
          -- One of the premise coincides with the conclusion.
          exact h52
        -- We have shown the premise of h50, we can now drive its conclusion.
        let h55 := h50 h54
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h55
      case inr h56 =>
        -- We want to use the implication h50 based on <expert-advice>. So we show its premise.
        have h57 : p1 := by
          -- One of the premise coincides with the conclusion.
          exact h52
        -- We have shown the premise of h50, we can now drive its conclusion.
        let h58 := h50 h57
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h58
  case inr h59 =>
    -- Conjunctions on the left can always be decomposed.
    let h60 := h59.left
    let h61 := h59.right
    -- Conjunctions on the left can always be decomposed.
    let h62 := h60.left
    let h63 := h60.right
    -- Conjunctions on the left can always be decomposed.
    let h64 := h39.left
    let h65 := h39.right
    -- Conjunctions on the left can always be decomposed.
    let h66 := h64.left
    let h67 := h64.right
    -- Disjunctions on the left can always be decomposed.
    cases h66
    case inl h68 =>
      -- Conjunctions on the left can always be decomposed.
      let h69 := h67.left
      let h70 := h67.right
      -- Disjunctions on the left can always be decomposed.
      cases h65
      case inl h71 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h68
      case inr h72 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h68
    case inr h73 =>
      -- Conjunctions on the left can always be decomposed.
      let h74 := h67.left
      let h75 := h67.right
      -- Disjunctions on the left can always be decomposed.
      cases h65
      case inl h76 =>
        -- We want to use the implication h73 based on <expert-advice>. So we show its premise.
        have h77 : p1 := by
          -- One of the premise coincides with the conclusion.
          exact h75
        -- We have shown the premise of h73, we can now drive its conclusion.
        let h78 := h73 h77
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h78
      case inr h79 =>
        -- We want to use the implication h73 based on <expert-advice>. So we show its premise.
        have h80 : p1 := by
          -- One of the premise coincides with the conclusion.
          exact h75
        -- We have shown the premise of h73, we can now drive its conclusion.
        let h81 := h73 h80
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h81



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51937985442259509868116450694 : ((((((True ∧ True) → (p4 ∧ (p4 ∧ True))) ∨ p3) ∨ (p3 ∧ (p1 → (p2 → p4)))) ∨ ((p3 → ((p5 ∨ p5) ∨ p5)) ∨ (p2 → True))) ∨ False) := by
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
theorem thm_5_vars_67696614271474152146342527458 : ((p1 → (p4 → ((p4 → (((p5 → (p1 ∨ p1)) ∧ (p3 ∧ p2)) ∨ ((p2 ∨ p3) ∧ (((p2 ∧ (True ∧ p1)) ∧ p5) → p1)))) ∨ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1510672010416784834124191071 : (((p3 → (True → ((p1 ∧ p5) ∨ (((p2 → True) ∨ p1) ∨ p1)))) ∧ ((((p2 ∧ p3) → False) → (p5 → False)) ∨ True)) ∨ (False ∨ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114455149997486221898904385855 : (((((p5 → p2) ∧ ((p4 ∨ ((False ∨ p4) → (p3 ∧ (False ∨ (p4 ∧ p4))))) → p2)) ∧ p2) → ((True ∨ (p2 → False)) → p4)) ∨ (p4 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314688762574530351688325223229 : (p3 ∨ ((((p4 ∨ p1) ∨ p3) ∧ (p4 → (((p4 → p4) → ((p5 ∨ p4) ∨ p5)) ∨ p3))) → (((p3 → p1) ∨ True) ∨ ((p1 ∧ p3) ∨ True)))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h6 =>
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
theorem thm_5_vars_231222233777487412547392797445 : (((p3 ∨ p4) ∨ p4) → (((True → (p1 → ((False → (((p5 → False) ∧ False) → False)) → (p3 → p1)))) → ((True ∨ p2) ∧ p5)) → (p5 ∨ p1))) := by
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
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h5 : (True → (p1 → ((False → (((p5 → False) ∧ False) → False)) → (p3 → p1)))) := by
        -- Implications on the right can always be decomposed.
        intro h6
        -- Implications on the right can always be decomposed.
        intro h7
        -- Implications on the right can always be decomposed.
        intro h8
        -- Implications on the right can always be decomposed.
        intro h9
        -- One of the premise coincides with the conclusion.
        exact h7
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h10 := h2 h5
      -- We need to get the right conjuct of h10 based on <expert-advice>.
      let h11 := h10.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h11
    case inr h12 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h13 : (True → (p1 → ((False → (((p5 → False) ∧ False) → False)) → (p3 → p1)))) := by
        -- Implications on the right can always be decomposed.
        intro h14
        -- Implications on the right can always be decomposed.
        intro h15
        -- Implications on the right can always be decomposed.
        intro h16
        -- Implications on the right can always be decomposed.
        intro h17
        -- One of the premise coincides with the conclusion.
        exact h15
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h18 := h2 h13
      -- We need to get the right conjuct of h18 based on <expert-advice>.
      let h19 := h18.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h19
  case inr h20 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h21 : (True → (p1 → ((False → (((p5 → False) ∧ False) → False)) → (p3 → p1)))) := by
      -- Implications on the right can always be decomposed.
      intro h22
      -- Implications on the right can always be decomposed.
      intro h23
      -- Implications on the right can always be decomposed.
      intro h24
      -- Implications on the right can always be decomposed.
      intro h25
      -- One of the premise coincides with the conclusion.
      exact h23
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h26 := h2 h21
    -- We need to get the right conjuct of h26 based on <expert-advice>.
    let h27 := h26.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h27



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231546202294971641804002075397 : (((p5 → True) ∨ p1) → ((p1 → (p4 → p1)) → ((((True ∧ ((p5 → p4) ∧ False)) ∨ ((p4 ∧ p5) → p4)) ∨ (p2 ∧ True)) ∨ (p3 ∧ p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h7 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- One of the premise coincides with the conclusion.
    exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_625089414427912274498424151385 : ((((True → ((True ∨ (p4 → (p2 → (p4 ∧ (p3 ∨ ((((p2 ∧ p4) ∧ (False ∨ False)) ∨ (False ∨ False)) → (True ∧ p1))))))) → False)) ∨ True) ∨ False) ∧ True) := by
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
theorem thm_5_vars_63943372088436048993357472136 : ((False ∨ (((((p4 → p3) → p5) → False) → (p5 → ((p2 ∨ (p4 ∨ (((False → (p3 ∧ True)) ∨ p2) → p2))) ∨ (p1 → False)))) ∨ p4)) ∨ p5) := by
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
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : ((p4 → p3) → p5) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h3
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257817105075706861597174031015 : ((p3 ∨ p5) → ((((p4 → (False ∧ p4)) ∧ (False → True)) ∨ p1) ∨ (((p4 → (p3 ∧ p5)) ∨ ((True → True) ∨ (True → (False ∧ p4)))) ∨ False))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_960314754502309150435674744267 : ((((p5 ∧ p3) ∧ (((False → p5) → ((p5 → (True ∧ (p3 ∧ (((p2 → False) ∨ (p1 ∨ (True → True))) ∧ p1)))) → (p5 → p1))) → p1)) → p1) ∧ True) := by
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
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h6 : ((False → p5) → ((p5 → (True ∧ (p3 ∧ (((p2 → False) ∨ (p1 ∨ (True → True))) ∧ p1)))) → (p5 → p1))) := by
    -- Implications on the right can always be decomposed.
    intro h7
    -- Implications on the right can always be decomposed.
    intro h8
    -- Implications on the right can always be decomposed.
    intro h9
    -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
    have h10 : p5 := by
      -- One of the premise coincides with the conclusion.
      exact h9
    -- We have shown the premise of h8, we can now drive its conclusion.
    let h11 := h8 h10
    -- We need to get the right conjuct of h11 based on <expert-advice>.
    let h12 := h11.right
    -- We need to get the right conjuct of h12 based on <expert-advice>.
    let h13 := h12.right
    -- We need to get the right conjuct of h13 based on <expert-advice>.
    let h14 := h13.right
    -- One of the premise coincides with the conclusion.
    exact h14
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h15 := h3 h6
  -- One of the premise coincides with the conclusion.
  exact h15
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_339002071235962730143325313114 : (p1 → (True ∧ (((((p3 → p3) → (((p2 ∨ p5) ∧ p1) ∧ p3)) ∨ (p1 ∧ True)) → (((p5 ∨ ((True → p4) ∧ p2)) ∧ p4) ∧ True)) → p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (((p3 → p3) → (((p2 ∨ p5) ∧ p1) ∧ p3)) ∨ (p1 ∧ True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h1
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179124918948689386015921379164 : ((p1 ∧ ((True ∨ ((p2 ∨ False) ∨ (p2 ∨ ((p5 ∧ False) ∨ p2)))) → False)) ∨ (False → ((False → p5) ∧ ((p2 ∨ ((p4 → p2) → p4)) → p5)))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- False on the left can always be used.
    apply False.elim h1
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_680397823214912493685679834219 : ((((((p2 ∧ (p2 ∨ ((True ∧ False) → (True ∨ False)))) ∧ (p3 ∨ p3)) ∧ (p5 ∧ ((p3 ∧ p5) ∨ True))) → (False ∨ ((True ∨ p4) → True))) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
      let h10 := h3.left
      let h11 := h3.right
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- Conjunctions on the left can always be decomposed.
        let h13 := h12.left
        let h14 := h12.right
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
      -- Conjunctions on the left can always be decomposed.
      let h19 := h3.left
      let h20 := h3.right
      -- Disjunctions on the left can always be decomposed.
      cases h20
      case inl h21 =>
        -- Conjunctions on the left can always be decomposed.
        let h22 := h21.left
        let h23 := h21.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h24
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h25 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h26
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h27 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h28 =>
      -- Conjunctions on the left can always be decomposed.
      let h29 := h3.left
      let h30 := h3.right
      -- Disjunctions on the left can always be decomposed.
      cases h30
      case inl h31 =>
        -- Conjunctions on the left can always be decomposed.
        let h32 := h31.left
        let h33 := h31.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h34
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h35 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h36
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h37 =>
      -- Conjunctions on the left can always be decomposed.
      let h38 := h3.left
      let h39 := h3.right
      -- Disjunctions on the left can always be decomposed.
      cases h39
      case inl h40 =>
        -- Conjunctions on the left can always be decomposed.
        let h41 := h40.left
        let h42 := h40.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h43
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h44 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h45
        -- True on the right can always be proven directly.
        apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_330247321887775140723204123307 : (True → (False ∨ (((p4 ∨ True) ∧ (((p2 ∧ (p5 → False)) ∧ (p5 ∧ ((p5 ∨ p5) → ((p3 ∨ (p2 → p2)) ∨ p4)))) → p3)) ∨ (False → p2)))) := by
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
theorem thm_5_vars_260466060660515426636848370022 : ((p3 → False) → (((p4 ∧ (p5 ∧ p2)) ∧ ((p2 ∧ (p4 ∨ ((((p3 ∨ True) → p3) ∨ p2) ∨ p5))) ∨ ((p5 → p5) ∧ (False ∨ p2)))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_458696274235481481488116845913 : ((((True → ((p4 → p5) ∧ (((p4 ∨ p1) → (True ∧ ((p2 ∧ (p2 ∧ p5)) ∧ p1))) → False))) ∨ (True ∨ (True ∨ (p2 ∨ (p2 ∧ p2))))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114837390910972252615068927005 : (((((p3 ∨ (p5 ∧ ((p2 ∨ p2) ∧ (p1 ∧ (p4 ∨ p4))))) ∧ True) ∧ False) ∨ ((((p5 ∨ p1) → (p2 → p5)) ∧ p4) ∨ p2)) ∨ (True ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193889436253214726321791710776 : ((False ∨ ((p5 ∨ p5) → ((p5 → (p5 ∧ p2)) ∨ p3))) → ((((True ∧ (((True → p2) → p3) → p3)) → (p5 → p2)) ∨ True) ∨ (p3 ∧ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- False on the left can always be used.
    apply False.elim h2
  case inr h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164529617424070316323807506940 : ((((((p3 ∧ p5) ∨ p2) ∨ ((p3 ∧ (False → p1)) ∧ True)) ∧ (p2 ∨ (p5 → p3))) ∧ p2) ∨ ((p4 ∨ (True ∧ (True ∧ True))) ∨ (p1 ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_774661089786547619817181793150 : (((False ∨ (((True ∨ (p3 → ((p5 ∨ (p3 → p1)) ∨ p4))) ∧ p3) → ((True → p4) ∨ (((p4 ∧ (True → True)) ∨ p3) ∨ (p5 ∨ p3))))) ∨ p1) ∧ True) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137092253437675477711091560592 : ((True ∧ ((False ∨ (((p2 ∨ p5) ∧ ((((p3 ∧ True) ∨ False) ∧ (p1 ∧ (True ∨ True))) → p3)) ∧ (p3 ∧ p4))) ∨ p5)) ∨ (True ∨ (p4 ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_780034693048939219810159838590 : (((p2 ∨ (((False ∨ p5) ∧ ((((p2 ∨ p4) ∧ ((((p4 → p4) → p2) ∨ p5) → (p1 ∨ (p3 ∨ p3)))) ∧ False) → p5)) ∨ (p1 ∨ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313958039437108934240310057116 : (p3 ∨ (((((False ∨ p1) ∧ (((p2 ∨ (((False → p3) → p2) ∧ (p5 ∨ p5))) ∨ (True → True)) → False)) ∧ p1) → (False ∨ p3)) ∨ (False ∧ p2))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h8 : ((p2 ∨ (((False → p3) → p2) ∧ (p5 ∨ p5))) ∨ (True → True)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h9
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h10 := h5 h8
    -- False on the left can always be used.
    apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256428481128857186444587665219 : ((False ∨ p3) → ((False → p5) ∧ (p2 ∨ ((((p2 ∧ ((False ∧ p2) ∨ (((p5 ∧ False) ∧ p4) ∨ p5))) ∧ False) ∧ (p4 ∧ p3)) ∨ (p2 → True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_618846655729297849691508259365 : (((((p1 ∨ (True → p5)) ∧ ((True ∨ p2) → (p5 → ((p1 ∨ (p3 ∨ False)) → (p3 ∧ (((p3 → (p2 ∧ p3)) ∨ True) ∨ p4)))))) ∨ True) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_156817701781652689803288665937 : (((p3 ∨ ((p3 ∨ (p1 ∨ (p3 ∧ (p5 ∧ ((p3 → ((p2 ∧ p2) ∨ p5)) ∨ p5))))) ∨ p3)) ∧ p1) ∨ (((p2 ∧ True) ∧ (p4 → p3)) → p2)) := by
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
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37826734543478617699595487925 : ((((False ∨ (((False ∨ ((False → p5) ∧ p4)) ∧ p2) ∨ (p1 ∧ (((((p5 → p2) ∨ p5) ∧ p4) ∧ (p5 ∧ p1)) → p2)))) → p2) ∧ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323227382844681996391146813993 : (p5 ∨ ((((((True ∨ p2) ∧ True) ∧ False) → (p2 ∧ p5)) → (p2 ∧ (False → (p3 ∨ (p2 ∨ ((p1 ∧ p4) ∨ (p1 → p2))))))) ∨ (p3 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_655384028776567081471426899120 : (((((((((False ∨ ((p3 ∨ p4) → p1)) ∧ (p3 → (p5 ∨ False))) ∧ True) → (False ∧ p1)) ∨ (p5 → p5)) ∨ (p3 ∧ p4)) ∨ (p1 → True)) ∨ False) ∧ True) := by
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
theorem thm_5_vars_316632806258129765358276360573 : (p3 ∨ (p4 ∨ ((True → ((p1 ∧ (((p2 → p2) ∧ False) ∨ p3)) ∨ p2)) ∨ ((True ∨ True) ∨ (((True ∨ False) → (p2 ∨ p1)) ∧ (p1 ∧ p2)))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48102050018306278728236938564 : ((((((p5 ∨ p5) ∧ p2) ∨ p2) ∨ ((True → True) ∧ (p5 ∨ ((p1 → (p2 ∨ ((p1 ∧ p4) → (p3 → p5)))) ∨ p1)))) → (p1 ∨ True)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h3 =>
      -- Conjunctions on the left can always be decomposed.
      let h4 := h3.left
      let h5 := h3.right
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h6 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h7 =>
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
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h13 =>
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h14 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h15 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_657649519861937710213147355531 : (((((p2 ∨ False) → (((((((p3 ∧ (False ∨ p2)) ∧ p5) ∨ (p1 ∧ p1)) ∧ p1) ∨ p2) ∧ p1) ∨ (p1 → (p5 → p2)))) ∨ (p1 → p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_780215536009974886118041685444 : (((p2 ∨ ((p2 ∧ (((((((p2 ∧ False) → (p5 → ((p5 ∧ p3) → p2))) → p4) ∨ False) → p3) ∨ p3) ∧ p4)) ∨ (p4 → (False → p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149116030350493620159939592791 : (((False ∧ True) ∧ (False ∧ (p3 ∨ ((((p5 ∨ p4) ∧ p1) ∧ (p2 ∧ ((p2 ∨ (p2 → p1)) → False))) ∧ p5)))) ∨ (((p1 ∨ False) → False) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159028588250307133250004841496 : ((p4 ∨ ((p1 → p1) → (p5 → (((p5 → True) → (p3 → (p5 ∧ False))) ∨ ((p3 ∨ p1) ∧ p1))))) ∨ (False → (p5 → (False ∧ (p1 ∧ p4))))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49324922937340438459217472003 : (((p4 ∨ (((p1 ∧ (p3 → (p3 ∨ False))) ∨ ((p3 → p4) ∨ (((True → p2) ∨ True) → p3))) → (p5 ∨ p4))) ∨ (p4 → (p4 ∧ True))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51482821491969680048424100780 : ((((p2 → ((False ∨ p5) → (p1 ∨ False))) ∨ (p3 ∨ (((p1 → (p3 → p2)) ∨ True) → p4))) → ((((p3 ∧ True) → p4) ∧ p2) ∧ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_348165208915828023958461401507 : (p3 → ((False ∨ p4) → (((((p4 ∨ (p1 ∨ (p2 ∨ (p3 ∧ (False ∨ (p1 ∧ p3)))))) → (p4 ∧ ((p3 → p5) → p3))) ∨ p4) → False) ∨ True))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350111198134518598626240450477 : (p4 → (((((((p3 ∧ p3) ∧ p1) ∧ p1) ∧ p2) ∨ ((False ∧ False) ∧ ((p5 ∧ True) ∨ (p3 ∨ False)))) ∨ (p1 → ((p2 ∨ True) ∨ p3))) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_588220786647540888358200556194 : ((((((((p4 ∨ p2) → ((p2 → p3) → p2)) → p4) ∨ ((False → p2) ∨ ((((False → (p3 → p4)) → p1) ∨ p5) → p2))) ∨ p4) ∧ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180249624418092249783903906435 : (((False ∨ ((p1 ∧ p5) → (True → ((False → (False ∧ True)) ∨ p2)))) → False) → (p4 ∨ ((((p5 ∨ p1) ∨ ((p4 ∨ p5) → p2)) ∨ True) → p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (False ∨ ((p1 ∧ p5) → (True → ((False → (False ∧ True)) ∨ p2)))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the left can always be decomposed.
    let h5 := h3.left
    let h6 := h3.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h7
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- False on the left can always be used.
    apply False.elim h7
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h8 := h1 h2
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166232229863755425081756631181 : ((p2 ∧ ((p3 ∧ False) ∨ (p4 ∨ ((((p5 → (False → p1)) ∧ p4) ∧ p1) → (False ∨ True))))) ∨ (p1 → ((p2 → ((True ∧ p2) ∨ p3)) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_330263291103915624178443075089 : (True → (False ∨ (((False → (p2 → p5)) → p3) ∨ (p4 ∨ ((p5 ∨ ((p1 ∨ (p5 → (p5 ∧ (False → True)))) ∧ ((p5 ∧ p3) ∧ p5))) → p5))))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- One of the premise coincides with the conclusion.
    exact h3
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
      -- Conjunctions on the left can always be decomposed.
      let h10 := h8.left
      let h11 := h8.right
      -- One of the premise coincides with the conclusion.
      exact h9
    case inr h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h6.left
      let h14 := h6.right
      -- Conjunctions on the left can always be decomposed.
      let h15 := h13.left
      let h16 := h13.right
      -- One of the premise coincides with the conclusion.
      exact h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_32972224108372468513221312370 : ((p3 ∨ (((p1 ∨ p3) → (((((((True → p5) → p3) → p5) → p2) ∨ (p2 ∨ True)) ∨ p4) ∨ p1)) ∨ ((p1 ∧ p5) ∨ (False ∧ p4)))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_956436888538705970112763164328 : (((((p3 ∧ True) → True) → ((p5 → ((p2 ∧ True) → (((p3 ∨ p2) → p1) ∧ (p2 ∨ (p3 ∨ (p2 ∨ ((False ∧ p5) → p4))))))) ∧ p2)) → p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p3 ∧ True) → True) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- One of the premise coincides with the conclusion.
  exact h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217693329137482596739140895597 : ((((p5 → True) → p4) → p2) → (((p2 ∨ False) → p3) ∨ (p3 → ((p1 ∨ ((p2 ∧ p1) → ((p1 → False) → (False ∨ (p1 ∨ False))))) ∨ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114967387841998796522547610896 : (((p2 → (p5 ∧ (((True → True) ∧ p3) ∧ (p1 ∨ ((True ∨ p5) ∨ p1))))) → ((p5 ∨ (p2 → ((True ∧ p3) ∧ True))) ∧ p1)) ∨ (False → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_141177208887070937073599543589 : ((((p1 → (p2 ∧ (p1 ∨ p3))) ∧ p3) ∨ ((((p1 → ((p5 ∨ p1) ∨ False)) ∨ (p2 ∨ False)) ∨ p2) ∨ (p1 → p4))) → (p4 → (p4 ∨ p4))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Disjunctions on the left can always be decomposed.
        cases h8
        case inl h9 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h2
        case inr h10 =>
          -- Disjunctions on the left can always be decomposed.
          cases h10
          case inl h11 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h2
          case inr h12 =>
            -- False on the left can always be used.
            apply False.elim h12
      case inr h13 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h2
    case inr h14 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258276649567512333092214235251 : ((p5 ∨ True) → (((((True → ((False ∨ p1) ∧ p3)) → (p1 ∨ (p4 ∨ p1))) → (True → ((((True ∧ p3) → p3) ∨ p3) ∧ p1))) ∧ p2) ∨ True)) := by
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
theorem thm_5_vars_731212148775262014003210011889 : ((((p3 ∨ (p4 ∧ True)) → (False ∨ ((p1 → (True → ((p1 ∧ p2) → (p4 ∨ (((True ∨ p4) ∨ (p4 ∧ p1)) ∧ p4))))) ∨ (p1 ∧ p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308750507986190545385492014684 : (p2 ∨ ((p5 → ((False ∨ p4) ∨ (p2 ∨ (False ∨ ((True ∧ False) → (((p4 ∧ (p4 ∨ (True → ((p4 ∧ p3) ∨ p1)))) ∨ p1) ∨ True)))))) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64072757090658253296433950540 : ((False ∨ (((p2 → (p3 ∨ ((True → ((p2 → False) ∧ p2)) ∨ p4))) ∨ ((p4 ∨ False) → True)) → ((p4 ∨ (p1 → False)) ∧ (True → True)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54087287191700225345119796051 : ((((True → p2) ∨ ((p1 → p1) → ((p5 ∨ p2) ∨ True))) → ((((True ∨ p4) → p5) ∧ p3) → ((((p1 ∨ p1) → False) → p3) → p5))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h6 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h7 : (True ∨ p4) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h8 := h4 h7
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h10 : (True ∨ p4) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h11 := h4 h10
    -- One of the premise coincides with the conclusion.
    exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115044802688419132431758277454 : ((((p3 ∧ (p1 ∨ ((False ∧ (False ∧ p1)) ∨ (p2 → p4)))) ∨ False) ∨ ((p4 ∧ (p1 ∧ ((p1 → p2) ∨ True))) → (p3 ∨ p4))) ∨ (p4 ∧ p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  cases h5
  case inl h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_733427242526731967868081832502 : ((((p4 ∧ p1) ∧ (((False ∧ False) ∧ (((p4 ∨ (((p2 ∧ p2) ∨ True) ∨ p2)) ∧ ((p5 ∧ (p4 → True)) ∧ p1)) → (False ∧ True))) ∨ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58043140717480007947158394569 : (((False ∧ True) ∧ ((p4 ∨ (True ∧ p1)) → ((False ∧ ((p5 ∧ (((p2 → (p3 ∧ p1)) ∨ p5) ∧ True)) ∨ p2)) ∨ (p2 → (True ∧ p1))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_811554451188814373909244805786 : (((p5 → (True → (((False ∨ p1) → ((p4 → (p3 → ((p2 ∨ p3) ∨ (False ∧ p1)))) ∧ ((p2 ∧ p2) → p3))) → (p5 ∧ (p1 ∨ p2))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_687568555422307653083861604362 : (((((((((p2 ∨ p2) → p1) → p1) → (False ∧ (p1 → (p3 ∨ False)))) → p3) → p3) ∧ (((p1 ∨ p3) → (p1 ∨ False)) ∧ (p2 ∨ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301418246664051362322212994118 : (False ∨ ((((True ∨ p3) ∨ p4) → p3) → ((False ∨ ((p3 ∨ (p4 ∧ (((((False → True) ∧ p5) → (p1 ∧ p1)) ∧ p5) → p4))) ∨ p2)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227325642791489470643888977287 : (((p2 → p4) → p4) ∨ (((p4 → True) ∨ True) → (False ∨ (((p2 ∧ p2) ∧ p3) ∨ (((True ∨ p2) ∧ False) → (p2 → ((p5 ∨ False) ∧ True))))))) := by
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
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the left can always be decomposed.
    let h5 := h3.left
    let h6 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- False on the left can always be used.
      apply False.elim h6
    case inr h8 =>
      -- False on the left can always be used.
      apply False.elim h6
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h10
    -- Implications on the right can always be decomposed.
    intro h11
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the left can always be decomposed.
    let h12 := h10.left
    let h13 := h10.right
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h14 =>
      -- False on the left can always be used.
      apply False.elim h13
    case inr h15 =>
      -- False on the left can always be used.
      apply False.elim h13
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303974633881137633655595957218 : (p1 ∨ ((((p5 ∨ p2) → p1) → (p5 ∨ (((((p5 → p5) ∧ p2) → False) ∧ False) ∨ (p3 ∨ (p2 ∧ (p5 ∨ (False ∨ (p2 ∧ True)))))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190029335444779497519725819853 : ((((p2 → ((True ∨ (True → p3)) → p1)) ∧ p4) ∧ p1) ∨ ((p2 ∧ ((p3 ∧ ((p4 → p5) ∧ p5)) ∧ True)) → (((p4 ∧ p2) ∨ p4) ∨ p3))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h8 := h7.left
  let h9 := h7.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_312454922265051511593171264657 : (p2 ∨ (p4 → (p1 ∨ ((True → (((((p3 ∧ p5) ∧ True) → False) ∨ ((p3 ∧ (((p4 → False) ∨ p3) ∨ False)) → p3)) → (True → p5))) ∨ True)))) := by
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
theorem thm_5_vars_166570022389818042760162635258 : ((True → (((p1 ∧ False) ∧ (((((p1 ∨ p2) ∨ False) ∨ p1) → p3) ∨ (True ∧ p2))) ∧ False)) ∨ (((True ∨ p2) → p5) → ((p3 ∨ p5) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (True ∨ p2) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_753692306015867619280830173538 : (((False ∧ ((((p4 ∧ p2) → False) ∨ (False ∧ ((p3 ∧ p2) ∨ (p3 ∨ (p3 → p5))))) ∨ ((p5 ∨ ((True ∨ p5) ∨ True)) ∨ (p3 ∨ True)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_238320860050239405950636111616 : ((False ∨ True) ∧ (((False ∧ ((p5 ∨ p5) ∨ p1)) → (False → (p1 ∧ (p3 ∨ True)))) → ((False ∧ ((True ∧ True) ∧ ((p3 ∨ p3) ∧ p1))) ∨ True))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65645127260581633904915504323 : ((p4 ∨ (((p2 ∨ (False ∨ p5)) ∨ (((((p4 → p3) ∨ p1) ∧ False) ∨ (p4 ∧ p1)) → (((p3 ∧ p4) ∧ (p3 ∨ False)) ∨ p1))) ∨ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181296166670827195190282648379 : ((p5 ∧ ((p1 → (False → (p2 ∨ False))) ∨ ((p5 → (p1 ∧ p1)) ∧ p2))) → ((p1 → p4) ∨ (False ∨ (p2 → (p4 → (p1 ∨ (p2 → p5))))))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Implications on the right can always be decomposed.
    intro h6
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h11
    -- Implications on the right can always be decomposed.
    intro h12
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h13
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137238581474633092705222795192 : ((p1 ∧ (((((p3 → p1) ∧ ((p4 ∧ (p5 ∨ True)) ∨ p3)) ∨ p1) ∧ (p4 ∧ (p1 → False))) ∨ (False ∨ (True → p5)))) ∨ ((p3 → p3) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166094846163032555055200821726 : (((False → True) → ((False ∨ p5) ∧ (p2 ∨ (p1 ∧ ((p1 ∨ (p1 ∨ (False ∨ p1))) → p4))))) ∨ (p1 → (p1 ∧ ((p1 ∧ (p1 → p1)) ∧ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135981123121275176786686855433 : (((((True → True) ∨ (p1 → (p3 ∨ (p1 ∧ True)))) → p1) ∨ ((p2 ∧ (p2 → (p3 ∨ (p1 ∨ p5)))) ∧ (True → p1))) ∨ (p3 ∨ (True ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_229140730030718623114091870264 : ((True → (p5 ∧ p3)) ∨ ((True ∧ (p5 ∨ (p3 → ((p5 ∨ (((p4 ∧ p4) ∧ (p1 ∨ p1)) → (((p5 ∨ p5) ∧ p4) → False))) ∨ True)))) ∨ p5)) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136278335575526776263397900176 : (((((p1 ∨ p3) → p3) → (p2 ∨ p3)) → ((((p4 → p4) ∨ p2) ∨ (False ∨ ((p4 → p1) ∨ (p5 → p4)))) → False)) ∨ (p3 ∨ (True → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171512145283947428449063711802 : (((((p5 ∨ ((p2 ∧ p4) → (False ∧ True))) → ((p5 ∧ p1) ∨ p4)) ∧ True) ∨ p5) ∨ ((True → True) ∨ (p5 → (((False ∧ p4) → True) → False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_780352002860450854390782393931 : (((p2 ∨ (((p1 ∨ p5) ∧ ((((p3 ∨ p2) ∨ (p4 ∨ (p1 ∧ (p4 → p1)))) ∨ (p5 ∨ p3)) ∧ p4)) → (((p2 → p3) ∨ p1) ∧ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37790601354454973825947117356 : (((((True ∨ False) → ((((p2 ∧ (p5 ∧ p1)) ∨ False) ∧ False) ∨ (((False ∨ (False → (p5 ∨ False))) → False) → (False → p3)))) → p3) ∧ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_142219660175372723710039956541 : ((p1 ∧ ((False → False) → (((((p3 → False) → ((p2 ∨ (p2 ∧ ((p4 ∨ p4) ∧ True))) ∨ p2)) → p2) ∧ p1) ∧ False))) → ((p4 ∨ False) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : (False → False) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- False on the left can always be used.
    apply False.elim h5
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h4
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_741755753723438371892770311075 : ((((True → p2) ∨ (False ∧ ((p4 → (False ∨ p3)) ∧ ((((p1 → (p4 ∨ p1)) ∨ (p2 ∨ ((False → (True ∧ False)) ∧ False))) ∧ p5) ∨ p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53319858847658357194967590325 : (((p2 → (p3 → ((False ∧ (p3 ∨ False)) ∧ ((p4 ∨ p1) ∧ True)))) ∨ ((p4 ∨ p3) ∨ ((p3 → ((p5 → False) ∨ (p4 → p5))) → p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_943081312036690419288430756252 : (((((True → p4) ∨ (p4 ∨ p3)) ∧ (p4 ∧ (((p4 → (((p2 → (p2 ∧ p3)) ∧ (p5 ∨ False)) ∧ p5)) ∨ (p2 → (p1 ∧ p3))) → p3))) → p4) ∧ True) := by
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
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h3.left
      let h10 := h3.right
      -- One of the premise coincides with the conclusion.
      exact h9
    case inr h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h3.left
      let h13 := h3.right
      -- One of the premise coincides with the conclusion.
      exact h12
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340703808485144801738128503297 : (p2 → ((((True → ((((((p1 ∨ p3) ∨ p2) ∧ p1) ∧ p1) ∨ True) ∧ (p5 ∧ (p3 ∧ (p5 → p5))))) ∨ (p1 ∧ (p2 → p1))) ∧ p3) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206497787846769328374100468841 : ((p5 ∨ ((p5 ∧ p4) ∨ (p4 ∨ p5))) ∨ (p5 → (True ∨ (p5 ∨ (((p5 ∧ False) → p5) ∧ (False ∨ ((True → (False ∧ p4)) ∨ (p2 ∧ False)))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324175338807356417163850575563 : (p5 ∨ (((p5 ∧ p5) ∨ (p3 ∨ ((p3 ∨ (p1 ∧ p2)) ∨ p4))) ∨ ((p5 → ((True ∧ p5) ∧ True)) ∨ (((p4 ∨ (p5 ∨ p3)) ∧ p1) → p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_598542018312865786102820113524 : ((((((False → True) → p4) → ((p4 ∧ p1) ∨ (((p3 → ((p4 ∧ (False → p3)) ∧ p1)) ∨ (p1 ∧ p5)) ∧ (p4 → (p1 ∧ p2))))) ∧ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67672449810578280664867023587 : ((p1 → (True → (p4 ∨ (((True ∧ p4) ∨ (False → p5)) ∧ ((((p2 ∨ (True ∧ p4)) ∧ p3) ∨ p3) ∨ (((p2 ∧ p4) ∧ p2) ∨ p4)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



