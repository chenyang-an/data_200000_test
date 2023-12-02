variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317092450499686917086742472733 : (p3 ∨ (p5 → ((p4 ∨ ((((p5 ∧ False) ∧ (True ∧ ((p1 → False) → p3))) ∨ True) ∨ (p5 ∨ ((p5 → ((p4 ∨ True) → True)) → p3)))) ∧ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_90966133145711165809364359731 : (((False → p1) ∧ (((((p3 → p5) ∨ p4) → (p1 → p1)) → p2) ∨ ((p2 ∧ (p3 → (p3 → ((p2 ∨ p4) ∨ p4)))) ∨ (p2 ∧ p1)))) → p2) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h5 : (((p3 → p5) ∨ p4) → (p1 → p1)) := by
      -- Implications on the right can always be decomposed.
      intro h6
      -- Implications on the right can always be decomposed.
      intro h7
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h8 =>
        -- One of the premise coincides with the conclusion.
        exact h7
      case inr h9 =>
        -- One of the premise coincides with the conclusion.
        exact h7
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h10 := h4 h5
    -- One of the premise coincides with the conclusion.
    exact h10
  case inr h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h12.left
      let h14 := h12.right
      -- One of the premise coincides with the conclusion.
      exact h13
    case inr h15 =>
      -- Conjunctions on the left can always be decomposed.
      let h16 := h15.left
      let h17 := h15.right
      -- One of the premise coincides with the conclusion.
      exact h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38929968621063995423542169037 : (((((True ∨ p4) ∨ True) → (p5 → ((p4 → (p1 ∨ (p3 ∧ (p3 ∧ p1)))) → (((((p5 → p4) ∧ p2) ∨ p1) → p5) ∧ p2)))) ∧ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_625840127775017117625972533770 : ((((p1 → (p5 → ((((True ∨ False) ∨ ((True ∨ p2) ∧ ((p2 ∧ ((p4 → ((p2 ∨ p3) ∧ p3)) ∧ p3)) ∨ p5))) → p3) ∨ p4))) ∨ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_659183106758872131970178242185 : ((((p3 → (p2 ∨ ((True ∨ p3) ∧ (p3 ∧ (False ∧ (((True ∧ (p2 → p5)) ∧ p4) ∧ ((p3 ∨ p4) ∧ (p1 ∨ p3)))))))) ∨ (True ∨ p5)) ∨ p3) ∧ True) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55272234331896402653859496664 : ((((False → p4) → (p2 → (False ∧ True))) ∨ ((((p1 ∧ p4) ∨ (p1 ∧ p1)) ∧ (True ∨ True)) ∨ (False → ((p5 ∧ (p5 ∧ p4)) ∨ p5)))) ∨ p4) := by
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
theorem thm_5_vars_619632533078479912417028478092 : (((((p2 ∧ p3) ∧ ((((p1 ∨ ((((False → True) → p5) ∨ True) ∨ False)) ∧ (p5 ∧ p1)) ∨ p4) ∧ ((False ∧ True) → (True → p4)))) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_352882331565717326955544893257 : (p4 → (True ∧ (((p5 → (((((p1 ∧ p4) ∧ (p5 → p5)) ∧ p4) → ((p3 ∨ p5) → True)) ∨ p2)) → p1) ∨ (p3 → (p2 ∨ (p4 ∧ p4)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_153124986261178652092441563432 : ((p4 ∧ (((p3 → p3) ∨ p4) ∨ (p3 → (p2 ∧ ((p2 ∧ p1) → ((p2 ∧ (p3 → p2)) → (p4 → p2))))))) → (((p3 ∧ False) ∨ p4) ∨ False)) := by
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h6 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h6
  case inr h7 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305167337792874327522068410095 : (p1 ∨ ((((p5 → ((((p1 ∨ False) → False) ∧ (p3 ∨ ((p3 ∧ False) ∧ True))) ∧ p4)) ∨ p4) ∧ (True ∧ p2)) ∨ ((False ∨ True) ∨ (p3 → p1)))) := by
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
theorem thm_5_vars_48838962816757602234748572871 : (((False ∨ ((p1 → p2) ∧ ((p5 → p3) ∨ ((p2 ∧ ((p4 ∧ (p2 ∨ (False ∨ True))) ∨ (p3 → p2))) ∨ False)))) ∧ ((p3 → p4) ∨ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41308500594491113642600398849 : (((((False ∨ (p5 ∧ (p1 ∨ ((p5 → ((True ∧ (p3 ∧ True)) ∨ p1)) → True)))) ∨ False) ∧ ((False ∨ p2) ∧ ((False ∧ p3) ∧ p3))) ∨ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_629690237436057167315321734827 : ((((((True ∧ (False ∨ ((True ∧ p4) ∨ (((((p4 ∨ p1) ∨ p1) ∨ p1) ∨ p3) ∨ True)))) ∨ (True ∧ (p2 ∨ (p1 ∧ p1)))) ∨ True) → False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48364156078600265635602699955 : (((p4 ∨ (p1 → (((p3 ∧ p3) → p3) ∧ (True → ((((True → p5) → p4) → False) ∧ ((p1 ∨ (p4 ∨ True)) ∧ p4)))))) → (True ∧ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168652977673786403981021180048 : ((p4 ∧ ((True ∨ p2) → (False ∧ ((False → (True ∨ p2)) ∧ (False ∨ (True ∨ (p3 ∧ True))))))) → (p3 ∧ ((p2 ∨ ((p2 ∧ p1) ∨ p1)) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : (True ∨ p2) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- False on the left can always be used.
  apply False.elim h6
  -- Conjunctions on the left can always be decomposed.
  let h7 := h1.left
  let h8 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_352816588665251281916307956782 : (p4 → ((p5 ∨ p4) → (((((p2 → p4) → p1) → (p4 ∧ True)) → ((p1 ∨ (((p5 ∨ p1) ∨ p2) → p4)) → p1)) ∨ ((p2 ∨ p5) ∨ p4)))) := by
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
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_124505307190710523320928647029 : ((((p1 ∧ (p1 ∨ True)) ∧ (p5 → False)) ∧ (((((False ∧ ((False ∨ ((True ∧ p2) → p3)) → False)) ∨ p4) ∧ p4) ∨ p2) → p3)) → (p3 → p3)) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h9 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h10 =>
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164811215602634253131421783722 : ((((p1 ∨ p4) ∧ (((p5 ∨ p3) → ((p5 ∧ p2) → (p1 ∧ p5))) ∨ (p3 ∨ p2))) ∨ False) ∨ (((True → ((p1 → p4) ∧ False)) ∨ p5) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_629677552400118689794696394753 : (((((((((p1 ∨ p2) → (((p1 ∧ ((p2 → p1) → True)) → True) → True)) ∨ p2) ∨ False) ∨ ((p2 → (p3 ∨ p3)) → False)) ∨ p2) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157493964888292417308984383375 : (((((False → (p5 → p1)) ∨ False) → (((False ∧ p3) ∨ (p5 → False)) ∨ (p2 → False))) ∨ (p4 → True)) ∨ ((p1 ∧ ((p3 → p4) ∧ p4)) ∨ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_672216034773082765518536943568 : (((((p3 → (p2 ∧ ((True → (p2 → (((p3 ∧ ((p3 → p1) ∧ p5)) ∧ (p1 ∧ False)) ∨ p3))) ∧ False))) ∨ p2) → ((p2 → False) ∧ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_680782925233245162800430234339 : ((((((True ∨ p3) → p3) ∧ ((p4 ∨ (True → True)) ∧ (p2 ∨ (True ∧ (((p1 → p3) ∧ False) ∨ p1))))) → (((p5 ∧ p1) ∨ p4) → p3)) ∨ p5) ∧ True) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h6 := h1.left
    let h7 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h11 =>
        -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
        have h12 : (True ∨ p3) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h6, we can now drive its conclusion.
        let h13 := h6 h12
        -- One of the premise coincides with the conclusion.
        exact h13
      case inr h14 =>
        -- Conjunctions on the left can always be decomposed.
        let h15 := h14.left
        let h16 := h14.right
        -- Disjunctions on the left can always be decomposed.
        cases h16
        case inl h17 =>
          -- Conjunctions on the left can always be decomposed.
          let h18 := h17.left
          let h19 := h17.right
          -- False on the left can always be used.
          apply False.elim h19
        case inr h20 =>
          -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
          have h21 : (True ∨ p3) := by
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h6, we can now drive its conclusion.
          let h22 := h6 h21
          -- One of the premise coincides with the conclusion.
          exact h22
    case inr h23 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h24 =>
        -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
        have h25 : (True ∨ p3) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h6, we can now drive its conclusion.
        let h26 := h6 h25
        -- One of the premise coincides with the conclusion.
        exact h26
      case inr h27 =>
        -- Conjunctions on the left can always be decomposed.
        let h28 := h27.left
        let h29 := h27.right
        -- Disjunctions on the left can always be decomposed.
        cases h29
        case inl h30 =>
          -- Conjunctions on the left can always be decomposed.
          let h31 := h30.left
          let h32 := h30.right
          -- False on the left can always be used.
          apply False.elim h32
        case inr h33 =>
          -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
          have h34 : (True ∨ p3) := by
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h6, we can now drive its conclusion.
          let h35 := h6 h34
          -- One of the premise coincides with the conclusion.
          exact h35
  case inr h36 =>
    -- Conjunctions on the left can always be decomposed.
    let h37 := h1.left
    let h38 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h39 := h38.left
    let h40 := h38.right
    -- Disjunctions on the left can always be decomposed.
    cases h39
    case inl h41 =>
      -- Disjunctions on the left can always be decomposed.
      cases h40
      case inl h42 =>
        -- We want to use the implication h37 based on <expert-advice>. So we show its premise.
        have h43 : (True ∨ p3) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h37, we can now drive its conclusion.
        let h44 := h37 h43
        -- One of the premise coincides with the conclusion.
        exact h44
      case inr h45 =>
        -- Conjunctions on the left can always be decomposed.
        let h46 := h45.left
        let h47 := h45.right
        -- Disjunctions on the left can always be decomposed.
        cases h47
        case inl h48 =>
          -- Conjunctions on the left can always be decomposed.
          let h49 := h48.left
          let h50 := h48.right
          -- False on the left can always be used.
          apply False.elim h50
        case inr h51 =>
          -- We want to use the implication h37 based on <expert-advice>. So we show its premise.
          have h52 : (True ∨ p3) := by
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h37, we can now drive its conclusion.
          let h53 := h37 h52
          -- One of the premise coincides with the conclusion.
          exact h53
    case inr h54 =>
      -- Disjunctions on the left can always be decomposed.
      cases h40
      case inl h55 =>
        -- We want to use the implication h37 based on <expert-advice>. So we show its premise.
        have h56 : (True ∨ p3) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h37, we can now drive its conclusion.
        let h57 := h37 h56
        -- One of the premise coincides with the conclusion.
        exact h57
      case inr h58 =>
        -- Conjunctions on the left can always be decomposed.
        let h59 := h58.left
        let h60 := h58.right
        -- Disjunctions on the left can always be decomposed.
        cases h60
        case inl h61 =>
          -- Conjunctions on the left can always be decomposed.
          let h62 := h61.left
          let h63 := h61.right
          -- False on the left can always be used.
          apply False.elim h63
        case inr h64 =>
          -- We want to use the implication h37 based on <expert-advice>. So we show its premise.
          have h65 : (True ∨ p3) := by
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h37, we can now drive its conclusion.
          let h66 := h37 h65
          -- One of the premise coincides with the conclusion.
          exact h66
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_85393384744691253145665418597 : ((((p4 → (p5 ∧ p3)) ∧ ((True → (False ∨ (False ∧ False))) ∧ p2)) ∧ ((((False ∧ p2) → (p5 ∧ p5)) ∧ (p5 ∧ p3)) ∨ (p1 ∨ p3))) → p4) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h13 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h14 := h6 h13
    -- Disjunctions on the left can always be decomposed.
    cases h14
    case inl h15 =>
      -- False on the left can always be used.
      apply False.elim h15
    case inr h16 =>
      -- Conjunctions on the left can always be decomposed.
      let h17 := h16.left
      let h18 := h16.right
      -- False on the left can always be used.
      apply False.elim h17
  case inr h19 =>
    -- Disjunctions on the left can always be decomposed.
    cases h19
    case inl h20 =>
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h21 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h22 := h6 h21
      -- Disjunctions on the left can always be decomposed.
      cases h22
      case inl h23 =>
        -- False on the left can always be used.
        apply False.elim h23
      case inr h24 =>
        -- Conjunctions on the left can always be decomposed.
        let h25 := h24.left
        let h26 := h24.right
        -- False on the left can always be used.
        apply False.elim h25
    case inr h27 =>
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h28 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h29 := h6 h28
      -- Disjunctions on the left can always be decomposed.
      cases h29
      case inl h30 =>
        -- False on the left can always be used.
        apply False.elim h30
      case inr h31 =>
        -- Conjunctions on the left can always be decomposed.
        let h32 := h31.left
        let h33 := h31.right
        -- False on the left can always be used.
        apply False.elim h32



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57897873405885450869700312425 : (((p3 ∨ (False → True)) → ((p2 → (((p3 → p3) ∨ ((p3 ∨ (p3 ∧ True)) → (p3 → (p1 ∨ p3)))) ∨ ((p5 ∨ False) → p4))) → p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49180918720102325809186092301 : (((((p5 ∧ p4) ∨ (p5 ∧ p5)) ∨ (p1 ∨ (((p4 ∨ (p1 ∧ False)) ∧ (p1 ∨ ((True → True) → p1))) ∨ True))) ∨ ((p1 ∧ p4) ∨ p3)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_218576871323533766937869538069 : (((p1 → p5) → (p1 ∧ True)) → ((((p3 ∧ p3) ∧ (((p4 ∧ (False ∨ p4)) ∨ p5) ∧ (p4 ∧ p4))) ∨ (((p2 ∨ p5) ∨ True) ∨ p3)) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
theorem thm_5_vars_811082495851636310142596841540 : (((p5 → (p1 ∧ (((False ∨ (((p1 ∧ (p3 → False)) ∧ False) → p5)) → (p3 ∨ ((p1 ∧ True) ∨ False))) ∧ (p2 ∧ (p1 ∧ (p3 ∨ p2)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_326311942584813509986632658229 : (p5 ∨ (p4 → ((p4 → (p2 → False)) → (((p3 → (p4 ∧ p5)) → (p2 ∨ p5)) ∨ (False → (p3 ∧ (((True ∨ p5) → p3) → (True ∨ p2)))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_615097687376518374553096367138 : ((((((((((p1 → (p1 ∧ p1)) ∨ (p5 ∧ p1)) ∨ p4) ∨ True) → (p5 ∨ p1)) ∧ p1) ∧ (p5 → (((p1 → p5) ∨ p1) ∨ True))) ∨ True) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_186784518109602561798091569250 : ((((p1 → (False ∧ p2)) ∧ p3) ∧ (True → ((True ∧ p3) ∨ p2))) → (((((False → p3) ∨ p3) ∨ (p3 → p5)) ∨ True) → ((p5 ∨ False) ∨ p3))) := by
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
        let h6 := h1.left
        let h7 := h1.right
        -- Conjunctions on the left can always be decomposed.
        let h8 := h6.left
        let h9 := h6.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h9
      case inr h10 =>
        -- Conjunctions on the left can always be decomposed.
        let h11 := h1.left
        let h12 := h1.right
        -- Conjunctions on the left can always be decomposed.
        let h13 := h11.left
        let h14 := h11.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h14
    case inr h15 =>
      -- Conjunctions on the left can always be decomposed.
      let h16 := h1.left
      let h17 := h1.right
      -- Conjunctions on the left can always be decomposed.
      let h18 := h16.left
      let h19 := h16.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h19
  case inr h20 =>
    -- Conjunctions on the left can always be decomposed.
    let h21 := h1.left
    let h22 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h23 := h21.left
    let h24 := h21.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h24



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54135273334512609658097830372 : (((p4 ∨ (((p4 → ((False ∧ p1) ∨ p3)) ∨ p1) ∧ p5)) → (((p4 → (((p2 ∧ True) → False) ∧ p2)) ∧ (False → True)) ∨ (True ∨ False))) ∨ p3) := by
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160565359639320731390362504844 : ((((True ∨ (((False → p2) ∨ p4) ∨ p2)) ∧ ((p4 ∨ p3) ∧ p1)) → ((p4 ∧ p2) ∨ (p1 → p2))) → ((p2 ∨ True) ∨ (True → (False → False)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192338875916889107259963494476 : (((p2 ∨ (p2 → (p4 ∨ ((p2 → p3) → False)))) ∧ p3) → ((((p4 → ((p1 ∨ (p4 → p2)) ∧ (p5 ∧ p3))) → True) ∧ (True ∧ p5)) ∨ True)) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53401210396137215797526046958 : (((((((p2 → p1) → True) ∨ p4) ∨ (p2 ∧ False)) ∨ (p2 ∨ p2)) → ((p3 ∧ (p3 → p1)) → (p4 ∨ ((p2 → False) ∧ (p3 ∧ p1))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179027583242449618553974755138 : (((p2 ∨ p4) → (p5 → ((p1 ∨ ((p4 ∧ p5) ∨ p3)) → (p2 ∨ False)))) ∨ (((True ∧ p2) ∧ False) → (p2 ∨ (False → ((p5 → False) → p4))))) := by
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
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219948387565304101088516367432 : ((p5 → ((p5 ∧ p3) ∧ True)) → ((((p1 ∧ True) ∧ (((p2 → p2) → True) ∧ (False → p5))) → ((p4 → (False ∧ p4)) → (p5 ∧ p1))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_139688237884030583254012985997 : ((((p2 ∨ (p1 ∨ p4)) → (p4 → (p1 ∨ ((True ∧ ((p4 → False) → (p4 → p5))) → (p3 → (p4 → p4)))))) → p1) → (False ∨ (p1 ∧ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p2 ∨ (p1 ∨ p4)) → (p4 → (p1 ∨ ((True ∧ ((p4 → False) → (p4 → p5))) → (p3 → (p4 → p4)))))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- Implications on the right can always be decomposed.
      intro h7
      -- Implications on the right can always be decomposed.
      intro h8
      -- Conjunctions on the left can always be decomposed.
      let h9 := h6.left
      let h10 := h6.right
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h12
      case inr h13 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h14
        -- Implications on the right can always be decomposed.
        intro h15
        -- Implications on the right can always be decomposed.
        intro h16
        -- Conjunctions on the left can always be decomposed.
        let h17 := h14.left
        let h18 := h14.right
        -- One of the premise coincides with the conclusion.
        exact h16
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h19 := h1 h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h19
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_861234034207847363278129821102 : (((((((p2 ∨ p1) ∧ ((p5 ∧ (((p2 ∧ (False → (p3 ∧ p5))) → p4) ∧ (p1 → p1))) ∧ True)) ∨ True) ∨ ((p3 ∨ True) ∨ p1)) → False) → p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((((p2 ∨ p1) ∧ ((p5 ∧ (((p2 ∧ (False → (p3 ∧ p5))) → p4) ∧ (p1 → p1))) ∧ True)) ∨ True) ∨ ((p3 ∨ True) ∨ p1)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
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
theorem thm_5_vars_218941755509512257865334470996 : ((p3 ∧ (p5 ∨ (p2 → p4))) → (((p1 ∨ ((p1 ∨ ((p3 ∨ p5) ∨ False)) ∧ (p3 → p1))) ∧ ((p5 ∨ p2) → p1)) ∨ (False → (p5 ∧ True)))) := by
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
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- False on the left can always be used.
    apply False.elim h5
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- False on the left can always be used.
    apply False.elim h7
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_674966923497437971566431554870 : (((((((p5 ∧ ((p3 ∨ p5) ∧ False)) ∧ p4) ∨ (((p1 → p2) ∨ p4) ∨ (False ∨ (True → p1)))) ∧ p2) ∧ (p4 → ((p3 ∨ p5) ∨ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190999913380287093537243452205 : ((((True → p1) → (p4 ∨ False)) ∨ (False ∧ (p3 → p4))) ∨ ((((p3 → False) ∧ p5) ∧ p3) → (((p3 → ((False → True) ∧ p4)) ∨ p2) ∧ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h6 : p3 := by
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h7 := h4 h6
  -- False on the left can always be used.
  apply False.elim h7
  -- Conjunctions on the left can always be decomposed.
  let h8 := h1.left
  let h9 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h10 := h8.left
  let h11 := h8.right
  -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
  have h12 : p3 := by
    -- One of the premise coincides with the conclusion.
    exact h9
  -- We have shown the premise of h10, we can now drive its conclusion.
  let h13 := h10 h12
  -- False on the left can always be used.
  apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_318749093564407246365175294459 : (p4 ∨ ((p1 ∧ (p3 ∧ (p4 ∨ (p3 ∨ (p3 ∨ (((True → p1) ∨ ((p2 → p4) ∨ (True ∧ (True ∨ p5)))) ∨ (True ∨ p3))))))) → (p2 ∨ p1))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h2
      case inr h11 =>
        -- Disjunctions on the left can always be decomposed.
        cases h11
        case inl h12 =>
          -- Disjunctions on the left can always be decomposed.
          cases h12
          case inl h13 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h2
          case inr h14 =>
            -- Disjunctions on the left can always be decomposed.
            cases h14
            case inl h15 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- One of the premise coincides with the conclusion.
              exact h2
            case inr h16 =>
              -- Conjunctions on the left can always be decomposed.
              let h17 := h16.left
              let h18 := h16.right
              -- Disjunctions on the left can always be decomposed.
              cases h18
              case inl h19 =>
                -- Show the right disjunct based on <expert-advice>.
                apply Or.inr
                -- One of the premise coincides with the conclusion.
                exact h2
              case inr h20 =>
                -- Show the right disjunct based on <expert-advice>.
                apply Or.inr
                -- One of the premise coincides with the conclusion.
                exact h2
        case inr h21 =>
          -- Disjunctions on the left can always be decomposed.
          cases h21
          case inl h22 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h2
          case inr h23 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37851501329151768670227136727 : ((((False → ((p2 → (True → (p4 → (p1 → (((p5 ∧ p4) ∧ p5) ∨ ((p3 ∧ (p3 ∧ p1)) ∧ (True → p1))))))) → p2)) → False) ∧ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173709072868501666122889298533 : (((((((p5 ∧ (p2 ∨ False)) ∨ (p1 ∨ p2)) ∨ p2) → p3) ∧ (p5 → p4)) ∨ p4) → (p3 ∨ (p5 → (p1 ∨ ((p4 ∨ (p5 ∨ p4)) ∧ True))))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h5
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h7
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207744428595889625323774339852 : (((True ∨ ((True → p3) ∨ p2)) → p2) → ((((p4 ∧ p5) → (False ∨ (False ∨ p4))) ∧ (p2 ∨ ((p5 → (p4 ∨ p3)) ∨ p5))) ∨ (p4 ∧ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (True ∨ ((True → p3) ∨ p2)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h5
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46378400639452760909324597135 : (((((((True → (False ∧ p3)) → False) ∧ (True → p1)) → p3) ∧ ((p4 ∨ p1) ∧ (p2 → (p3 ∧ (p4 ∨ (False ∨ p2)))))) ∧ (True → p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338061702720936327328026298754 : (p1 → (((p3 ∨ (p2 → (((p5 → False) ∨ True) ∧ False))) ∨ p4) → (((False → True) → (p1 ∧ False)) → (p5 → (p4 ∧ (p4 ∨ (p4 → True))))))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h7 : (False → True) := by
        -- Implications on the right can always be decomposed.
        intro h8
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h9 := h3 h7
      -- We need to get the right conjuct of h9 based on <expert-advice>.
      let h10 := h9.right
      -- False on the left can always be used.
      apply False.elim h10
    case inr h11 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h12 : (False → True) := by
        -- Implications on the right can always be decomposed.
        intro h13
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h14 := h3 h12
      -- We need to get the right conjuct of h14 based on <expert-advice>.
      let h15 := h14.right
      -- False on the left can always be used.
      apply False.elim h15
  case inr h16 =>
    -- One of the premise coincides with the conclusion.
    exact h16
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h17 =>
    -- Disjunctions on the left can always be decomposed.
    cases h17
    case inl h18 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h19
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h20 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h21
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h22 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h22



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193011255472563071503660671278 : ((((False → (p5 → p5)) ∧ (p4 ∧ p5)) → (p2 ∧ True)) → ((p3 → ((((((p3 → (p5 ∨ p4)) ∧ p3) → p3) ∨ p1) → p5) ∨ True)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171897472197926566312846175576 : (((p4 ∨ (True ∧ (p1 ∧ ((((p4 ∧ p4) ∧ (p4 → p4)) ∧ p2) → True)))) → p5) ∨ ((p3 → (((False ∨ p4) ∧ False) ∨ (True ∨ p1))) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_111425952340806328343860682937 : (((p4 ∨ ((((p2 ∧ False) ∧ p2) ∨ (((p4 ∧ p1) ∨ (True ∨ ((p4 ∨ (p4 ∨ True)) → p3))) ∨ (p4 ∨ p2))) → False)) ∧ p4) ∨ (p2 → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_780173610973742297757546993717 : (((p2 ∨ ((p4 ∧ (p1 ∨ (p2 ∧ (((p5 → (p3 ∨ p3)) ∨ ((((p3 ∨ True) ∧ p1) ∨ p1) ∧ True)) ∨ True)))) ∧ ((True ∨ p4) ∧ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200071838245637584854212402364 : ((((p3 ∨ p4) ∧ True) ∧ ((True ∧ p4) → p3)) → (((p4 ∧ ((((p3 ∨ p1) ∨ ((p3 ∨ False) → (p5 ∨ p3))) ∨ p1) ∧ p4)) → p3) ∨ False)) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h7
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
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
        cases h13
        case inl h14 =>
          -- One of the premise coincides with the conclusion.
          exact h14
        case inr h15 =>
          -- One of the premise coincides with the conclusion.
          exact h6
      case inr h16 =>
        -- One of the premise coincides with the conclusion.
        exact h6
    case inr h17 =>
      -- One of the premise coincides with the conclusion.
      exact h6
  case inr h18 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h19 : (True ∧ p4) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- One of the premise coincides with the conclusion.
      exact h18
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h20 := h3 h19
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h21
    -- Conjunctions on the left can always be decomposed.
    let h22 := h21.left
    let h23 := h21.right
    -- Conjunctions on the left can always be decomposed.
    let h24 := h23.left
    let h25 := h23.right
    -- Disjunctions on the left can always be decomposed.
    cases h24
    case inl h26 =>
      -- Disjunctions on the left can always be decomposed.
      cases h26
      case inl h27 =>
        -- Disjunctions on the left can always be decomposed.
        cases h27
        case inl h28 =>
          -- One of the premise coincides with the conclusion.
          exact h28
        case inr h29 =>
          -- One of the premise coincides with the conclusion.
          exact h20
      case inr h30 =>
        -- One of the premise coincides with the conclusion.
        exact h20
    case inr h31 =>
      -- One of the premise coincides with the conclusion.
      exact h20



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_662781103872656952119846423234 : (((((p1 ∨ (True ∨ (p1 ∨ False))) → (False ∨ (True → (p3 ∨ (((p4 → p4) ∨ (p5 → (p2 → (p5 → p1)))) ∧ p2))))) → (p3 ∨ p2)) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p1 ∨ (True ∨ (p1 ∨ False))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
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
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h6 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h7 := h5 h6
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h11
      case inr h13 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h11
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39432465244887152151817752544 : (((p5 ∧ (((p5 ∧ ((p2 ∧ True) ∨ (p4 ∨ (p5 ∧ (p5 ∧ ((((p3 ∧ p2) ∧ p3) ∨ True) ∨ p4)))))) ∨ (True ∧ p2)) ∧ p5)) ∧ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_124668936579693870667412957393 : ((((p4 → p2) ∧ ((p3 → p5) → p1)) → ((((((False → p1) ∨ p2) ∧ ((p5 ∧ p5) → p3)) → p4) → (p4 ∧ p2)) ∧ p2)) → (p5 ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63249299306155129354687576468 : ((p5 ∧ (((((p4 ∨ (p4 → p4)) ∨ p1) ∧ (True → p3)) ∧ p3) → ((((p3 ∨ False) → p3) ∧ ((True ∨ (p1 ∧ False)) ∨ p5)) → p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310860648407339401358325384187 : (p2 ∨ (((p2 → p2) → False) → ((p2 ∨ p3) → (p1 ∧ (p4 → ((False ∧ p2) ∧ ((p3 → (p4 ∧ (p4 → (False ∧ (True ∨ p3))))) ∨ False))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h4 : (p2 → p2) := by
      -- Implications on the right can always be decomposed.
      intro h5
      -- One of the premise coincides with the conclusion.
      exact h5
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h6 := h1 h4
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h8 : (p2 → p2) := by
      -- Implications on the right can always be decomposed.
      intro h9
      -- One of the premise coincides with the conclusion.
      exact h9
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h10 := h1 h8
    -- False on the left can always be used.
    apply False.elim h10
  -- Implications on the right can always be decomposed.
  intro h11
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h12 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h13 : (p2 → p2) := by
      -- Implications on the right can always be decomposed.
      intro h14
      -- One of the premise coincides with the conclusion.
      exact h14
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h15 := h1 h13
    -- False on the left can always be used.
    apply False.elim h15
  case inr h16 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h17 : (p2 → p2) := by
      -- Implications on the right can always be decomposed.
      intro h18
      -- One of the premise coincides with the conclusion.
      exact h18
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h19 := h1 h17
    -- False on the left can always be used.
    apply False.elim h19
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h20 =>
    -- One of the premise coincides with the conclusion.
    exact h20
  case inr h21 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h22 : (p2 → p2) := by
      -- Implications on the right can always be decomposed.
      intro h23
      -- One of the premise coincides with the conclusion.
      exact h23
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h24 := h1 h22
    -- False on the left can always be used.
    apply False.elim h24
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h25 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h26 : (p2 → p2) := by
      -- Implications on the right can always be decomposed.
      intro h27
      -- One of the premise coincides with the conclusion.
      exact h27
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h28 := h1 h26
    -- False on the left can always be used.
    apply False.elim h28
  case inr h29 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h30 : (p2 → p2) := by
      -- Implications on the right can always be decomposed.
      intro h31
      -- One of the premise coincides with the conclusion.
      exact h31
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h32 := h1 h30
    -- False on the left can always be used.
    apply False.elim h32



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135098597720730870447052731295 : ((((((p3 ∨ (p1 ∧ p5)) → p5) → p4) ∨ (True → (((((p1 ∧ p3) ∧ True) ∨ p2) ∧ p5) ∨ True))) ∨ (p3 ∧ p1)) ∨ ((False ∨ True) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345541378624978878196731032002 : (p3 → ((((True ∧ p2) ∨ (p5 → (p4 ∨ (False ∨ p5)))) → (False ∨ ((p4 ∧ (p4 → p5)) ∧ ((((p1 ∨ False) ∨ p2) → False) → False)))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_613628426644701756936618765557 : (((((((((p2 → (p1 ∨ False)) ∧ p3) ∨ ((p1 ∨ p4) → (p1 ∧ False))) ∨ (False → False)) → (p2 ∧ True)) ∧ (p4 → (p5 → p4))) ∨ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_626602352063802499231433207908 : ((((p4 → (p1 ∧ (((p1 ∧ p5) → p1) ∧ (((((p2 ∨ p1) ∧ (p4 → ((p3 → p1) ∨ False))) → (p3 → p2)) ∧ p4) → p3)))) ∨ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_353898868120337105744002152415 : (p4 → (p2 → (((True → (True ∨ p1)) → ((((p2 → (True ∧ p5)) → False) ∧ ((True ∨ ((p1 ∧ (p4 ∧ False)) ∧ p4)) ∧ p3)) ∨ p2)) ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350321401397938475756517042236 : (p4 → ((True → ((p2 → (((((((p2 ∨ p2) ∧ p3) ∧ p3) ∧ (p3 → ((True ∨ (p1 ∧ True)) → p5))) ∨ p3) ∧ False) ∧ False)) ∨ p5)) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_686225522645650436592514147483 : ((((((p3 ∨ (p5 ∨ (True → p5))) → ((True ∧ True) → True)) → ((p2 ∨ (p3 → p5)) ∧ p2)) → (((p1 ∨ (p5 ∨ p2)) ∨ False) ∨ False)) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p3 ∨ (p5 ∨ (True → p5))) → ((True ∧ True) → True)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h2
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60375989595119685127314174375 : (((p3 → p1) → ((((p4 ∧ (p3 → (True ∧ p1))) ∨ (p4 ∨ p3)) ∨ False) → ((True ∧ True) ∧ (((p1 ∨ (p1 → True)) → False) ∨ p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161149017248520182334077893741 : (((p5 → p5) ∧ (((p2 ∧ p1) ∧ ((p1 → p2) ∧ ((p2 ∧ ((False ∧ p1) ∧ False)) → p3))) ∨ p3)) → ((p3 ∧ (True ∧ (p3 ∨ p5))) → p3)) := by
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
  cases h6
  case inl h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h1.left
    let h9 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- Conjunctions on the left can always be decomposed.
      let h13 := h11.left
      let h14 := h11.right
      -- Conjunctions on the left can always be decomposed.
      let h15 := h12.left
      let h16 := h12.right
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h17 =>
      -- One of the premise coincides with the conclusion.
      exact h17
  case inr h18 =>
    -- Conjunctions on the left can always be decomposed.
    let h19 := h1.left
    let h20 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h20
    case inl h21 =>
      -- Conjunctions on the left can always be decomposed.
      let h22 := h21.left
      let h23 := h21.right
      -- Conjunctions on the left can always be decomposed.
      let h24 := h22.left
      let h25 := h22.right
      -- Conjunctions on the left can always be decomposed.
      let h26 := h23.left
      let h27 := h23.right
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h28 =>
      -- One of the premise coincides with the conclusion.
      exact h28



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350352608566945121427514795331 : (p4 → ((p4 → (True ∧ (p2 ∨ (((True ∧ ((p1 ∨ (p1 → p3)) ∧ (p3 ∧ p2))) ∨ p5) ∧ (p5 → ((p2 ∧ (p5 ∨ p3)) → p5)))))) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_715929465802312169243511648154 : (((((p5 ∨ (p2 ∧ True)) ∨ True) ∧ (((p1 ∨ (p5 ∧ (p3 ∨ True))) ∨ (((p1 ∧ ((p4 ∨ p3) ∨ False)) ∨ (p5 ∨ p3)) ∨ p1)) ∨ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_327883271822483029835136024146 : (True → ((p5 ∧ ((False ∨ p3) → ((((p2 ∨ (((True → p1) → (p1 → p3)) ∧ True)) → p5) → (p2 ∧ (p4 ∨ p4))) → p4))) ∨ (True ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231325862335020478467628995739 : (((True → p2) ∨ False) → (((p2 ∨ (((p2 ∨ p5) ∨ p1) → p1)) ∨ (p5 ∨ ((((False → p4) → True) ∨ True) ∧ (True ∨ p4)))) → (p4 ∨ True))) := by
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
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h9 =>
        -- False on the left can always be used.
        apply False.elim h9
  case inr h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h13 =>
        -- False on the left can always be used.
        apply False.elim h13
    case inr h14 =>
      -- Conjunctions on the left can always be decomposed.
      let h15 := h14.left
      let h16 := h14.right
      -- Disjunctions on the left can always be decomposed.
      cases h15
      case inl h17 =>
        -- Disjunctions on the left can always be decomposed.
        cases h16
        case inl h18 =>
          -- Disjunctions on the left can always be decomposed.
          cases h1
          case inl h19 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h20 =>
            -- False on the left can always be used.
            apply False.elim h20
        case inr h21 =>
          -- Disjunctions on the left can always be decomposed.
          cases h1
          case inl h22 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h23 =>
            -- False on the left can always be used.
            apply False.elim h23
      case inr h24 =>
        -- Disjunctions on the left can always be decomposed.
        cases h16
        case inl h25 =>
          -- Disjunctions on the left can always be decomposed.
          cases h1
          case inl h26 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h27 =>
            -- False on the left can always be used.
            apply False.elim h27
        case inr h28 =>
          -- Disjunctions on the left can always be decomposed.
          cases h1
          case inl h29 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h30 =>
            -- False on the left can always be used.
            apply False.elim h30



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317398350702899034622025408926 : (p4 ∨ (((p5 ∨ ((p3 → p5) ∧ p1)) ∨ ((True ∧ (p1 → p4)) ∨ ((p5 ∨ (p3 → True)) ∨ (((p2 → (p4 ∨ p5)) ∨ False) ∨ p4)))) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_653087521096844511206750653159 : ((((True → (p1 ∨ (p3 ∨ ((((p2 ∨ p1) ∧ p4) ∨ p2) → (((False ∧ (p1 ∧ p3)) ∨ False) ∨ ((p1 → True) ∨ True)))))) ∧ (p1 → p1)) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- Implications on the right can always be decomposed.
  intro h9
  -- One of the premise coincides with the conclusion.
  exact h9
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171420108176619461200656538532 : ((((True ∧ p3) ∧ ((True → ((p5 ∧ p3) ∨ ((p1 → p4) ∨ p5))) → p2)) ∧ False) ∨ ((((p1 ∨ p1) → p1) → ((p1 ∨ p3) → p5)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356519802970588013475462517664 : (p5 → ((((p5 ∨ True) ∧ (p4 ∨ ((p5 → True) ∧ p3))) ∧ p1) ∨ (False ∨ ((p4 → p3) → (True → ((((p5 ∧ p3) ∨ False) ∨ True) ∨ p1)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149189710657507327534670907887 : (((p2 → p3) ∧ ((p1 → p5) ∧ ((((p3 → p3) ∨ (p5 ∧ p2)) ∧ (p2 ∨ (False ∨ p3))) → (p1 → p4)))) ∨ ((p5 ∧ (p3 ∧ p2)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_655444189270243589080131201991 : (((((True ∧ ((((((True → p3) → False) → (True → p3)) → ((p5 ∨ False) ∧ (False → p5))) → p1) → p1)) ∨ (p2 ∧ p5)) ∨ (p1 ∨ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178461068203745341806958866798 : (((p2 ∨ (((p5 ∨ p1) ∧ (p1 ∧ p5)) ∧ p4)) ∧ (True ∧ (p4 ∨ p1))) ∨ (((p5 → (p1 ∨ p3)) ∨ (p5 → (p5 → True))) → (True → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115033199981010352677672345029 : (((p5 → (p1 ∧ ((((p5 → (p2 → p3)) ∨ p5) ∧ p3) → p4))) ∧ (((False → ((p2 → p2) ∧ True)) → False) ∨ (p4 ∨ p3))) ∨ (p4 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56190785398135579316736544119 : (((p4 ∧ (p4 → (False ∨ p3))) ∨ ((p3 ∨ p3) ∨ ((p2 ∧ p1) ∨ ((True → p3) → ((p2 → (True ∧ p4)) → (p3 ∨ (p4 → True))))))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148650266131838731895343630474 : ((((p2 ∧ (True ∨ (p2 ∨ True))) → (False ∧ p4)) ∧ (((False ∧ (True ∧ True)) ∨ ((p4 ∧ p3) ∨ p2)) ∧ p5)) ∨ ((p5 → p3) ∨ (p2 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41451899089210115815090590233 : (((((((p3 ∧ p4) ∧ (p2 → p4)) → (p4 ∨ (True ∨ p4))) → p3) ∧ ((((False ∨ (p1 ∧ p5)) → (p5 ∧ p3)) ∨ p3) → True)) ∨ True) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62712676906892763109553507201 : ((p4 ∧ ((True ∧ ((True ∧ (((False → p1) → ((p4 ∨ p5) ∨ (True ∧ ((p5 ∧ p5) ∧ (True ∨ p3))))) ∨ (p5 ∧ p2))) ∨ p2)) → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_660957990462417966351844058437 : (((((p4 → ((p4 → ((p2 ∧ p1) ∧ p3)) → ((p2 → (p1 ∧ p1)) ∨ (((p3 → (p5 ∧ p2)) ∧ p5) → p2)))) → False) → (False ∧ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118356869512858912672590867098 : ((p2 ∨ ((p3 → ((p5 ∧ ((p1 → p3) → (p2 → p3))) → (True ∨ ((p1 ∨ p5) ∨ (True → ((p1 ∨ False) → p5)))))) → p2)) ∨ (False → False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52482808810433305972879008301 : (((False → (((p4 ∧ p1) ∨ (p1 → p4)) ∧ (False ∨ ((p1 ∨ True) → False)))) ∧ (p3 ∧ ((((p1 → (p4 ∨ p1)) ∨ True) → p3) ∧ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_781367073720588802479910726646 : (((p2 ∨ (p2 ∧ ((p1 → (p1 → ((True ∨ (((p2 ∧ p1) ∧ p5) → True)) → p2))) ∨ ((p1 ∨ p2) ∧ (p2 → (p1 → (False ∧ p2))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197003353466495359296363390064 : (((((p4 ∨ p5) ∨ p1) ∧ (False ∨ True)) ∨ p3) ∨ ((((p5 ∧ (True ∧ p2)) ∨ True) → (True ∧ (p2 → True))) → (((p2 ∨ True) ∧ p1) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67608792311543547698617173358 : ((p1 → (p2 ∧ (((p5 ∧ (p4 → True)) → p4) ∧ ((((((False → (True → True)) ∧ p2) ∨ p4) ∧ True) ∧ (p3 ∨ (p2 ∨ p1))) ∨ True)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112717561597888173429211920855 : ((((p4 → (((p1 ∨ (p3 → (p4 ∨ ((p2 ∨ p2) ∨ p1)))) ∧ p5) → False)) ∧ (p3 ∧ (False → (p3 → (p4 ∨ p2))))) → p1) ∨ (p2 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178752413081406576578936962072 : ((((p3 ∨ p3) ∧ p2) ∧ ((p4 ∧ False) ∨ ((p2 ∧ p2) → (p2 ∧ p1)))) ∨ (False → (True ∨ (True ∨ (((True → (True ∧ True)) ∨ True) → p5))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42189627522575529121576432021 : (((True ∧ (((p3 ∧ p4) → ((p5 ∧ False) ∨ ((False ∧ p2) ∧ (p5 ∧ p2)))) ∨ (True ∨ (((p5 → True) ∧ (True ∧ False)) ∧ p4)))) ∨ p3) ∨ p4) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_625838805946030463320228784656 : ((((p1 → (p4 → (p2 ∧ (((((p2 ∧ (p3 → (p1 → True))) → p3) → (p4 ∨ (False → p4))) → ((False ∧ p1) ∨ p3)) ∧ p1)))) ∨ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149513797774509355466836470044 : ((p1 ∧ (((True ∨ True) ∨ False) → (((p4 ∨ p2) ∧ (p4 ∨ ((p1 → ((p2 → p1) → True)) ∧ p3))) ∨ p3))) ∨ (True → (False → (False ∨ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_302679155735982378059097282549 : (False ∨ (p3 ∨ (((((((False ∧ p3) ∨ p4) ∨ p1) → (p3 ∨ (p3 → ((True ∧ p5) ∨ (p5 ∧ True))))) → (False ∨ p5)) ∨ (p3 ∨ True)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336456139743868439638256403289 : (p1 → ((True → (p3 ∨ ((False ∧ (False ∨ ((False → (False → (p1 → p2))) → (False ∧ (False ∧ (True ∨ True)))))) ∧ (p2 → (False ∨ p4))))) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_427223572815067227530395633317 : (((((((p5 ∧ p5) ∧ ((((p1 ∧ p3) ∧ p5) ∧ ((p2 ∨ ((p1 → p3) → p2)) → p2)) ∨ False)) → (p2 ∧ True)) ∧ p3) ∨ (p2 → True)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114958397549258983089670282782 : (((False ∨ ((p1 → (((False ∨ (p4 → p2)) ∧ p1) ∧ p3)) ∨ (True ∨ True))) → (((p5 → (p3 → False)) ∨ False) ∧ (p5 → True))) ∨ (False → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174396038444701397119677238741 : (((p3 ∨ ((p4 ∨ ((True ∧ True) → True)) ∨ p2)) ∧ (p1 → (False ∨ (p5 ∧ p5)))) → ((p5 → ((p5 → p2) ∨ p5)) ∧ (p1 → (True ∧ p5)))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h2
      case inr h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h2
    case inr h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
  -- Implications on the right can always be decomposed.
  intro h11
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h12 := h1.left
  let h13 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h12
  case inl h14 =>
    -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
    have h15 : p1 := by
      -- One of the premise coincides with the conclusion.
      exact h11
    -- We have shown the premise of h13, we can now drive its conclusion.
    let h16 := h13 h15
    -- Disjunctions on the left can always be decomposed.
    cases h16
    case inl h17 =>
      -- False on the left can always be used.
      apply False.elim h17
    case inr h18 =>
      -- Conjunctions on the left can always be decomposed.
      let h19 := h18.left
      let h20 := h18.right
      -- One of the premise coincides with the conclusion.
      exact h20
  case inr h21 =>
    -- Disjunctions on the left can always be decomposed.
    cases h21
    case inl h22 =>
      -- Disjunctions on the left can always be decomposed.
      cases h22
      case inl h23 =>
        -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
        have h24 : p1 := by
          -- One of the premise coincides with the conclusion.
          exact h11
        -- We have shown the premise of h13, we can now drive its conclusion.
        let h25 := h13 h24
        -- Disjunctions on the left can always be decomposed.
        cases h25
        case inl h26 =>
          -- False on the left can always be used.
          apply False.elim h26
        case inr h27 =>
          -- Conjunctions on the left can always be decomposed.
          let h28 := h27.left
          let h29 := h27.right
          -- One of the premise coincides with the conclusion.
          exact h29
      case inr h30 =>
        -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
        have h31 : p1 := by
          -- One of the premise coincides with the conclusion.
          exact h11
        -- We have shown the premise of h13, we can now drive its conclusion.
        let h32 := h13 h31
        -- Disjunctions on the left can always be decomposed.
        cases h32
        case inl h33 =>
          -- False on the left can always be used.
          apply False.elim h33
        case inr h34 =>
          -- Conjunctions on the left can always be decomposed.
          let h35 := h34.left
          let h36 := h34.right
          -- One of the premise coincides with the conclusion.
          exact h36
    case inr h37 =>
      -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
      have h38 : p1 := by
        -- One of the premise coincides with the conclusion.
        exact h11
      -- We have shown the premise of h13, we can now drive its conclusion.
      let h39 := h13 h38
      -- Disjunctions on the left can always be decomposed.
      cases h39
      case inl h40 =>
        -- False on the left can always be used.
        apply False.elim h40
      case inr h41 =>
        -- Conjunctions on the left can always be decomposed.
        let h42 := h41.left
        let h43 := h41.right
        -- One of the premise coincides with the conclusion.
        exact h43



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42919758927466602555003180778 : (((p4 → (((((True → ((p2 → False) ∧ ((p3 ∨ False) → (p5 → False)))) ∨ (p3 ∧ (True ∧ p3))) ∨ False) ∧ (p3 → p4)) ∧ False)) ∨ True) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257127939098878886585659966098 : ((p2 ∨ p1) → ((p3 → (((True → ((((((p5 ∨ ((p4 ∨ p2) ∧ p3)) ∨ p4) → p4) → p1) ∧ p4) → (False → p5))) ∨ True) → p4)) ∨ True)) := by
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



