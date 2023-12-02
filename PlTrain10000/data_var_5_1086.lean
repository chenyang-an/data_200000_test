variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41555153364679524366680525292 : ((((((p5 ∨ p5) ∨ ((p5 → p4) → (p3 ∨ p4))) ∨ p1) → (((True ∧ ((p5 → p4) ∨ p2)) ∧ p4) ∨ ((p5 → p4) ∧ False))) ∨ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233011848536848122441228937308 : ((p4 ∧ (p1 ∧ True)) → ((p2 ∧ ((p2 ∨ p4) ∧ (((p5 → p2) → (False ∨ (True ∨ False))) → (p2 ∧ ((p4 → p2) → (p4 → p4)))))) ∨ p4)) := by
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
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260271337151711526165260320360 : ((p2 → p3) → (p1 → (((p1 ∨ p5) → False) → (False ∨ (False ∨ (p1 → (p2 ∧ (((True ∨ ((False → p5) ∧ p2)) ∨ p5) ∨ (p5 ∧ p5))))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : (p1 ∨ p5) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_587024406179300366242506494023 : (((((p5 ∨ ((p2 ∧ True) ∧ (((p2 ∨ (((p1 ∧ True) ∧ (((p3 ∧ p2) ∧ p4) → p3)) ∧ False)) ∨ (p5 → p2)) → p2))) ∧ False) ∧ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351202710203035816746650133664 : (p4 → ((p3 → ((True ∧ (p2 ∨ (False ∧ ((p2 ∧ (p5 ∨ False)) ∨ (((p3 ∨ p4) ∨ p1) → (True ∨ True)))))) ∨ p4)) ∧ ((p2 ∨ p4) → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116090110828499632382808690841 : ((((p3 ∨ p1) ∨ p2) ∧ (((p1 → (p4 → ((p2 → p1) → ((True → True) → p3)))) ∧ True) → (((p5 ∨ False) ∧ True) → p1))) ∨ (p1 → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_24234628985106513990993880988 : (((p3 → (True ∧ (p2 ∧ p3))) → (((((False → p5) ∧ True) ∧ (p3 → p4)) → ((False ∧ False) ∨ (p3 ∨ ((p5 ∧ False) ∧ p5)))) ∨ True)) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300906271893938852238225395045 : (False ∨ (((((p5 ∨ p3) ∧ p3) ∧ ((p1 → True) ∧ p4)) ∨ (p1 ∧ (p4 ∧ p2))) → (p5 ∨ (p5 ∨ (p1 → ((p4 ∨ (p2 ∨ False)) ∧ p1)))))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h3.left
    let h6 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h4.left
      let h9 := h4.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h4.left
      let h12 := h4.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h13
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h12
      -- One of the premise coincides with the conclusion.
      exact h13
  case inr h14 =>
    -- Conjunctions on the left can always be decomposed.
    let h15 := h14.left
    let h16 := h14.right
    -- Conjunctions on the left can always be decomposed.
    let h17 := h16.left
    let h18 := h16.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h19
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h17
    -- One of the premise coincides with the conclusion.
    exact h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137782292395460618464151814052 : ((p2 ∨ (((p4 ∨ p4) ∧ True) ∨ ((False → p1) → ((False ∧ (False ∧ (((p5 → p5) ∧ p2) ∧ (p4 ∨ p3)))) ∨ p4)))) ∨ (p2 ∨ (False → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65134211721577702461537643371 : ((p2 ∨ (p2 → ((((((p1 ∨ (((p1 ∨ (p5 ∨ (p4 ∧ (p3 ∨ p3)))) ∧ False) → p1)) → (p5 ∨ True)) ∧ p3) ∨ p1) ∧ p5) ∨ p2))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_710307360850609524081399179118 : (((((p3 → ((p4 → p5) → p1)) ∨ True) ∧ (p2 ∨ (True → (p4 ∨ ((p2 ∧ p4) ∨ (p1 ∨ (((True ∨ (p4 ∧ p4)) ∧ p3) ∨ p5))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_913427569752825086179391528203 : ((((False ∨ (((p1 → (p1 ∨ (((p4 ∧ True) → (p5 ∨ p5)) → True))) ∧ False) → (p1 ∨ p2))) → (p2 ∧ ((p2 → (p4 ∧ p5)) ∧ False))) → p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (False ∨ (((p1 → (p1 ∨ (((p4 ∧ True) → (p5 ∨ p5)) → True))) ∧ False) → (p1 ∨ p2))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- False on the left can always be used.
    apply False.elim h5
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h2
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- False on the left can always be used.
  apply False.elim h8
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_773950113008153942347408719763 : (((False ∨ ((p4 → (((p3 → (True → (p1 → (False → p2)))) ∨ (((p1 ∨ p1) → (p4 ∨ p3)) ∧ p2)) ∨ (p3 ∧ (True ∨ p3)))) → p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_702457073102838464876893765680 : (((((p3 ∨ ((((p3 ∧ False) ∧ p1) ∨ p3) ∧ p5)) ∨ True) ∨ ((p2 ∧ True) ∨ ((p5 → (p1 ∧ ((p1 ∨ (p2 → p2)) ∧ p2))) ∧ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_619176378693305669843952756803 : (((((p5 ∨ (False ∧ p3)) ∨ (p2 ∨ ((p1 ∨ ((p3 ∧ (p5 ∨ True)) → (((p4 → ((p5 ∧ False) ∨ p5)) ∧ False) → p2))) ∨ p3))) ∨ p2) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111656398220501825347194710518 : ((((False ∧ (((p1 → ((False ∨ (p1 ∧ (p1 ∨ (True ∧ (False → p2))))) → True)) ∨ p4) → ((False ∨ p5) ∨ p5))) ∨ p1) ∨ True) ∨ (p3 → p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258034201335254458684518751744 : ((p4 ∨ p2) → ((((p1 ∨ (((False ∨ p1) → p4) → ((p2 → ((False ∧ p1) ∨ p5)) ∨ (p5 ∧ True)))) ∨ (False → (p5 ∨ True))) ∨ False) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190606221828469762150812208748 : ((((False ∨ p3) → (((True ∧ p4) ∨ p2) ∨ p5)) → p2) ∨ (False → ((p4 ∨ (False ∧ p4)) → (p5 ∧ ((True → p3) → ((p2 → p5) ∧ p4)))))) := by
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
    -- False on the left can always be used.
    apply False.elim h1
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- False on the left can always be used.
    apply False.elim h5
  -- Implications on the right can always be decomposed.
  intro h7
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h8
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h9 =>
    -- False on the left can always be used.
    apply False.elim h1
  case inr h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- False on the left can always be used.
    apply False.elim h11
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h13 =>
    -- False on the left can always be used.
    apply False.elim h1
  case inr h14 =>
    -- Conjunctions on the left can always be decomposed.
    let h15 := h14.left
    let h16 := h14.right
    -- False on the left can always be used.
    apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187243323038484685247625796245 : ((True ∧ (((False → (p4 ∨ True)) ∨ (p2 ∧ True)) ∧ (p2 ∨ p4))) → (False ∨ (((p5 ∨ (False ∨ p5)) → ((p4 ∨ p1) → (p4 ∨ True))) ∨ p1))) := by
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
    cases h5
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h8
      -- Implications on the right can always be decomposed.
      intro h9
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Disjunctions on the left can always be decomposed.
        cases h8
        case inl h11 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h10
        case inr h12 =>
          -- Disjunctions on the left can always be decomposed.
          cases h12
          case inl h13 =>
            -- False on the left can always be used.
            apply False.elim h13
          case inr h14 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h10
      case inr h15 =>
        -- Disjunctions on the left can always be decomposed.
        cases h8
        case inl h16 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h17 =>
          -- Disjunctions on the left can always be decomposed.
          cases h17
          case inl h18 =>
            -- False on the left can always be used.
            apply False.elim h18
          case inr h19 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
    case inr h20 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h21
      -- Implications on the right can always be decomposed.
      intro h22
      -- Disjunctions on the left can always be decomposed.
      cases h22
      case inl h23 =>
        -- Disjunctions on the left can always be decomposed.
        cases h21
        case inl h24 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h23
        case inr h25 =>
          -- Disjunctions on the left can always be decomposed.
          cases h25
          case inl h26 =>
            -- False on the left can always be used.
            apply False.elim h26
          case inr h27 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h23
      case inr h28 =>
        -- Disjunctions on the left can always be decomposed.
        cases h21
        case inl h29 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h20
        case inr h30 =>
          -- Disjunctions on the left can always be decomposed.
          cases h30
          case inl h31 =>
            -- False on the left can always be used.
            apply False.elim h31
          case inr h32 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h20
  case inr h33 =>
    -- Conjunctions on the left can always be decomposed.
    let h34 := h33.left
    let h35 := h33.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h36 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h37
      -- Implications on the right can always be decomposed.
      intro h38
      -- Disjunctions on the left can always be decomposed.
      cases h38
      case inl h39 =>
        -- Disjunctions on the left can always be decomposed.
        cases h37
        case inl h40 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h39
        case inr h41 =>
          -- Disjunctions on the left can always be decomposed.
          cases h41
          case inl h42 =>
            -- False on the left can always be used.
            apply False.elim h42
          case inr h43 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h39
      case inr h44 =>
        -- Disjunctions on the left can always be decomposed.
        cases h37
        case inl h45 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h46 =>
          -- Disjunctions on the left can always be decomposed.
          cases h46
          case inl h47 =>
            -- False on the left can always be used.
            apply False.elim h47
          case inr h48 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
    case inr h49 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h50
      -- Implications on the right can always be decomposed.
      intro h51
      -- Disjunctions on the left can always be decomposed.
      cases h51
      case inl h52 =>
        -- Disjunctions on the left can always be decomposed.
        cases h50
        case inl h53 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h52
        case inr h54 =>
          -- Disjunctions on the left can always be decomposed.
          cases h54
          case inl h55 =>
            -- False on the left can always be used.
            apply False.elim h55
          case inr h56 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h52
      case inr h57 =>
        -- Disjunctions on the left can always be decomposed.
        cases h50
        case inl h58 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h49
        case inr h59 =>
          -- Disjunctions on the left can always be decomposed.
          cases h59
          case inl h60 =>
            -- False on the left can always be used.
            apply False.elim h60
          case inr h61 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h49



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156940596333635022323483556457 : (((((p1 ∨ (p2 → p4)) ∨ (((p4 ∨ p1) ∧ ((p4 ∨ p4) → p2)) ∨ p5)) ∨ (True → True)) ∨ p2) ∨ ((True → p1) ∧ ((p4 ∨ p1) → p3))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149002415503071003982269035475 : (((p5 → (p4 ∨ p4)) ∧ (False ∧ (p2 ∨ (((p3 ∧ p4) ∧ p4) ∨ (p1 ∨ (p3 ∧ (p1 → (p4 ∧ p3)))))))) ∨ (False → ((p3 ∨ True) ∧ p5))) := by
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
theorem thm_5_vars_57822866374059306607894091850 : (((p3 ∧ (p4 → True)) → (p1 ∨ (False ∨ ((((True ∨ p3) ∧ True) ∧ p2) ∨ (((p1 ∧ p4) ∧ (True → ((p2 ∧ p5) ∨ p4))) ∨ p3))))) ∨ p4) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158692417164829509330399766147 : ((p2 ∧ ((p5 → p4) → ((True ∨ ((p4 ∨ False) ∨ (p4 ∨ (((True ∨ p5) ∧ False) → p2)))) → p2))) ∨ (((p5 ∨ (True ∧ False)) ∧ p1) → p5)) := by
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
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- False on the left can always be used.
    apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111028622667464890004535127853 : ((((p4 ∨ (((p2 ∧ p4) ∨ (p4 ∨ (p5 → p2))) → ((p3 ∨ p1) ∨ (p4 ∨ (p4 ∨ p1))))) → (p2 → (False ∨ p3))) ∧ p3) ∨ (True ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116496372202983051329998923568 : (((p3 ∧ p1) ∧ (((((True → (p4 → ((p1 ∨ p4) ∧ p3))) ∧ ((((p2 ∧ True) ∧ p4) ∨ p5) → p4)) → False) ∨ True) ∨ p2)) ∨ (True ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158627729338784675507125729274 : ((False ∧ (p4 → ((((p3 ∨ p4) ∧ p4) ∨ (p3 ∨ p5)) → (((False ∧ False) → (p5 → True)) → p2)))) ∨ ((((False → p3) ∧ False) ∧ p4) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_637869757880937647927385915447 : (((((((p5 → p5) → (p5 ∧ p2)) → (False ∧ p5)) ∧ ((((((p2 ∨ p2) → p4) ∨ (False ∧ (p4 ∨ p3))) ∧ p5) → True) ∧ p5)) → p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59363047332251873313887111251 : (((p5 ∨ p3) ∨ (((((p4 ∧ (p2 ∨ p4)) ∨ p1) ∨ (p1 → True)) ∧ ((p2 ∧ (False → True)) → (p1 → False))) ∧ ((True ∧ p5) ∨ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46922880967878081735300638186 : ((((((p2 ∧ p5) → True) ∧ (p1 → ((False → (((p5 → False) ∧ (p2 → p5)) → (p3 ∧ p4))) → (True ∧ p4)))) ∨ False) ∨ (p3 ∨ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_355828626213470086656267626055 : (p5 → ((((((p3 ∨ False) → p1) ∧ (p3 ∧ ((False ∧ (p3 ∧ (p5 ∧ (p1 ∧ p2)))) ∨ (False → p1)))) ∧ False) ∧ False) ∨ ((p1 → p5) ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_752220565895546379172033188969 : (((True ∧ (p4 → ((((((p4 ∧ (False ∧ p5)) ∧ p5) ∨ ((True ∧ ((p4 ∨ p5) ∨ p3)) → True)) ∧ (p2 ∧ (p5 ∧ False))) ∧ p3) ∧ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_668005987382309375718113880496 : ((((p4 ∨ ((p5 → (p5 ∨ ((True → True) ∨ False))) → (p4 ∨ ((((p5 → (p3 ∨ p4)) ∨ p5) ∧ False) ∧ p2)))) ∧ ((p1 ∨ p5) ∨ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44157287273776576366400212965 : (((((p4 ∧ (((p5 → p4) ∧ ((p1 → (p4 → p3)) ∧ ((p1 ∨ p1) → True))) → True)) ∨ (p5 ∨ p3)) → ((p5 ∨ p4) ∧ p2)) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257688459414850518209807567811 : ((p3 ∨ p3) → (((((p3 → (p5 ∧ (p2 ∨ p2))) ∧ p5) ∨ (((p4 → (p4 → p5)) → p3) → p4)) ∨ True) ∨ ((p5 → (p1 ∧ p2)) → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_306651959721715570878228432850 : (p1 ∨ (True ∧ ((((p5 ∧ p1) ∧ (p4 ∨ (((True ∧ p5) → False) ∨ False))) ∨ (p5 ∨ (p1 ∨ (p2 → p2)))) ∨ ((p5 ∧ p5) ∧ (False → p2))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_732227419863714139480538570567 : ((((True ∧ p5) ∧ ((p2 ∧ True) ∨ ((((((p5 → (((p5 ∧ (False ∨ p4)) ∨ p3) ∨ (p1 ∧ p4))) → True) → False) ∨ p2) ∨ True) ∧ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150343803734935754442302563312 : ((p5 → ((p4 → ((((p2 ∨ (p4 ∧ False)) ∧ p2) ∨ ((False → p4) → p1)) ∨ p2)) ∧ (False → (False ∧ p3)))) ∨ ((p4 ∧ (p4 ∧ p3)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_694098167527071733860777564480 : (((((((p1 ∨ (False ∧ p3)) → (p4 ∧ p4)) ∨ True) → ((p5 → p1) ∧ p5)) ∨ ((p5 ∨ p5) → (p5 ∨ ((p2 ∧ p1) ∧ (True → p2))))) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111438446119014748989407245155 : (((p5 ∨ ((p3 → (p2 → ((((p5 ∨ ((False ∨ p5) ∧ (p3 ∧ True))) ∧ False) ∧ p3) ∧ False))) ∧ (p4 ∨ (True → False)))) ∧ p4) ∨ (p5 → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111251332736034073325705390541 : ((((p2 ∧ p4) ∨ (((False → (p4 ∧ False)) ∧ p1) → ((p3 ∨ (p5 ∧ p5)) ∨ ((((p4 → False) ∧ p4) → p2) ∨ True)))) ∧ p1) ∨ (True ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317988476435434494738062164367 : (p4 ∨ ((p4 → (((p5 ∨ ((((False ∨ p1) ∧ p4) → (True → p3)) → p4)) → (p2 → (((False ∨ (p1 ∨ p3)) ∧ p1) ∨ p2))) → False)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199189486483656674582397879998 : (((p3 ∧ (p5 ∨ (True → (p5 ∧ p5)))) ∧ p1) → (((True ∨ (p5 → (True ∧ p2))) → (p2 ∨ p2)) ∨ ((False ∨ p4) → ((False ∧ False) ∨ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- False on the left can always be used.
      apply False.elim h8
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
  case inr h10 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h11
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- False on the left can always be used.
      apply False.elim h12
    case inr h13 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319316101810134630973533537460 : (p4 ∨ (((p2 → True) → ((p2 → (p4 → ((p1 ∨ p1) → p4))) → ((p2 → False) ∧ False))) → ((p3 ∧ (p3 → p4)) → ((False ∧ p1) ∧ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h5 : (p2 → True) := by
    -- Implications on the right can always be decomposed.
    intro h6
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h7 := h1 h5
  -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
  have h8 : (p2 → (p4 → ((p1 ∨ p1) → p4))) := by
    -- Implications on the right can always be decomposed.
    intro h9
    -- Implications on the right can always be decomposed.
    intro h10
    -- Implications on the right can always be decomposed.
    intro h11
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- One of the premise coincides with the conclusion.
      exact h10
    case inr h13 =>
      -- One of the premise coincides with the conclusion.
      exact h10
  -- We have shown the premise of h7, we can now drive its conclusion.
  let h14 := h7 h8
  -- We need to get the right conjuct of h14 based on <expert-advice>.
  let h15 := h14.right
  -- False on the left can always be used.
  apply False.elim h15
  -- Conjunctions on the left can always be decomposed.
  let h16 := h2.left
  let h17 := h2.right
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h18 : (p2 → True) := by
    -- Implications on the right can always be decomposed.
    intro h19
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h20 := h1 h18
  -- We want to use the implication h20 based on <expert-advice>. So we show its premise.
  have h21 : (p2 → (p4 → ((p1 ∨ p1) → p4))) := by
    -- Implications on the right can always be decomposed.
    intro h22
    -- Implications on the right can always be decomposed.
    intro h23
    -- Implications on the right can always be decomposed.
    intro h24
    -- Disjunctions on the left can always be decomposed.
    cases h24
    case inl h25 =>
      -- One of the premise coincides with the conclusion.
      exact h23
    case inr h26 =>
      -- One of the premise coincides with the conclusion.
      exact h23
  -- We have shown the premise of h20, we can now drive its conclusion.
  let h27 := h20 h21
  -- We need to get the right conjuct of h27 based on <expert-advice>.
  let h28 := h27.right
  -- False on the left can always be used.
  apply False.elim h28
  -- Conjunctions on the left can always be decomposed.
  let h29 := h2.left
  let h30 := h2.right
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h31 : (p2 → True) := by
    -- Implications on the right can always be decomposed.
    intro h32
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h33 := h1 h31
  -- We want to use the implication h33 based on <expert-advice>. So we show its premise.
  have h34 : (p2 → (p4 → ((p1 ∨ p1) → p4))) := by
    -- Implications on the right can always be decomposed.
    intro h35
    -- Implications on the right can always be decomposed.
    intro h36
    -- Implications on the right can always be decomposed.
    intro h37
    -- Disjunctions on the left can always be decomposed.
    cases h37
    case inl h38 =>
      -- One of the premise coincides with the conclusion.
      exact h36
    case inr h39 =>
      -- One of the premise coincides with the conclusion.
      exact h36
  -- We have shown the premise of h33, we can now drive its conclusion.
  let h40 := h33 h34
  -- We need to get the right conjuct of h40 based on <expert-advice>.
  let h41 := h40.right
  -- False on the left can always be used.
  apply False.elim h41



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230354778405201721059285134496 : (((p2 ∨ p4) ∧ p2) → (((p5 ∨ (((False ∧ p5) ∧ p4) → ((p2 ∧ p2) → False))) → False) → (p4 ∨ (((p2 → (p5 → False)) ∨ True) → p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h6 : (p5 ∨ (((False ∧ p5) ∧ p4) → ((p2 ∧ p2) → False))) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h7
      -- Implications on the right can always be decomposed.
      intro h8
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Conjunctions on the left can always be decomposed.
      let h11 := h7.left
      let h12 := h7.right
      -- Conjunctions on the left can always be decomposed.
      let h13 := h11.left
      let h14 := h11.right
      -- False on the left can always be used.
      apply False.elim h13
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h15 := h2 h6
    -- False on the left can always be used.
    apply False.elim h15
  case inr h16 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338811531419800621320572589652 : (p1 → ((p2 ∨ p3) ∨ ((p5 → ((p1 → False) ∨ (((p3 ∨ ((p4 ∨ (p5 ∨ p4)) ∧ (p5 → (p3 ∧ p1)))) → p4) ∨ (p2 ∧ True)))) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_813564126877173340584475111951 : (((((True → (((((False ∨ (p4 ∨ p1)) → p2) → ((False ∨ False) ∨ True)) → ((((p3 ∨ p2) ∨ False) → False) ∧ p4)) ∧ p1)) ∧ p2) ∧ True) → p3) ∧ True) := by
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
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h6 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h7 := h4 h6
  -- We need to get the left conjuct of h7 based on <expert-advice>.
  let h8 := h7.left
  -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
  have h9 : (((False ∨ (p4 ∨ p1)) → p2) → ((False ∨ False) ∨ True)) := by
    -- Implications on the right can always be decomposed.
    intro h10
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h8, we can now drive its conclusion.
  let h11 := h8 h9
  -- We need to get the left conjuct of h11 based on <expert-advice>.
  let h12 := h11.left
  -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
  have h13 : ((p3 ∨ p2) ∨ False) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h12, we can now drive its conclusion.
  let h14 := h12 h13
  -- False on the left can always be used.
  apply False.elim h14
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118260269826323158416649824412 : ((p1 ∨ (((p3 ∧ ((p1 ∧ False) ∧ (p2 ∨ (p2 ∧ p1)))) ∨ ((p1 ∨ True) ∨ p5)) → (p1 ∧ ((True ∧ (False → p4)) ∧ p1)))) ∨ (p4 → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_326002940287783668433377917889 : (p5 ∨ (True → (((p4 ∨ (p1 → p4)) ∨ (p2 → p3)) ∨ ((p5 ∨ (((p2 → (p2 ∨ (True ∨ (p3 → p4)))) ∧ p3) ∨ (p5 ∧ p4))) ∨ True)))) := by
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
theorem thm_5_vars_66250241157682629452414888025 : ((p5 ∨ (((p2 ∨ p3) ∧ (p5 ∧ p5)) ∧ ((p4 ∧ ((p4 ∧ p1) → p5)) ∨ (((p4 ∨ p1) → p1) ∧ (p4 ∨ (p5 → (True ∨ False))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219280084630128195493065529780 : ((p1 ∨ (p3 → (False → p1))) → ((p3 ∨ (p4 ∨ ((((p4 ∨ (((p4 → p5) → p3) → p5)) → p2) ∧ True) ∨ (p1 ∨ p2)))) ∨ (p3 → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259272258543457509704998852568 : ((False → p1) → ((p1 ∧ (((p4 ∧ (p2 → False)) ∧ ((p4 ∨ p5) ∨ p1)) ∧ False)) ∨ ((True ∨ (True → (p4 ∨ p2))) ∨ ((p4 → p5) → p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192845599809803436905584580837 : ((((p1 ∨ ((p2 ∨ p4) → p2)) ∨ p1) ∧ (p4 ∨ p2)) → ((p4 ∧ (p2 ∨ (False ∧ (p5 ∨ (((p5 ∧ p2) ∨ p3) ∨ p1))))) → (p3 ∨ p4))) := by
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
    cases h6
    case inl h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Disjunctions on the left can always be decomposed.
        cases h7
        case inl h10 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h10
        case inr h11 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h3
      case inr h12 =>
        -- Disjunctions on the left can always be decomposed.
        cases h7
        case inl h13 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h13
        case inr h14 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h3
    case inr h15 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h16 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h16
      case inr h17 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h3
  case inr h18 =>
    -- Conjunctions on the left can always be decomposed.
    let h19 := h18.left
    let h20 := h18.right
    -- False on the left can always be used.
    apply False.elim h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178255361041378376671348454092 : ((((((p4 ∨ p4) ∨ p3) ∧ ((p1 ∨ False) ∧ True)) → p1) ∧ (True → False)) ∨ ((True → ((((False ∧ False) ∨ p3) ∨ (p5 ∨ True)) ∧ False)) → False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_117773012117959230856258621270 : ((p4 ∧ ((p5 → ((((p2 ∧ (p3 ∧ p5)) ∧ ((p1 ∧ False) → p1)) → False) ∨ (((False ∨ p2) ∨ p3) ∨ p3))) ∨ (p1 ∨ p5))) ∨ (p3 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350892419569324413690542864852 : (p4 → ((True → (((False ∧ ((True → p3) → (p4 ∨ (True ∨ (p3 → p3))))) ∧ (p3 → ((True ∧ p1) ∨ False))) ∨ (False → p3))) ∧ (False ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114169556444042223042675161780 : ((((((p1 ∧ (p3 → p1)) ∨ ((p1 → (p2 → (p2 ∨ p3))) ∨ (p2 ∧ p4))) ∨ p1) ∧ (p3 ∨ p1)) → ((p4 → p5) → False)) ∨ (p3 → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138826829910102925515402581166 : (((p3 ∧ ((((False → (p5 → p2)) ∨ (True → (p3 ∨ True))) ∧ (((p4 ∧ (p1 → p3)) → p4) → p4)) ∧ p4)) ∧ True) → ((p2 ∧ p1) ∨ True)) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h8
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
theorem thm_5_vars_204293682845702561096867891689 : ((((p2 → True) → (p5 ∧ p5)) ∧ True) ∨ ((((p4 ∨ p4) → p5) → ((p1 ∨ p2) → (p2 ∧ p5))) ∨ ((True ∧ False) → (p2 ∧ (p5 → False))))) := by
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
  -- False on the left can always be used.
  apply False.elim h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h1.left
  let h6 := h1.right
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_783318115731175901063261159960 : (((p3 ∨ (((((p4 ∨ ((p5 → (p1 ∨ p3)) ∨ p4)) → p2) ∧ (False ∨ (p2 → p3))) ∨ (p2 → p2)) → (p3 ∨ (p5 ∨ (True ∧ True))))) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    cases h4
    case inl h5 =>
      -- False on the left can always be used.
      apply False.elim h5
    case inr h6 =>
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
  case inr h7 =>
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49571271230216404013906186899 : (((((((p1 ∨ p1) ∨ p4) ∨ p3) ∧ (((p1 → (p5 → p1)) ∨ p3) ∧ p2)) ∧ ((p5 ∨ (p1 ∧ p1)) → True)) → ((p5 ∨ True) ∧ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178328082940874152513243690796 : ((((p4 ∧ (p1 → (True ∨ (False ∧ False)))) → (False ∨ p1)) ∨ (False → p4)) ∨ ((p4 → (False → ((p1 ∨ p1) ∧ p2))) ∨ ((p1 → p2) ∧ p2))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299234352871416266724120273626 : (False ∨ ((((p5 ∧ (p1 ∧ (p3 ∨ (p1 → (False → ((p3 → True) ∧ (p5 ∨ (False ∧ False)))))))) ∨ (p1 ∨ True)) ∧ (False → (p5 → p3))) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_739305776145187592770751610253 : ((((p4 ∧ p3) ∨ ((((((True ∨ False) → p5) → p4) → p3) ∨ (False ∧ p3)) ∨ (p1 ∨ (True ∨ ((p3 ∧ (p5 ∧ (p5 → p2))) ∧ True))))) ∨ False) ∧ True) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_355545840903540892302498002827 : (p5 → (((p5 ∧ ((p4 ∨ ((p4 ∧ (p4 → (p5 ∨ (p1 ∨ False)))) → (((p2 → p3) → p1) ∨ (p3 ∧ p3)))) → p4)) ∨ p1) ∨ (True ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157541037471300548147712677887 : ((((p4 ∧ ((False → ((p5 ∨ (p1 ∧ True)) ∨ ((p3 → p5) → True))) → p3)) ∨ p1) → (p2 ∨ p2)) ∨ (((p1 ∧ (p1 ∧ p1)) ∧ p1) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58524780023575042273407105214 : (((p5 ∨ p1) ∧ (((((False ∨ p5) ∨ ((True ∨ ((False → p2) → p5)) ∧ False)) ∨ p1) ∧ ((False ∨ p3) → (False → p3))) ∧ (p2 ∨ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350321206482808442126964929163 : (p4 → ((True → (((p3 ∧ ((p2 → True) ∨ p3)) ∨ (((p5 ∧ True) ∧ (p1 → (p4 → ((p2 → (p2 ∨ p5)) → p5)))) ∨ p4)) ∨ p2)) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_655105068275923464795104364821 : (((((p2 ∨ ((p3 → (p3 ∧ (((p3 ∨ p1) ∨ p3) ∨ (p2 → ((p1 → p2) → p3))))) ∨ ((p3 ∧ True) → p3))) → p2) ∨ (p4 → True)) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_66076906876638670020277678134 : ((p5 ∨ ((p4 ∧ ((p4 → ((p1 → ((p3 ∧ (p4 ∧ ((True ∨ True) ∨ p1))) ∨ ((p1 ∨ True) → False))) ∧ p2)) → (False ∧ p4))) ∨ True)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134220375167833516637307275945 : ((((p3 ∨ ((p2 ∨ p4) ∧ (p1 ∨ True))) ∧ (p3 → (((p5 ∨ False) ∨ p2) → ((p4 ∨ (False → p5)) ∨ p2)))) ∨ p3) ∨ (p3 ∨ (True ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43596370205791268556675180210 : (((((p2 ∨ (True ∧ (((p4 ∧ (p3 ∨ ((p1 ∨ (True → (p1 ∧ p3))) ∧ (p2 → p3)))) ∧ (p1 → p3)) ∨ p4))) ∨ p2) → False) → p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159157885587691950641427607750 : ((p1 → (((True → True) → ((((False ∧ (True ∨ p2)) ∨ ((True → p3) → p5)) ∧ p1) ∧ p3)) ∨ False)) ∨ (((False ∨ True) → (False ∨ p3)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_702252226669254067871960043533 : (((((((p4 ∧ p1) → p4) → ((True ∧ p1) ∧ False)) ∧ p5) ∨ (p5 ∨ ((((p4 ∨ (p2 → p3)) ∨ (p1 ∨ p4)) ∨ p3) ∧ (False → p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_746394619026309337355931793070 : ((((p2 ∨ p1) → ((p1 ∨ ((p5 → False) → p2)) → ((True → (False ∧ (((p2 ∧ (p4 → p2)) → ((p3 ∧ p3) → True)) ∨ p4))) → p4))) ∨ p3) ∧ True) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h5 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h6 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h7 := h3 h6
      -- We need to get the left conjuct of h7 based on <expert-advice>.
      let h8 := h7.left
      -- False on the left can always be used.
      apply False.elim h8
    case inr h9 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h10 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h11 := h3 h10
      -- We need to get the left conjuct of h11 based on <expert-advice>.
      let h12 := h11.left
      -- False on the left can always be used.
      apply False.elim h12
  case inr h13 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h14 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h15 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h16 := h3 h15
      -- We need to get the left conjuct of h16 based on <expert-advice>.
      let h17 := h16.left
      -- False on the left can always be used.
      apply False.elim h17
    case inr h18 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h19 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h20 := h3 h19
      -- We need to get the left conjuct of h20 based on <expert-advice>.
      let h21 := h20.left
      -- False on the left can always be used.
      apply False.elim h21
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_247953703610594436761175196140 : ((p1 ∨ p4) ∨ (((((p4 → False) ∧ True) ∧ ((p3 ∨ p4) ∧ (((((p5 → (p1 ∧ True)) ∧ p4) ∧ (p4 → True)) → p4) ∨ p4))) → p3) ∨ p1)) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h3.left
  let h7 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h9 =>
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h10 =>
      -- One of the premise coincides with the conclusion.
      exact h8
  case inr h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h12 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h13 : p4 := by
        -- One of the premise coincides with the conclusion.
        exact h11
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h14 := h4 h13
      -- False on the left can always be used.
      apply False.elim h14
    case inr h15 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h16 : p4 := by
        -- One of the premise coincides with the conclusion.
        exact h15
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h17 := h4 h16
      -- False on the left can always be used.
      apply False.elim h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_780528188176062766653965185882 : (((p2 ∨ ((((p5 ∨ p4) ∨ (((False → p5) ∧ (p5 ∨ p4)) ∧ p1)) ∧ False) ∨ (p2 ∨ (((p3 ∨ p4) → p3) ∨ ((p4 ∧ p5) ∨ True))))) ∨ p3) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350155740508950359325871941859 : (p4 → (((p3 ∨ (((p1 ∧ (False → (p4 ∨ p1))) ∨ p5) ∨ True)) → (((p2 ∨ (p3 ∨ True)) ∨ (p1 → (False ∨ False))) ∨ (p4 ∧ p3))) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h1
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Conjunctions on the left can always be decomposed.
        let h7 := h6.left
        let h8 := h6.right
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
      case inr h9 =>
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
    case inr h10 =>
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
theorem thm_5_vars_701644958687551044599210462 : (((False ∨ ((p2 → p4) → ((p2 → p1) ∨ (p5 → p5)))) ∧ (((p5 ∨ ((False ∨ False) ∨ True)) ∨ (p4 ∨ (p4 ∧ p4))) ∧ True)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2
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
theorem thm_5_vars_319276770703827620451564620419 : (p4 ∨ (((True ∧ (p4 ∧ (p5 ∨ (True ∧ False)))) ∧ (p5 ∨ ((p3 ∧ (p1 → p1)) ∧ p2))) ∨ (False → (p3 ∧ (((p5 ∧ p4) ∨ p2) ∧ False))))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61041463447368515897550533965 : ((False ∧ (((p2 → False) ∧ (((p1 ∧ True) ∨ p2) → (False ∧ ((((p1 → p1) ∧ (p1 ∨ p5)) ∧ (p5 → True)) → p2)))) ∨ (True → False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356747400290222850900237465317 : (p5 → ((p1 → (p5 ∧ (True ∧ (p3 → False)))) ∨ ((((p4 ∧ ((True ∧ p3) → p1)) ∧ (p3 ∧ (p4 ∧ p3))) ∧ ((True ∧ False) ∧ True)) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260699662542065837356979999657 : ((p3 → p3) → (p5 → ((p3 ∨ (p2 ∨ p5)) → ((((False → ((p4 → (p5 → (False → (p3 → False)))) ∧ p5)) → p3) → (p1 ∨ p3)) ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41074493080825015848240662738 : ((((False → (p3 → (((((p3 → p4) → True) → p2) → (True → (p1 → ((True → p2) ∨ p2)))) ∧ (True ∧ p2)))) → (True ∧ False)) ∨ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256057594303319872686402106664 : ((True ∨ p4) → (((p4 ∨ p1) ∨ ((p5 ∧ p3) ∧ p2)) ∨ (False → ((p4 ∨ (p5 ∧ p1)) → ((True ∧ (p2 ∨ p3)) ∨ (p5 ∨ (False → False))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- False on the left can always be used.
      apply False.elim h3
    case inr h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- False on the left can always be used.
      apply False.elim h3
  case inr h9 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115259442812077972126991185824 : ((((p5 ∧ p1) ∧ (p1 ∨ (True ∨ (p5 ∧ (False → False))))) ∨ ((((p1 ∧ ((False ∨ p2) → p1)) ∧ False) ∧ (p3 → p1)) ∨ True)) ∨ (p2 ∨ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301558231284610175086964178916 : (False ∨ ((p4 ∧ (False ∧ True)) ∨ ((p1 ∧ (p2 → ((p1 ∧ True) ∧ (p1 → (p1 ∨ ((p1 ∨ (False → (p2 ∨ (p2 ∨ False)))) → p3)))))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_657312779702865395004938969241 : (((((p4 ∧ p5) ∧ ((((True ∧ p3) → (False → ((p5 ∨ p4) ∨ True))) → (True → ((p4 → (False ∧ p2)) → p5))) ∧ False)) ∨ (p1 ∧ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_8824303704731989703905616584 : (((((p3 → (p4 ∧ ((p3 ∨ p4) ∨ ((p4 ∧ (p2 ∨ p5)) ∧ False)))) ∧ ((p2 ∧ p4) ∧ (p2 ∧ p1))) → ((p4 ∨ p2) ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_761996054137704096527609303980 : (((p3 ∧ ((p4 ∧ ((((True ∧ p1) ∨ ((p5 ∨ (False → p2)) → p2)) → p3) → ((p4 → False) ∨ (((p5 ∨ True) ∨ p4) → p3)))) → p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135241346570911488534631928319 : (((((p4 ∨ False) ∨ p2) → (False ∧ ((p3 → ((False ∨ p1) ∧ ((p4 → True) ∨ True))) → (True → p3)))) → (False ∨ False)) ∨ ((True ∧ False) → p3)) := by
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
theorem thm_5_vars_356720047637196419918862792748 : (p5 → (((p1 ∧ ((p3 ∧ p2) ∨ p3)) ∨ p2) ∨ (p2 → (p2 → (((p3 ∧ p4) ∨ (((p1 → True) ∨ (False ∨ (p2 ∧ p2))) → p5)) → p5))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h8 =>
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41274316378225696404374386452 : ((((((p4 → ((p5 ∨ p3) ∧ (p3 ∨ p3))) ∧ (p5 ∨ ((True ∨ (False ∨ p1)) → p3))) ∧ p2) → (p1 ∨ ((p1 ∧ p3) ∨ p2))) ∨ False) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  cases h5
  case inl h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147397734384615955759733118985 : ((((((p1 ∨ False) ∧ True) ∨ (p1 ∨ False)) ∧ ((False → p3) ∧ (((p3 ∧ (p4 ∨ p5)) → False) → True))) ∨ p4) ∨ (p5 → ((False ∨ False) → p2))) := by
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
    apply False.elim h3
  case inr h4 =>
    -- False on the left can always be used.
    apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_264458518875713646314976464248 : (True ∧ ((p3 ∨ (p4 ∨ (p5 ∧ p1))) → ((((p3 ∧ p5) → (((True ∨ False) ∧ p5) → False)) ∧ ((False ∧ False) → True)) ∨ ((True → False) → p5)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
      have h9 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h8, we can now drive its conclusion.
      let h10 := h8 h9
      -- False on the left can always be used.
      apply False.elim h10
    case inr h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h14
      -- One of the premise coincides with the conclusion.
      exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58869016123720626198471606874 : (((False ∧ True) ∨ (((True ∨ True) → ((p2 ∨ (p2 ∨ (True → p3))) ∧ False)) → (p5 → ((((p4 ∧ p2) ∧ p4) ∧ p2) ∧ (p2 ∧ True))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_902666446158190763021607519 : ((p4 → ((((p5 ∨ p1) ∨ p4) ∧ ((((p1 ∨ p3) ∧ p2) ∨ (p5 ∧ ((p5 ∧ p1) ∨ True))) ∧ False)) ∨ ((p3 ∨ p2) → True))) ∨ p2) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218808987799122878247270846260 : ((p1 ∧ (p5 ∨ (p2 ∨ p5))) → ((True ∨ ((p2 → p2) ∧ p5)) → ((((((p4 ∨ True) ∨ (p2 ∨ p2)) → p4) ∨ (p1 ∨ p3)) ∧ True) ∧ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h1.left
    let h5 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h4
      case inr h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h4
  case inr h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- Conjunctions on the left can always be decomposed.
    let h13 := h1.left
    let h14 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h14
    case inl h15 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h13
    case inr h16 =>
      -- Disjunctions on the left can always be decomposed.
      cases h16
      case inl h17 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h13
      case inr h18 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h13
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_153305157019009401370978258147 : ((p1 ∨ (((True → True) → (p5 ∨ ((p3 ∧ (p2 → p1)) → p2))) ∧ ((False ∨ (p2 → (p4 ∧ False))) ∨ p2))) → (((p2 ∨ p2) ∨ p4) ∨ True)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- False on the left can always be used.
        apply False.elim h7
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
theorem thm_5_vars_321256867974569878296610757492 : (p4 ∨ (p4 ∨ (((p3 ∧ (p3 ∧ ((p3 ∨ True) ∧ p3))) ∨ False) ∨ (((True ∧ True) ∨ (p3 ∨ (False ∧ p2))) ∨ (((p3 ∨ True) → False) ∧ False))))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219939980024514492910419527650 : ((p4 → (p2 → (p2 → p5))) → ((p1 ∨ (((((p5 ∨ False) → (p4 ∨ p1)) ∧ ((False ∧ (p2 → p5)) ∧ (p5 → False))) ∨ True) ∨ p1)) ∨ p3)) := by
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



