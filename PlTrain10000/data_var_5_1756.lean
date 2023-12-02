variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192398845217711608850010974657 : ((((p2 → ((True ∨ p2) ∧ (False ∨ True))) ∧ p1) ∨ p1) → (((p3 ∨ (p2 ∨ p1)) ∧ ((False ∧ (False ∨ (p2 ∧ False))) ∨ (p2 → p2))) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h6
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_139831268777938017621361865767 : (((p1 → ((False ∨ p1) ∨ (False ∧ ((((((p5 → (p5 ∧ False)) ∧ True) ∨ False) ∧ p4) ∧ (p4 ∧ p2)) → False)))) → p4) → (p2 ∨ (p4 ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p1 → ((False ∨ p1) ∨ (False ∧ ((((((p5 → (p5 ∧ False)) ∧ True) ∨ False) ∧ p4) ∧ (p4 ∧ p2)) → False)))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_924229816301835364800820840730 : ((((True → (False ∧ (((((p3 → p2) ∨ p5) ∨ p1) ∨ p4) ∧ p4))) ∧ ((p2 ∨ (False ∧ (p5 ∧ True))) ∧ (((p4 → True) → p1) ∧ p2))) → p3) ∧ True) := by
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
    let h7 := h5.left
    let h8 := h5.right
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h9 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h10 := h2 h9
    -- We need to get the left conjuct of h10 based on <expert-advice>.
    let h11 := h10.left
    -- False on the left can always be used.
    apply False.elim h11
  case inr h12 =>
    -- Conjunctions on the left can always be decomposed.
    let h13 := h12.left
    let h14 := h12.right
    -- False on the left can always be used.
    apply False.elim h13
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_105986935527216396458389649114 : ((((((p3 ∨ p2) → False) → ((((p2 ∨ p2) ∨ p5) → p3) → p3)) ∨ p1) → (p4 ∨ (p2 → (((p5 ∧ p5) ∨ p4) ∨ p2)))) ∧ (p4 → True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
  -- Implications on the right can always be decomposed.
  intro h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_685761668553512267163613814046 : (((((((False ∨ (p5 → ((p4 → (((p3 ∧ p2) ∧ p2) ∧ p4)) ∧ p4))) → False) ∨ True) → p2) → ((False → False) ∧ ((p3 → p3) → False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263484929466007661935416929000 : (True ∧ ((p3 ∧ ((p1 ∨ (False → (p1 ∧ (p2 → True)))) ∧ (((p2 ∨ False) ∨ (False → p5)) ∧ ((p1 ∨ p4) ∨ p3)))) → ((p2 ∨ True) ∧ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Disjunctions on the left can always be decomposed.
        cases h8
        case inl h11 =>
          -- Disjunctions on the left can always be decomposed.
          cases h11
          case inl h12 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h10
          case inr h13 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h10
        case inr h14 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h10
      case inr h15 =>
        -- False on the left can always be used.
        apply False.elim h15
    case inr h16 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h17 =>
        -- Disjunctions on the left can always be decomposed.
        cases h17
        case inl h18 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h19 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h20 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h21 =>
    -- Conjunctions on the left can always be decomposed.
    let h22 := h5.left
    let h23 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h22
    case inl h24 =>
      -- Disjunctions on the left can always be decomposed.
      cases h24
      case inl h25 =>
        -- Disjunctions on the left can always be decomposed.
        cases h23
        case inl h26 =>
          -- Disjunctions on the left can always be decomposed.
          cases h26
          case inl h27 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h25
          case inr h28 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h25
        case inr h29 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h25
      case inr h30 =>
        -- False on the left can always be used.
        apply False.elim h30
    case inr h31 =>
      -- Disjunctions on the left can always be decomposed.
      cases h23
      case inl h32 =>
        -- Disjunctions on the left can always be decomposed.
        cases h32
        case inl h33 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h34 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h35 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_610468411545970890290087155712 : ((((((p1 ∧ ((p2 → p2) → (((((p5 → (p2 ∧ p3)) ∨ True) ∧ ((p5 ∨ (p1 ∨ p1)) ∨ p3)) → False) ∧ p3))) → p3) → p4) ∨ True) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_611142450991739186619015294147 : ((((((p1 ∨ (p3 ∧ p4)) ∧ (((((p2 → True) ∨ (p5 → p5)) → ((p4 ∨ p4) ∧ p4)) → p2) → ((p4 → p3) ∨ p2))) → False) ∨ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43681182150296021966364383941 : (((((((p3 ∧ p4) → (((p5 ∧ (True ∧ p2)) ∧ p4) ∧ True)) ∨ False) → (p2 ∨ (((p5 ∨ p2) ∧ p5) → (p2 → False)))) → p2) → p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_151259625867037522112406236747 : ((((p4 → p2) → ((p5 ∧ ((p5 ∧ (p1 ∨ p1)) → p1)) → (((p1 → p5) → p4) ∨ (p3 ∨ p4)))) → p3) → (p2 → (p2 ∨ (p5 → p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_82221064352242563313841016516 : ((((((True ∧ p3) → p2) ∧ (((False ∨ (p2 → (((False → p4) ∧ p2) ∧ p2))) ∨ p2) ∨ False)) ∧ p4) ∧ (((p3 ∧ True) → p5) → p1)) → p4) := by
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
    cases h8
    case inl h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- False on the left can always be used.
        apply False.elim h10
      case inr h11 =>
        -- One of the premise coincides with the conclusion.
        exact h5
    case inr h12 =>
      -- One of the premise coincides with the conclusion.
      exact h5
  case inr h13 =>
    -- False on the left can always be used.
    apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148373927795743481382442508543 : (((((p3 ∧ (p1 ∧ ((p1 ∧ p5) ∧ (p5 ∨ p4)))) → (p1 → True)) → p2) ∨ (((p3 ∨ p4) → p5) → False)) ∨ ((p4 → (False → p3)) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_620352088538552036712693671919 : (((((p2 ∨ p3) ∨ ((True → ((p4 ∨ p1) → ((p3 → ((True → p2) → p5)) ∨ (((True → False) → p1) ∨ (p3 → False))))) → p5)) ∨ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310449833397988930317966491903 : (p2 ∨ ((((p5 ∨ (p1 → False)) ∧ p4) ∨ True) ∧ (((p5 ∨ (((p4 → p1) ∨ True) ∨ (True ∨ True))) ∨ (False ∧ (p3 → p2))) ∨ (p2 ∨ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_716899564728902415784264535376 : ((((p2 ∧ ((p5 ∨ True) → p4)) ∧ ((((p1 ∧ ((p5 → p3) ∧ (p2 ∨ (p2 → p2)))) ∧ p1) ∨ (p1 ∨ False)) ∨ (p4 → (p1 ∧ p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43793059415162686671764341592 : ((((p4 ∨ (((p4 → (p2 → p1)) ∨ p2) ∨ (((p3 ∨ ((p1 ∨ p5) → (p1 → (True ∨ p4)))) → (True → p3)) ∧ p1))) → False) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40710202043506875761320584932 : (((((((((p4 ∨ False) ∧ p5) ∧ p4) ∨ p1) ∨ (p4 ∧ p2)) ∨ (((((p5 → (p4 ∨ p2)) ∨ p4) ∨ p4) ∨ p3) → p4)) → p2) ∨ True) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_676579305128777170587867686398 : ((((p1 ∧ (p2 ∨ (((((p4 ∨ True) ∧ p5) ∧ p4) ∧ True) ∨ (p2 ∨ (((p2 ∨ p3) ∧ p1) ∨ p4))))) ∧ ((p1 ∧ False) ∧ (p2 ∧ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147126779670006151696986869797 : ((((p2 ∧ True) → (True ∧ (((p5 ∨ (True ∧ (False → False))) ∧ (p3 → True)) → (True → (False ∨ False))))) ∧ True) ∨ (p2 → (True ∨ (p5 ∨ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_144049129301687485516008734380 : (((p5 ∨ (((p3 → (p3 ∧ False)) ∨ ((p1 ∧ ((p5 → p1) ∧ (p4 ∨ p3))) ∨ True)) ∨ (p4 → p1))) ∨ p5) ∧ ((False ∧ True) → (True ∧ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150777145934125842627906959153 : (((((((p4 → p2) ∧ (False ∨ (p3 → p5))) ∧ p2) → ((p1 → p5) ∨ ((p5 → p4) ∨ p5))) → p2) ∨ p2) → ((p5 ∧ (p4 → p2)) → p2)) := by
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
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h6 : ((((p4 → p2) ∧ (False ∨ (p3 → p5))) ∧ p2) → ((p1 → p5) ∨ ((p5 → p4) ∨ p5))) := by
      -- Implications on the right can always be decomposed.
      intro h7
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Conjunctions on the left can always be decomposed.
      let h10 := h8.left
      let h11 := h8.right
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- False on the left can always be used.
        apply False.elim h12
      case inr h13 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h14
        -- One of the premise coincides with the conclusion.
        exact h3
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h15 := h5 h6
    -- One of the premise coincides with the conclusion.
    exact h15
  case inr h16 =>
    -- One of the premise coincides with the conclusion.
    exact h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_14830926406594808319366894897 : (((((p1 ∨ ((((p5 ∨ p1) → p5) ∨ p2) ∧ True)) ∧ (True ∨ p4)) ∨ (p3 → ((p2 ∧ ((p5 ∧ p3) ∧ p2)) ∨ p3))) ∨ (p4 ∧ p5)) ∧ True) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308501982518179564182733556953 : (p2 ∨ ((((((False ∧ ((p1 → False) → ((p2 → (False ∧ False)) ∨ False))) ∨ (p2 → p1)) ∨ True) ∨ p3) ∨ ((p3 → (p5 → p4)) ∧ p2)) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_135564078653174002882693208489 : (((p5 ∨ (p5 ∨ ((p3 ∧ p4) ∧ (((((True → True) ∧ p1) ∨ p4) → p3) → p4)))) ∧ ((True ∧ p1) → (p2 ∨ p1))) ∨ ((p4 ∨ False) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232091325936459707717876636710 : (((p4 ∨ p5) → p1) → ((((p3 → p3) → p5) ∧ (p3 → (p1 → ((p1 → ((False ∧ (p5 ∨ p4)) ∧ (False ∨ p1))) ∧ (p2 ∨ p1))))) → p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h5 : (p3 → p3) := by
    -- Implications on the right can always be decomposed.
    intro h6
    -- One of the premise coincides with the conclusion.
    exact h6
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h7 := h3 h5
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310038620236115555676571758419 : (p2 ∨ ((False ∧ (p3 → ((p4 ∨ (p3 ∨ ((False ∨ p4) ∨ True))) → ((p4 → True) ∧ p2)))) ∨ (p4 ∨ (p1 ∨ (True ∨ (p4 ∧ (p2 → p4))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_258157437897834818423350086887 : ((p4 ∨ p4) → (((p5 → ((((p3 ∨ False) ∧ ((p5 ∧ True) ∨ p3)) ∨ p2) → (p2 ∨ p1))) ∧ (p2 ∨ (p1 ∨ ((p1 ∨ p5) ∧ p3)))) ∨ True)) := by
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
theorem thm_5_vars_190667797437761112743780337419 : (((False → ((True ∧ p2) → (p1 → (True ∨ True)))) → p1) ∨ (p4 ∨ (p2 ∨ ((False ∧ (((p5 ∨ p4) ∧ ((False → True) → True)) ∧ p3)) ∨ True)))) := by
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
theorem thm_5_vars_51468243156157105531306780797 : ((((((True ∧ True) ∧ ((p4 ∨ p1) ∨ True)) ∨ p5) ∧ ((p2 ∨ False) → (p5 → (p5 → p2)))) → (((False ∨ (True ∧ p3)) ∧ p3) ∨ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_748029371830036782716116747511 : ((((p1 → p1) → (((p4 → ((p1 → ((p3 ∨ False) ∨ (p5 → (p2 ∨ True)))) → (((True → p1) ∨ True) ∧ p1))) ∨ (True → True)) ∨ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213489191349039977950629688828 : (((p2 → (p4 ∧ False)) ∧ p3) ∨ (((False ∧ False) ∨ (((True → p2) → p3) → ((p1 ∨ (p4 → (p4 → True))) ∨ (True ∨ (p1 → p3))))) ∨ False)) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41385858370213771366965561527 : (((((p3 ∧ ((((p1 → (False → p5)) → p2) ∧ p3) ∨ (p2 ∨ p5))) → False) ∧ (True ∨ ((p5 ∨ (p1 ∨ False)) → (p4 ∧ p4)))) ∨ True) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48676573916022276683836153903 : (((((p3 ∨ ((p4 ∨ (p1 ∧ p4)) → (p1 → p4))) ∧ p2) ∨ (((p3 → False) ∧ p5) → ((False → p5) → p1))) ∧ ((p2 ∨ p4) ∨ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197038486801854433998486574986 : ((((False ∧ p5) ∧ ((p3 ∨ False) ∧ False)) ∨ True) ∨ (((True ∨ ((True ∨ p2) → ((p5 ∨ ((p4 → p5) ∧ p5)) ∨ p2))) ∧ (p1 ∧ p2)) → p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61633588348384109580852235256 : ((p1 ∧ ((True → True) → ((p3 → ((((p3 ∧ True) ∧ (p5 → p5)) → (p4 ∨ p5)) → p5)) → ((p2 ∨ ((p2 ∧ True) → p1)) ∨ p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68047651505775820212805359189 : ((p2 → (p5 ∧ ((((p5 → ((True ∨ (p3 ∧ p3)) ∧ (((p2 → False) ∨ (p2 → False)) ∧ p3))) ∨ ((p3 ∨ p3) ∧ True)) ∨ p4) ∧ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_704918457643387665270839402100 : ((((p4 ∨ (((p4 ∨ (p5 → p4)) → p2) ∨ (p3 ∧ p1))) → (((True → p5) ∨ (p2 ∨ (True ∧ p5))) → ((p2 ∨ p2) ∨ (p4 → p4)))) ∨ p1) ∧ True) := by
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
    cases h1
    case inl h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h5
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h8
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
        -- One of the premise coincides with the conclusion.
        exact h12
  case inr h13 =>
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h14 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h15 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h14
      case inr h16 =>
        -- Disjunctions on the left can always be decomposed.
        cases h16
        case inl h17 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h14
        case inr h18 =>
          -- Conjunctions on the left can always be decomposed.
          let h19 := h18.left
          let h20 := h18.right
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h14
    case inr h21 =>
      -- Conjunctions on the left can always be decomposed.
      let h22 := h21.left
      let h23 := h21.right
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h24 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h25
        -- One of the premise coincides with the conclusion.
        exact h25
      case inr h26 =>
        -- Disjunctions on the left can always be decomposed.
        cases h26
        case inl h27 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h28
          -- One of the premise coincides with the conclusion.
          exact h28
        case inr h29 =>
          -- Conjunctions on the left can always be decomposed.
          let h30 := h29.left
          let h31 := h29.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h32
          -- One of the premise coincides with the conclusion.
          exact h32
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206325092570707345908613610866 : ((p1 ∨ (p2 ∨ ((p1 ∨ p3) ∧ p3))) ∨ ((p2 ∨ (((p1 ∨ True) → False) ∧ (False ∨ (p5 ∧ (p2 → ((p3 ∨ p4) ∧ (p5 ∧ p2))))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_797097553319777613013951531082 : (((p1 → (((((True ∨ p4) → p1) → p1) → ((False ∧ (False → True)) ∨ (((p3 → p3) ∨ p2) ∧ (p5 ∧ ((p5 → p1) ∧ True))))) ∧ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_704813249322027515370792260680 : ((((True ∨ ((p5 → True) → ((False ∨ (p5 ∧ p4)) ∨ p3))) → (p2 ∨ ((((p3 ∧ (p1 → p3)) ∨ p2) ∧ (True ∧ p5)) ∨ (p2 ∧ p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49755875622608294318081681415 : (((True ∨ (((((True ∧ ((p5 → p5) → p5)) ∨ ((False → p5) ∨ p5)) → p2) ∨ ((True ∨ p3) ∨ p4)) → p4)) → ((p5 ∨ p5) → p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314545558799567924005037311121 : (p3 ∨ ((((p3 ∨ ((p3 ∨ p5) → (p5 ∧ True))) ∧ (p4 ∨ (p5 ∨ p5))) ∨ (p2 → (p4 ∨ True))) ∨ ((p3 → (p3 → p5)) ∨ (p2 ∨ p5)))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157908101392593311490101101303 : ((((((p3 ∨ False) ∧ True) ∨ p4) ∨ (p1 → (p1 ∧ p3))) → (p3 ∨ (p2 ∨ (p1 ∧ (p5 ∧ True))))) ∨ (p2 → (True ∨ (False ∨ (False → p5))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158168006646813592238197201496 : ((((p2 → (p2 ∨ p5)) ∨ p2) → (p4 ∨ ((p3 ∨ (True → ((p1 ∧ (p5 → p5)) ∧ True))) ∧ p4))) ∨ ((p4 → (p1 ∧ False)) → (p3 → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41550154072625199700025970965 : ((((p1 → ((p5 → True) ∧ (((p3 → p3) → p2) ∨ p5))) ∨ (((p5 → p5) ∧ ((((False ∧ p1) → p5) ∧ p5) ∧ False)) ∨ p3)) ∨ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42534363678247613017464872241 : (((p1 ∨ (((p5 ∧ ((p2 ∧ p1) ∧ ((p2 ∧ p4) ∨ p5))) → ((False ∧ (p4 → (False ∧ (p1 → p3)))) ∧ (True → p5))) → p3)) ∨ True) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37391226839969668874995763690 : ((((((p2 → p3) → (p5 ∧ ((p1 ∨ (p1 ∨ ((p1 → ((p3 → p1) ∧ p3)) ∨ (p2 ∨ p5)))) ∧ (p4 ∨ False)))) → p2) ∨ False) ∧ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206026678137251993428140243787 : ((p2 ∧ ((False ∧ p2) ∧ (p1 ∨ p4))) ∨ (p3 → (p4 → ((False ∧ (p5 ∨ (p1 ∨ (((p3 ∨ (True ∨ p1)) → (p1 ∨ False)) → p3)))) → p3)))) := by
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
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309912941895276552899801815796 : (p2 ∨ ((((((p3 ∧ (p4 ∧ False)) ∨ p2) ∧ p1) ∧ (p5 → ((True → p3) ∧ (p3 ∧ p5)))) ∨ True) ∨ (p5 ∨ (p4 → ((p5 ∧ p4) → p1))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337135919550656517216549473528 : (p1 → ((p2 ∨ (p2 ∨ (p3 ∨ ((((p2 → True) ∧ p3) ∨ True) ∧ ((((p2 ∧ p1) → p1) ∧ ((p1 → False) ∧ p3)) ∧ p1))))) ∨ (p1 → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113699481094361293565598260978 : ((((p4 ∧ (p2 → ((((p1 ∧ True) ∧ True) → (((True ∨ p4) ∨ p5) → ((False → p3) ∨ p5))) ∨ p2))) → p3) → (p5 ∧ True)) ∨ (True ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205174052889541152509271633575 : (((False ∨ (p5 ∧ p5)) ∧ (p4 ∨ p1)) ∨ (True ∨ (True → ((((False ∧ p4) → True) → (True ∨ (p3 ∨ (p5 ∧ ((False ∨ p4) ∧ p3))))) ∧ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_624883897026165275834034137634 : ((((p5 ∨ ((p4 ∧ ((((p5 ∧ p1) ∨ p5) → p1) ∧ p3)) ∧ ((p4 ∧ (p2 ∨ (p3 → (True ∨ (False ∨ True))))) ∧ (True ∨ p2)))) ∨ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248711061339262613027131665798 : ((p3 ∨ p2) ∨ ((True ∧ (p5 ∧ (True ∨ p3))) ∨ (False ∨ (((False ∧ (False → (False ∧ p2))) ∧ (False ∨ True)) ∨ (True ∨ ((True → True) ∨ p5)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_38498088591755447844631179582 : (((((False → (p4 ∨ (p4 ∧ ((p2 → p3) ∨ (p3 → p5))))) → p2) ∨ (((((False → (p3 ∧ p3)) ∨ p2) ∧ True) → p3) ∨ True)) ∧ True) ∨ p4) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230368954821208701616698461854 : (((p3 ∨ False) ∧ True) → (((((p3 → p4) ∧ (p2 → (False → ((p5 ∧ ((p1 ∨ p3) ∨ p1)) → False)))) ∧ p2) → ((False ∧ p5) ∨ p1)) ∨ True)) := by
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
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59658229656750122721075355635 : (((True ∧ True) → (p2 ∨ ((((True ∨ p3) ∧ (p4 ∧ p3)) ∧ p4) → (p4 ∧ ((p2 ∨ (p2 → p5)) → (p1 ∨ ((p4 ∨ False) ∧ True))))))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h8.left
    let h11 := h8.right
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h12 =>
    -- Conjunctions on the left can always be decomposed.
    let h13 := h8.left
    let h14 := h8.right
    -- One of the premise coincides with the conclusion.
    exact h6
  -- Implications on the right can always be decomposed.
  intro h15
  -- Disjunctions on the left can always be decomposed.
  cases h15
  case inl h16 =>
    -- Conjunctions on the left can always be decomposed.
    let h17 := h4.left
    let h18 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h19 := h17.left
    let h20 := h17.right
    -- Disjunctions on the left can always be decomposed.
    cases h19
    case inl h21 =>
      -- Conjunctions on the left can always be decomposed.
      let h22 := h20.left
      let h23 := h20.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h18
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h24 =>
      -- Conjunctions on the left can always be decomposed.
      let h25 := h20.left
      let h26 := h20.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h18
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h27 =>
    -- Conjunctions on the left can always be decomposed.
    let h28 := h4.left
    let h29 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h30 := h28.left
    let h31 := h28.right
    -- Disjunctions on the left can always be decomposed.
    cases h30
    case inl h32 =>
      -- Conjunctions on the left can always be decomposed.
      let h33 := h31.left
      let h34 := h31.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h29
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h35 =>
      -- Conjunctions on the left can always be decomposed.
      let h36 := h31.left
      let h37 := h31.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h29
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_142004240020161439081997086787 : (((False → False) → ((((p3 → ((p1 ∨ p1) ∨ p2)) → (p5 → True)) ∨ (((p3 ∧ p5) → False) ∨ p1)) ∧ (False ∨ False))) → ((p3 ∨ p3) ∧ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (False → False) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- False on the left can always be used.
    apply False.elim h7
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h8 : (False → False) := by
    -- Implications on the right can always be decomposed.
    intro h9
    -- False on the left can always be used.
    apply False.elim h9
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h10 := h1 h8
  -- We need to get the right conjuct of h10 based on <expert-advice>.
  let h11 := h10.right
  -- Disjunctions on the left can always be decomposed.
  cases h11
  case inl h12 =>
    -- False on the left can always be used.
    apply False.elim h12
  case inr h13 =>
    -- False on the left can always be used.
    apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_188562485742920672132694052884 : ((((p2 → (p1 ∨ (False → p4))) ∨ p3) ∧ (p3 ∨ True)) ∧ ((p1 ∨ (False ∨ p5)) ∨ ((p1 ∨ (p1 → (p3 → p4))) → (True ∧ (p5 → p5))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- False on the left can always be used.
  apply False.elim h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h6 =>
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_195818410136235136083503669768 : (((p3 ∨ p3) → ((p4 ∧ p1) → (p4 ∧ p3))) ∧ ((False ∨ ((((p4 ∨ (p5 → (p2 ∨ p5))) → p4) → (False ∧ p1)) ∨ True)) ∧ (True ∨ p5))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h5 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h6 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  -- Conjunctions on the left can always be decomposed.
  let h7 := h2.left
  let h8 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h9 =>
    -- One of the premise coincides with the conclusion.
    exact h9
  case inr h10 =>
    -- One of the premise coincides with the conclusion.
    exact h10
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_654724714614085841524821177057 : (((((((p2 ∧ (p4 ∧ True)) → (p4 ∨ (((((((p4 → p1) ∧ True) ∧ True) ∨ True) → p5) → p3) ∧ p5))) ∨ p2) → p3) ∨ (p2 ∧ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_708473231562914997226911291764 : (((((((False → (p3 → False)) ∨ p1) ∧ False) ∨ True) → ((p2 ∧ (p3 ∧ ((True ∨ (p2 ∧ p3)) ∧ (((p2 → p4) → False) ∧ False)))) ∧ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324072492082713882518462042120 : (p5 ∨ ((((((False ∧ False) → p3) ∧ p2) ∨ (p4 ∨ (p4 ∧ p3))) ∨ p4) ∨ ((True ∨ (p5 ∨ (p4 ∨ p2))) ∨ ((p2 ∧ p3) ∧ (True → p4))))) := by
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
theorem thm_5_vars_34228963245533560962636457216 : ((True → ((((p1 ∨ ((p4 → ((False → p3) → (p2 ∧ (False → p1)))) ∨ False)) ∧ (True → (p5 ∨ True))) → p1) ∨ (p5 → (p5 ∨ p1)))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218513361946969301099748936271 : (((p3 ∨ True) → (False → p5)) → (((p5 → p2) ∨ p5) ∨ ((False ∧ ((True → (p4 ∨ ((p1 ∨ ((p2 → p5) ∧ p5)) ∨ p3))) ∧ True)) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68186904918547912622756288056 : ((p3 → (((((((p1 ∧ (p1 → p5)) ∨ p1) → p1) → False) → (p1 → (True ∨ (p3 ∧ (False → p4))))) → ((p3 → p4) ∧ p3)) ∨ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178707114525822217949125931140 : (((False ∨ ((p3 → p3) ∧ p2)) ∨ ((p4 ∧ p5) → ((p3 ∨ p1) ∧ p3))) ∨ ((False → ((p5 → (False ∧ True)) → p2)) ∨ ((p5 ∧ p4) ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165041214411807447658357802963 : ((((p3 → p2) ∧ (True ∧ ((((((p4 ∧ False) ∨ p2) → p3) ∧ True) ∨ p2) → p1))) → p5) ∨ ((p2 ∧ (((True → p4) → p5) ∧ p5)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_35614555958944947852433493956 : ((p2 → (((p5 ∧ True) ∨ False) → ((p4 ∨ (p4 ∨ (p1 ∧ p3))) ∨ (p2 ∧ ((p2 ∧ (p3 ∨ False)) ∨ ((p4 → p5) ∨ (True ∨ p1))))))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h1
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- False on the left can always be used.
    apply False.elim h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198619974447769343444811624369 : ((p2 ∨ (p3 ∨ (p4 ∧ ((p1 ∨ p2) → False)))) ∨ (((p2 → ((((p1 → p2) ∧ p4) ∨ (p2 ∧ p2)) ∧ (p1 ∨ (p3 → p2)))) → p1) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_983274706850225594994593905298 : (((p1 ∧ ((((False → p4) → (((False → True) ∧ p4) ∨ (p1 ∨ p5))) ∨ True) → (p3 ∧ (((p4 ∧ False) ∨ True) → ((p4 → p3) ∧ False))))) → False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : (((False → p4) → (((False → True) ∧ p4) ∨ (p1 ∨ p5))) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h7 : ((p4 ∧ False) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h8 := h6 h7
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- False on the left can always be used.
  apply False.elim h9
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_701349683336308998827976657342 : (((((p4 ∧ (p2 ∧ (p1 → p1))) ∧ ((False ∧ p2) ∨ p2)) ∧ (p2 → ((((False → ((p1 ∨ (p1 ∨ True)) ∨ p2)) ∨ True) ∧ p3) ∧ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157233149173133497915089926381 : ((((((p2 → (True ∨ p4)) ∧ (p3 ∧ (False ∧ True))) ∧ p3) → ((True ∧ (True ∧ p3)) ∧ p1)) → p2) ∨ (p2 → ((p3 → (p5 ∧ False)) → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66341826636956311027113331343 : ((p5 ∨ (p4 ∧ (((((p4 ∧ p2) → p5) ∨ p2) ∨ (p2 ∨ (p4 ∨ ((p5 ∨ (p1 → (p2 ∧ False))) ∧ (p5 ∨ (False ∧ p4)))))) ∧ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_261619976824384501701065745507 : ((p5 → p5) → ((((p1 ∨ p2) ∨ False) ∨ (p3 ∨ (p5 ∨ ((p5 ∧ ((((p4 ∧ (False ∧ False)) ∨ (True → p5)) ∨ p5) ∨ p3)) ∨ True)))) ∨ p1)) := by
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
theorem thm_5_vars_116774211497723462722113995621 : (((False ∨ p2) ∨ ((((p2 → True) ∧ True) → p2) ∨ ((p4 → (False ∧ p4)) ∨ ((p3 → p1) ∨ (True ∨ (p3 ∧ (p1 ∧ p4))))))) ∨ (p3 → False)) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_640135947760296949503008051074 : ((((((False ∨ p3) ∨ False) → (p4 ∨ (True ∧ ((((False ∨ (((((False ∧ p4) → p4) ∨ p2) ∨ True) ∨ p5)) → p1) ∨ False) ∧ p1)))) → p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213177052202290883677583247061 : ((((False ∨ p4) ∨ p2) ∧ p1) ∨ (((p2 → ((p1 → ((True ∧ p4) ∨ (p4 ∨ (p4 → False)))) ∨ p2)) ∨ p1) ∨ ((False ∧ (p3 ∨ False)) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_195295455067587343920399483566 : ((((True ∨ (p2 → False)) → p4) → (True ∨ p2)) ∧ (p2 → ((p1 ∧ (p3 ∨ (((((p4 ∨ p4) ∧ False) ∨ (p4 → p4)) → p2) → False))) ∨ p2))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342028945845279239702431971425 : (p2 → (((((p1 → p4) → p3) ∧ ((((p1 → (p5 → p1)) ∧ p1) → ((p4 ∧ (True ∧ p4)) ∧ p1)) ∧ p4)) ∧ p2) → (p3 → (p3 ∧ p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h7.left
  let h9 := h7.right
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Conjunctions on the left can always be decomposed.
  let h10 := h2.left
  let h11 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h12 := h10.left
  let h13 := h10.right
  -- Conjunctions on the left can always be decomposed.
  let h14 := h13.left
  let h15 := h13.right
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60015013460672675550149239043 : (((p1 ∨ False) → ((((((p5 → True) ∧ (p4 ∧ True)) ∨ (False ∨ p3)) ∧ ((((p1 ∧ p3) ∧ False) ∧ True) ∧ p1)) ∨ True) ∨ (p1 → p4))) ∨ p3) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- False on the left can always be used.
    apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59968303039295822761005513615 : (((False ∨ True) → ((((True → ((((p1 ∨ (p4 ∧ p2)) ∧ (p2 ∧ True)) → ((p3 ∧ p2) ∨ p4)) ∧ p1)) → (p3 ∧ False)) ∧ True) ∧ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_702657808692296564137879607115 : ((((((p4 ∧ (True ∧ p3)) ∧ (False ∧ p4)) ∧ (p3 → p5)) ∨ ((((p3 ∨ p4) ∧ (p5 ∨ False)) ∨ p3) ∨ (p4 → ((True ∨ True) ∨ p5)))) ∨ False) ∧ True) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_175875437091811181976553023710 : ((((((p1 → False) ∨ p3) ∨ (True ∨ True)) → ((p4 → False) ∨ True)) ∨ False) ∧ ((False ∧ (False ∨ (p1 ∨ (False → (False ∧ (False ∨ p5)))))) → p1)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Implications on the right can always be decomposed.
  intro h8
  -- Conjunctions on the left can always be decomposed.
  let h9 := h8.left
  let h10 := h8.right
  -- False on the left can always be used.
  apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147997461761084847283176038423 : ((((((((True ∨ p1) → p3) ∧ p4) → (p4 ∨ p4)) ∧ (((p3 → True) → p5) → p1)) → p5) ∨ (p5 → False)) ∨ (p4 → (p3 ∨ (p4 → True)))) := by
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
theorem thm_5_vars_148019268456879467170103366173 : ((((((p4 → (p5 ∧ p5)) → False) ∧ (False ∨ p1)) ∧ (p5 → ((p2 ∨ p1) → (p3 ∧ p4)))) ∨ (p5 → True)) ∨ ((p2 → p4) → (p3 → p2))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115302239217301742760944481672 : (((((True ∨ (p3 ∨ p1)) ∨ (p2 ∨ (p5 ∨ p5))) → False) → ((p1 ∨ p4) → ((((p4 ∨ p4) ∧ p4) ∨ False) ∨ (True ∧ False)))) ∨ (False ∧ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h4 : ((True ∨ (p3 ∨ p1)) ∨ (p2 ∨ (p5 ∨ p5))) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h5 := h1 h4
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h6
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248564007513208042322582555857 : ((p3 ∨ False) ∨ ((p3 ∧ (((p1 ∧ False) → (p1 → ((p1 → True) → (((((True ∨ p1) ∧ p3) → p2) ∨ (False ∨ True)) ∨ p5)))) → False)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64363686487696022300609693300 : ((p1 ∨ (((((p5 ∧ ((p2 ∨ p2) → (p2 ∨ False))) → False) ∧ (p2 ∧ p3)) ∧ ((p2 ∨ ((p2 → p4) ∨ p2)) ∧ (p5 ∨ p2))) ∨ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152349485132758472871606622661 : ((((p3 ∧ (True ∨ p4)) ∨ p2) ∨ ((((p1 ∨ p2) ∨ p2) ∧ (p5 ∧ (True → (p2 → p2)))) ∨ (False ∧ p3))) → (p4 → (p1 ∨ (p3 → p3)))) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h8
        -- One of the premise coincides with the conclusion.
        exact h8
      case inr h9 =>
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
      -- One of the premise coincides with the conclusion.
      exact h12
  case inr h13 =>
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h14 =>
      -- Conjunctions on the left can always be decomposed.
      let h15 := h14.left
      let h16 := h14.right
      -- Disjunctions on the left can always be decomposed.
      cases h15
      case inl h17 =>
        -- Disjunctions on the left can always be decomposed.
        cases h17
        case inl h18 =>
          -- Conjunctions on the left can always be decomposed.
          let h19 := h16.left
          let h20 := h16.right
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h18
        case inr h21 =>
          -- Conjunctions on the left can always be decomposed.
          let h22 := h16.left
          let h23 := h16.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h24
          -- One of the premise coincides with the conclusion.
          exact h24
      case inr h25 =>
        -- Conjunctions on the left can always be decomposed.
        let h26 := h16.left
        let h27 := h16.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h28
        -- One of the premise coincides with the conclusion.
        exact h28
    case inr h29 =>
      -- Conjunctions on the left can always be decomposed.
      let h30 := h29.left
      let h31 := h29.right
      -- False on the left can always be used.
      apply False.elim h30



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244070564723065821732444236042 : ((True ∧ p3) ∨ ((p3 ∨ ((p2 ∧ False) ∧ (((False → p2) → ((p1 ∧ p1) → ((p4 → False) ∧ True))) ∨ (p4 ∧ (p1 ∧ (True → p4)))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134737006833795702336597243031 : ((((p3 ∨ True) ∧ (((p2 → ((p4 → p3) ∨ (p3 ∧ (p1 → ((True → p4) ∧ True))))) → p2) ∧ (p4 → p2))) → p3) ∨ (p4 ∨ (p4 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179175895651269367091703041713 : ((p3 ∧ (((p1 ∧ ((p2 ∨ False) ∨ (p5 → (p2 ∨ False)))) → False) ∧ p4)) ∨ (((True ∧ (((p1 ∨ False) ∨ p2) ∨ p2)) ∨ p2) → (p4 ∨ True))) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Disjunctions on the left can always be decomposed.
        cases h6
        case inl h7 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h8 =>
          -- False on the left can always be used.
          apply False.elim h8
      case inr h9 =>
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_628862617148377641658646181017 : (((((p5 → ((((True → (p2 ∧ p2)) ∨ p1) → p1) → ((False → (((p2 ∧ p1) ∨ (p5 ∨ (p3 ∨ False))) ∧ p4)) ∧ p5))) ∧ p2) → p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_655833599808800758551972656828 : (((((((p4 ∨ (p5 ∧ (((p1 ∧ ((True ∧ p5) → p2)) → p1) ∧ (p4 ∧ p5)))) → p5) → p1) → ((p3 → False) → p2)) ∨ (p5 ∧ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_777717170357299289561300592330 : (((p1 ∨ ((p3 ∧ (True ∨ (True ∨ ((True ∧ p5) → p3)))) → (((p4 ∧ p2) ∨ (p5 → False)) ∨ (((True → (True → p3)) ∨ p4) ∨ True)))) ∨ p2) ∧ True) := by
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
  cases h3
  case inl h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50347546361655644856384638852 : ((((((False ∨ p2) ∨ False) ∧ False) ∧ (((False ∨ (p5 → (p4 ∨ p1))) → (p1 ∨ (p5 ∧ False))) ∨ p5)) ∨ (((p1 ∨ True) ∨ True) ∨ p5)) ∨ p3) := by
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
theorem thm_5_vars_38395502986377933935974173844 : (((((p4 ∨ p3) ∨ (p2 ∨ ((p1 ∨ True) ∨ (p4 ∧ ((True ∧ p5) ∨ (p1 → p3)))))) → ((p5 ∨ (p2 ∨ True)) ∧ (p1 ∧ p2))) ∧ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232099525681725923153564441117 : (((p5 ∨ True) → p4) → ((((p3 ∨ (False → ((p5 → p3) → p3))) ∨ p4) → ((p4 → p5) ∨ p5)) ∨ ((((p3 ∨ p4) ∧ p2) ∨ True) → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136698807428003410469618555195 : (((False ∧ p3) ∧ ((p5 ∨ p3) ∨ (True ∧ ((p1 ∧ ((p1 → p4) → p2)) ∧ (p3 ∨ (((p2 ∧ p4) ∨ p1) ∧ p4)))))) ∨ ((p4 ∧ False) → False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h3



