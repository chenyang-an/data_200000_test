variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354055507136310578436981945401 : (p4 → (p4 → (True ∧ ((p2 → p4) ∧ ((((True ∨ p2) → (p3 → (((p5 ∨ (False ∨ False)) ∨ p1) ∨ (p4 ∧ (False ∨ p5))))) ∧ p5) ∨ p4))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_318551303216211716424925155634 : (p4 ∨ (((p4 ∨ ((p3 ∨ (p5 ∧ (p3 ∨ (False → ((((p4 → p4) ∧ p3) ∧ p1) → ((True ∨ p3) → True)))))) ∧ p2)) ∧ p2) ∨ (p3 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_84659030326656312471053192116 : (((((p5 ∧ (((False ∨ p5) → (True ∧ True)) ∧ True)) → (True ∧ p4)) ∧ p5) ∧ ((p3 → p2) → (False → (p5 ∨ ((p5 → p4) ∧ True))))) → p4) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h6 : (p5 ∧ (((False ∨ p5) → (True ∧ True)) ∧ True)) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h5
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h7
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h8 := h4 h6
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- One of the premise coincides with the conclusion.
  exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117472734150213432584129080111 : ((p1 ∧ (p4 ∧ ((((False ∧ (((p3 ∨ p4) ∧ (((p4 → p2) ∧ True) → p4)) ∨ p5)) → p5) ∨ ((p3 ∨ p3) ∧ p5)) → p3))) ∨ (p4 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149681287581516127647204611923 : ((p5 ∧ (((((p3 → (True ∨ p4)) ∨ ((True ∨ p2) → p2)) ∨ (p1 ∨ (p4 ∧ (p5 ∧ p4)))) ∨ p1) → p2)) ∨ ((p4 ∧ (p3 ∨ p4)) → p4)) := by
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
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h5 =>
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171597832921385330054231232348 : (((((p2 → ((p2 ∨ p2) ∨ True)) ∨ p5) ∧ (p5 ∧ ((p3 ∧ p3) ∨ p1))) ∨ p1) ∨ (False → ((p2 → (p4 → ((p2 → p2) ∧ p4))) ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244674858314655339964560105211 : ((p1 ∧ True) ∨ ((((((((p2 ∨ p2) ∧ (True ∨ p4)) ∨ (True ∧ p1)) → (p1 → (False → p5))) ∨ p3) ∨ (p3 → p2)) → (p1 → p4)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319071348115930110487863636723 : (p4 ∨ ((((((p4 ∧ p4) ∨ (((p3 ∨ p2) → (False ∧ p3)) ∧ p3)) ∧ p4) ∨ (p1 ∨ (p4 ∧ p4))) ∧ p1) → (False ∨ (p3 → (p1 ∨ p1))))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
      have h14 : (p3 ∨ p2) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h13
      -- We have shown the premise of h12, we can now drive its conclusion.
      let h15 := h12 h14
      -- We need to get the left conjuct of h15 based on <expert-advice>.
      let h16 := h15.left
      -- False on the left can always be used.
      apply False.elim h16
  case inr h17 =>
    -- Disjunctions on the left can always be decomposed.
    cases h17
    case inl h18 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h19
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h20 =>
      -- Conjunctions on the left can always be decomposed.
      let h21 := h20.left
      let h22 := h20.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h23
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149368047571567812384880881816 : (((False → p4) → (((((((True → p5) ∨ (p2 ∧ True)) → (p2 ∨ (p5 → p4))) ∨ False) ∨ p3) ∨ p1) → p3)) ∨ ((False ∧ (p3 → p2)) → p4)) := by
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
theorem thm_5_vars_779865245775864957919071565963 : (((p2 ∨ ((p1 ∨ ((((p4 ∧ (p1 → p2)) ∨ (p5 → p1)) ∧ (p1 ∧ True)) ∨ (((p2 ∧ p3) ∨ (False ∧ False)) ∨ (p4 → False)))) → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324562953254433197245636660738 : (p5 ∨ ((p2 → ((p4 ∧ p1) ∨ p4)) → ((((False ∨ p4) ∨ ((p1 ∨ ((p2 → p4) ∧ True)) ∧ ((p3 → p3) ∧ (True ∨ p2)))) ∨ p4) ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : p2 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h8 =>
    -- One of the premise coincides with the conclusion.
    exact h8
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h9
  -- One of the premise coincides with the conclusion.
  exact h9
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_733572159233091123387515661224 : ((((p4 ∧ p4) ∧ (False ∨ (((p4 ∨ True) ∧ p4) ∧ ((p4 ∨ (((((p1 → p1) → (False ∧ p2)) ∨ False) ∨ p3) ∨ p1)) ∨ (p2 ∧ p3))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337588359610484657448350049634 : (p1 → (((p4 ∨ ((p1 ∨ p3) ∧ p4)) ∨ (((p4 ∨ (p2 ∨ p5)) ∧ (((p5 → p1) → p1) ∨ True)) ∧ p5)) → ((False ∧ (p4 → p4)) ∨ True))) := by
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
  case inr h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- Conjunctions on the left can always be decomposed.
    let h13 := h11.left
    let h14 := h11.right
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h15 =>
      -- Disjunctions on the left can always be decomposed.
      cases h14
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
    case inr h18 =>
      -- Disjunctions on the left can always be decomposed.
      cases h18
      case inl h19 =>
        -- Disjunctions on the left can always be decomposed.
        cases h14
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
        cases h14
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
theorem thm_5_vars_789589063748285855194154869820 : (((p5 ∨ (((((p1 ∨ p1) ∨ p1) → p5) ∧ (False ∧ p1)) ∨ (p3 ∨ (((p5 → (False → (p5 ∨ (p5 ∧ p2)))) → True) ∨ (p5 ∧ p3))))) ∨ p5) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114730005343035618166643345074 : (((((p5 ∧ (p4 ∨ p2)) ∧ (False → (p2 → p5))) → (p4 ∨ (True ∧ (p4 ∧ p3)))) → (False ∨ (p3 ∧ (p3 ∧ (p2 ∧ p3))))) ∨ (True ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161381040967179049697948540496 : ((p1 ∧ ((((False → p1) ∧ (p5 ∨ (True ∧ p3))) ∧ (((p1 ∨ (p2 ∧ p2)) ∨ p5) ∨ p3)) ∨ p3)) → ((p4 → True) ∧ ((p3 ∨ p2) ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h6.left
    let h9 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h11 =>
        -- Disjunctions on the left can always be decomposed.
        cases h11
        case inl h12 =>
          -- Disjunctions on the left can always be decomposed.
          cases h12
          case inl h13 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h10
          case inr h14 =>
            -- Conjunctions on the left can always be decomposed.
            let h15 := h14.left
            let h16 := h14.right
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h10
        case inr h17 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h17
      case inr h18 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h10
    case inr h19 =>
      -- Conjunctions on the left can always be decomposed.
      let h20 := h19.left
      let h21 := h19.right
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h22 =>
        -- Disjunctions on the left can always be decomposed.
        cases h22
        case inl h23 =>
          -- Disjunctions on the left can always be decomposed.
          cases h23
          case inl h24 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h21
          case inr h25 =>
            -- Conjunctions on the left can always be decomposed.
            let h26 := h25.left
            let h27 := h25.right
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h21
        case inr h28 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h28
      case inr h29 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h29
  case inr h30 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h30



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54055005382569787151507603148 : ((((((p5 ∨ p4) ∧ p3) → False) → ((True ∧ p3) ∨ p5)) → (((p1 → p3) → False) ∧ ((True ∧ (True → (p2 → (True → p1)))) ∨ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_636285847529123175861110487651 : (((((((p1 ∨ p2) ∧ ((p3 → (((p5 ∨ False) ∨ False) → p1)) ∧ (p3 ∧ p3))) ∧ p4) → (((p2 ∨ p5) → False) ∨ (True ∧ p5))) → p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43458674047650783278065115729 : (((((p4 ∧ p1) ∨ ((p2 ∧ p3) ∨ ((p1 ∧ (p4 ∨ ((p2 ∨ ((True → (True ∨ p4)) → True)) ∧ p3))) → (True ∨ p3)))) ∨ p5) → p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_122985223311869099648471487364 : (((((p1 ∧ p5) ∨ ((p5 ∨ (((p2 → p3) → True) ∨ True)) → p4)) ∨ (((False ∨ p5) ∨ p2) → False)) ∨ ((p3 → p3) ∧ p5)) → (p4 ∨ True)) := by
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
        -- Conjunctions on the left can always be decomposed.
        let h5 := h4.left
        let h6 := h4.right
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_792037850702918379997266734548 : (((True → ((p1 → (p5 → ((((True ∨ p2) → p5) ∧ (((p2 ∧ p3) ∧ (p5 → p4)) ∨ (p4 ∧ (p2 ∨ p3)))) → p2))) → (p4 ∨ True))) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50403280938140627927635481770 : (((True ∧ ((((p1 → (p3 ∨ (p4 ∧ p4))) ∨ ((p4 ∧ (False → (p5 ∧ p5))) → p1)) → p2) → p3)) ∨ ((p4 ∨ p4) ∨ (False → p1))) ∨ p3) := by
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
theorem thm_5_vars_213605565522909090178370909298 : ((((p5 → p1) ∧ p5) ∨ p4) ∨ (((((((p4 ∨ (True ∨ (p1 ∨ p2))) ∧ True) → False) → p4) ∨ (True ∧ True)) ∧ p5) ∨ (p3 → (p3 ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_691707942096858726787422097976 : ((((False ∨ ((p3 ∨ ((False → (True → ((True ∧ False) ∨ False))) ∧ p4)) → (p1 → p2))) → ((((True → p3) ∨ False) ∨ True) ∧ (False → False))) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- False on the left can always be used.
    apply False.elim h2
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- Implications on the right can always be decomposed.
  intro h4
  -- False on the left can always be used.
  apply False.elim h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190882390664800106649827250178 : ((((p4 ∨ p2) ∨ (p2 → (p2 ∧ p2))) → (p5 → False)) ∨ (((p4 → p1) → ((((p3 ∧ (p1 ∧ p2)) ∧ p5) ∧ False) ∨ False)) → (p1 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_353492207399472463207937085279 : (p4 → (p2 ∨ ((p5 ∨ (((p3 ∧ ((p4 → p1) ∧ p3)) ∧ (p5 ∨ False)) ∨ (p3 → (p1 ∨ False)))) → (((p3 ∧ (p3 ∨ p4)) → False) ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Conjunctions on the left can always be decomposed.
      let h8 := h6.left
      let h9 := h6.right
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h13 =>
        -- False on the left can always be used.
        apply False.elim h13
    case inr h14 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55560265527969007351204168958 : (((p4 ∧ ((True → (True ∧ True)) ∨ True)) → (p3 ∨ (((p1 → (p1 → True)) ∨ (True ∧ (p2 ∧ (False ∨ ((p4 ∨ p3) ∨ p5))))) → p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114190518534091911361963609341 : ((((p1 ∧ ((((True ∨ True) → p2) → ((p2 ∨ p3) ∨ p4)) → p1)) → ((p1 → (p3 → p1)) ∨ p3)) → (True ∧ (p4 → p5))) ∨ (p2 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48259163928601459509848369211 : (((p2 ∧ ((((p3 → (True → ((p1 → (p1 ∧ False)) ∧ True))) → False) → (p4 ∨ p5)) ∧ ((False ∧ False) ∨ (False → True)))) → (False ∧ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192802478634665149147051424903 : (((p5 ∨ ((p5 ∨ (p5 → p5)) → (False ∨ p1))) → False) → (True ∧ ((((p1 ∧ ((p5 ∨ p1) ∨ False)) ∨ p1) ∨ (p1 ∨ (p3 ∧ p5))) → p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
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
        -- Disjunctions on the left can always be decomposed.
        cases h7
        case inl h8 =>
          -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
          have h9 : (p5 ∨ ((p5 ∨ (p5 → p5)) → (False ∨ p1))) := by
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h8
          -- We have shown the premise of h1, we can now drive its conclusion.
          let h10 := h1 h9
          -- False on the left can always be used.
          apply False.elim h10
        case inr h11 =>
          -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
          have h12 : (p5 ∨ ((p5 ∨ (p5 → p5)) → (False ∨ p1))) := by
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h13
            -- Disjunctions on the left can always be decomposed.
            cases h13
            case inl h14 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- One of the premise coincides with the conclusion.
              exact h11
            case inr h15 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- One of the premise coincides with the conclusion.
              exact h11
          -- We have shown the premise of h1, we can now drive its conclusion.
          let h16 := h1 h12
          -- False on the left can always be used.
          apply False.elim h16
      case inr h17 =>
        -- False on the left can always be used.
        apply False.elim h17
    case inr h18 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h19 : (p5 ∨ ((p5 ∨ (p5 → p5)) → (False ∨ p1))) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h20
        -- Disjunctions on the left can always be decomposed.
        cases h20
        case inl h21 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h18
        case inr h22 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h18
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h23 := h1 h19
      -- False on the left can always be used.
      apply False.elim h23
  case inr h24 =>
    -- Disjunctions on the left can always be decomposed.
    cases h24
    case inl h25 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h26 : (p5 ∨ ((p5 ∨ (p5 → p5)) → (False ∨ p1))) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h27
        -- Disjunctions on the left can always be decomposed.
        cases h27
        case inl h28 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h25
        case inr h29 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h25
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h30 := h1 h26
      -- False on the left can always be used.
      apply False.elim h30
    case inr h31 =>
      -- Conjunctions on the left can always be decomposed.
      let h32 := h31.left
      let h33 := h31.right
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h34 : (p5 ∨ ((p5 ∨ (p5 → p5)) → (False ∨ p1))) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h33
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h35 := h1 h34
      -- False on the left can always be used.
      apply False.elim h35



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57528992542004305713762685895 : (((p5 → (p4 ∧ False)) ∨ ((((((False ∧ p3) ∨ (p2 ∧ p2)) → (True ∨ ((False ∨ (p4 ∧ p2)) ∧ p2))) → p1) → (p1 ∨ False)) → p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133589789854969545988090114341 : ((((False ∨ ((((False → p3) ∨ p2) ∧ p4) ∨ ((p5 ∧ p2) ∨ ((True ∨ True) ∧ ((False → p3) ∨ p2))))) ∨ False) ∧ p2) ∨ ((p3 ∨ p5) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_182641544402686707243407567028 : (((((True ∧ (p3 ∨ True)) → p1) ∧ p1) → ((p5 ∧ p4) ∨ True)) ∧ (((True → False) ∧ True) → (p5 ∨ ((p5 → ((p5 ∧ p4) ∨ False)) ∧ p4)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h7 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h8 := h5 h7
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47492589277373568576684534853 : (((False ∨ (p2 ∨ ((p1 ∧ p4) ∧ ((True ∧ ((((p2 ∨ (p4 ∧ p2)) → (True ∨ p5)) ∧ (p4 ∧ p1)) ∨ p3)) ∧ False)))) ∨ (p1 ∨ True)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115483477617882069618800310067 : ((((((p1 ∨ True) ∨ (p2 ∨ p5)) ∨ p4) ∧ p5) → ((p4 ∨ ((((True → False) ∨ True) ∨ ((p3 ∧ True) ∧ p3)) ∨ p4)) → p3)) ∨ (p4 → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40465992305098078017257589394 : ((((((False → p1) ∧ p5) ∨ (p3 → (((((p1 ∧ ((p1 ∨ True) ∨ p5)) ∨ (p3 ∨ p4)) ∧ p1) ∨ (p2 ∧ p4)) ∨ p4))) ∨ False) ∨ True) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308369443024429116264132736945 : (p2 ∨ ((((p3 ∧ (p4 ∧ (((p2 ∧ (p2 → True)) → (True ∧ (p2 ∧ p2))) → (((p3 ∧ (p3 → False)) ∨ p2) ∧ p5)))) ∧ False) ∨ True) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256822530959715468392840188263 : ((p1 ∨ p3) → (((True ∨ True) ∧ (p1 ∧ (p3 → (True → ((p5 → p5) → (((p2 → ((p5 → True) → (True ∧ p1))) → p5) → p1)))))) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h2
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- Implications on the right can always be decomposed.
    intro h6
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50446157249472830413835770251 : (((p1 ∨ (p2 ∨ ((((((p2 ∨ p1) → (True → p4)) ∧ (p1 → True)) → False) → False) ∨ (p4 → p5)))) ∨ (False ∨ (p4 ∧ (p5 → p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172945222480329583587851225355 : ((p3 ∧ ((True → p4) → (((False → (p3 ∧ (p5 ∨ p2))) ∧ p4) → (True ∧ p5)))) ∨ (False → (p3 ∨ ((p5 → p3) ∨ (False ∨ (p2 → p5)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156836489033941570386391101691 : (((p1 → ((((p5 ∧ p5) → True) → (p4 ∧ (p2 ∧ (True → True)))) ∧ ((False ∨ p2) → p5))) ∧ p4) ∨ (True → (p4 → (p4 → (p1 ∨ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_264583261091464829663620242737 : (True ∧ ((p3 ∨ (True ∧ p2)) ∨ (((((p5 → False) ∨ p4) → p3) ∧ (True → p3)) ∨ ((p3 ∨ (p2 ∨ ((False → p5) ∨ p5))) ∨ (p5 ∨ True))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_189179884026414456051128848029 : (((p1 ∧ True) ∨ ((((True ∧ p5) ∧ False) ∧ p5) → p4)) ∧ (((((False → p3) ∧ (p2 → p2)) → p5) ∨ ((True → False) ∧ (p5 → True))) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  apply False.elim h5
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56689973465602241244564323701 : ((((True ∧ p1) ∨ p2) ∧ (((False ∧ (p1 ∨ True)) ∨ p5) ∧ ((p2 → (p3 → p5)) ∨ (p3 ∧ (((False ∧ (p1 ∧ p1)) → p1) ∨ p5))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_122684553874308025810949307806 : (((((p5 ∧ (p2 ∨ p3)) ∧ ((p2 ∨ False) ∨ p5)) ∨ (((((False ∧ True) ∨ False) → p1) ∧ p1) → (p1 → p4))) → (p3 ∧ False)) → (p4 → p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : (((p5 ∧ (p2 ∨ p3)) ∧ ((p2 ∨ False) ∨ p5)) ∨ (((((False ∧ True) ∨ False) → p1) ∧ p1) → (p1 → p4))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h8 := h1 h3
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- False on the left can always be used.
  apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_131304502316268956764442916085 : ((((((p3 ∨ p1) ∧ False) → p5) ∨ True) → ((p4 ∧ (p3 ∧ ((p5 ∧ True) ∨ (p5 ∨ False)))) ∨ ((False → p1) → True))) ∧ (p5 → (p5 ∨ p4))) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro
  -- Implications on the right can always be decomposed.
  intro h6
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_695904206476347544032158647839 : (((((p1 → p4) ∨ (p1 → ((p4 ∨ ((True → (p1 ∧ False)) ∨ True)) ∧ p3))) → ((p2 → False) → (((p1 → p5) ∨ p1) ∨ (p5 → True)))) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307725846514503292979474362044 : (p1 ∨ (p3 → (((((p5 ∧ True) ∨ p3) ∧ ((((p3 ∨ ((((p4 ∧ False) → p4) ∨ (p5 → p3)) → p5)) → p1) ∧ p1) ∧ True)) ∧ True) ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_327035230622191560778466305455 : (True → ((((p5 ∨ ((((p1 → p1) ∧ p3) ∨ p4) ∨ p1)) ∧ p1) ∨ (False → ((p3 ∨ (True → True)) ∨ (True ∧ ((True → p3) ∧ p4))))) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245422970991409739687117080399 : ((p2 ∧ p4) ∨ (((p1 ∧ (((p3 → (p2 ∨ p3)) ∧ p5) ∨ (p2 ∧ p4))) ∨ ((p2 → p2) ∨ True)) ∨ (p4 → (((p5 → p4) ∨ False) ∨ p3)))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138060302961070707970799358354 : ((True → (p5 ∧ (p3 → (p5 ∧ (((p2 ∧ (p1 ∧ (p4 → False))) ∨ (p3 → ((p1 ∨ (p5 → p2)) → p5))) → p5))))) ∨ ((p2 ∧ p1) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_730892317466960317497953460385 : ((((True ∨ (p1 ∧ True)) → ((((p2 → (p4 ∧ p3)) ∧ (((p5 ∧ p1) ∨ True) ∧ (p2 ∨ p5))) ∨ p5) ∨ ((True ∧ True) ∨ (p5 ∧ p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259565505579874005314355779027 : ((p1 → True) → (((p2 ∨ (p5 → p1)) ∨ (p5 → ((p3 ∧ (False ∧ True)) ∨ ((p3 ∧ (False ∧ ((p2 ∨ False) → p5))) → p4)))) ∨ (p5 ∧ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244795742198167069254059355711 : ((p1 ∧ p1) ∨ (((((p5 ∨ (p4 → False)) ∨ p5) ∧ ((True ∨ ((p4 → p2) → (p5 → ((p3 → p3) ∨ (p1 ∨ p4))))) → p3)) → p1) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_125639240587276205336989565892 : (((p1 ∧ p5) ∨ ((((False → (((p3 → p5) → p3) ∨ (p5 ∧ p5))) → p1) ∧ ((p5 → p1) → (p5 ∧ (p1 → p3)))) ∧ p4)) → (False ∨ p5)) := by
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
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h6.left
    let h9 := h6.right
    -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
    have h10 : (p5 → p1) := by
      -- Implications on the right can always be decomposed.
      intro h11
      -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
      have h12 : (False → (((p3 → p5) → p3) ∨ (p5 ∧ p5))) := by
        -- Implications on the right can always be decomposed.
        intro h13
        -- False on the left can always be used.
        apply False.elim h13
      -- We have shown the premise of h8, we can now drive its conclusion.
      let h14 := h8 h12
      -- One of the premise coincides with the conclusion.
      exact h14
    -- We have shown the premise of h9, we can now drive its conclusion.
    let h15 := h9 h10
    -- We need to get the left conjuct of h15 based on <expert-advice>.
    let h16 := h15.left
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321262503671150986756469447071 : (p4 ∨ (p4 ∨ ((False ∧ (p3 ∧ p4)) ∨ (((((p2 ∨ (((p3 ∧ p1) → p4) ∨ p2)) → True) ∨ False) ∨ ((False ∨ p1) ∧ p1)) ∨ (p4 → p1))))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199386835061356571359166848815 : ((((p2 ∧ (p3 ∧ p5)) → (p2 ∨ True)) ∨ p5) → ((((((p5 ∨ p3) ∨ True) ∧ p5) ∨ (p2 ∨ p3)) ∧ (False ∨ (True → (p2 ∧ p3)))) → p3)) := by
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
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Disjunctions on the left can always be decomposed.
        cases h4
        case inl h10 =>
          -- False on the left can always be used.
          apply False.elim h10
        case inr h11 =>
          -- Disjunctions on the left can always be decomposed.
          cases h1
          case inl h12 =>
            -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
            have h13 : True := by
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h11, we can now drive its conclusion.
            let h14 := h11 h13
            -- We need to get the right conjuct of h14 based on <expert-advice>.
            let h15 := h14.right
            -- One of the premise coincides with the conclusion.
            exact h15
          case inr h16 =>
            -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
            have h17 : True := by
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h11, we can now drive its conclusion.
            let h18 := h11 h17
            -- We need to get the right conjuct of h18 based on <expert-advice>.
            let h19 := h18.right
            -- One of the premise coincides with the conclusion.
            exact h19
      case inr h20 =>
        -- Disjunctions on the left can always be decomposed.
        cases h4
        case inl h21 =>
          -- False on the left can always be used.
          apply False.elim h21
        case inr h22 =>
          -- Disjunctions on the left can always be decomposed.
          cases h1
          case inl h23 =>
            -- One of the premise coincides with the conclusion.
            exact h20
          case inr h24 =>
            -- One of the premise coincides with the conclusion.
            exact h20
    case inr h25 =>
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h26 =>
        -- False on the left can always be used.
        apply False.elim h26
      case inr h27 =>
        -- Disjunctions on the left can always be decomposed.
        cases h1
        case inl h28 =>
          -- We want to use the implication h27 based on <expert-advice>. So we show its premise.
          have h29 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h27, we can now drive its conclusion.
          let h30 := h27 h29
          -- We need to get the right conjuct of h30 based on <expert-advice>.
          let h31 := h30.right
          -- One of the premise coincides with the conclusion.
          exact h31
        case inr h32 =>
          -- We want to use the implication h27 based on <expert-advice>. So we show its premise.
          have h33 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h27, we can now drive its conclusion.
          let h34 := h27 h33
          -- We need to get the right conjuct of h34 based on <expert-advice>.
          let h35 := h34.right
          -- One of the premise coincides with the conclusion.
          exact h35
  case inr h36 =>
    -- Disjunctions on the left can always be decomposed.
    cases h36
    case inl h37 =>
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h38 =>
        -- False on the left can always be used.
        apply False.elim h38
      case inr h39 =>
        -- Disjunctions on the left can always be decomposed.
        cases h1
        case inl h40 =>
          -- We want to use the implication h39 based on <expert-advice>. So we show its premise.
          have h41 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h39, we can now drive its conclusion.
          let h42 := h39 h41
          -- We need to get the right conjuct of h42 based on <expert-advice>.
          let h43 := h42.right
          -- One of the premise coincides with the conclusion.
          exact h43
        case inr h44 =>
          -- We want to use the implication h39 based on <expert-advice>. So we show its premise.
          have h45 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h39, we can now drive its conclusion.
          let h46 := h39 h45
          -- We need to get the right conjuct of h46 based on <expert-advice>.
          let h47 := h46.right
          -- One of the premise coincides with the conclusion.
          exact h47
    case inr h48 =>
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h49 =>
        -- False on the left can always be used.
        apply False.elim h49
      case inr h50 =>
        -- Disjunctions on the left can always be decomposed.
        cases h1
        case inl h51 =>
          -- One of the premise coincides with the conclusion.
          exact h48
        case inr h52 =>
          -- One of the premise coincides with the conclusion.
          exact h48



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64648342519959938243443846165 : ((p1 ∨ (p5 ∧ (((((((p1 ∨ (p1 ∧ p5)) ∨ p1) ∧ p1) ∨ (p3 → p5)) ∨ ((p2 ∧ p1) ∧ p3)) ∨ (False ∨ p4)) ∧ (False → True)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198439868485024999734416662268 : ((p5 ∧ ((((p1 → False) → p3) ∨ p2) ∧ p1)) ∨ (p3 → ((((p3 ∨ p5) ∧ False) ∨ True) ∨ (p3 ∧ (((False → p3) ∧ p5) ∧ (p2 → p1)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57237709209797485608474763584 : ((((p1 ∧ p2) → False) ∨ ((((p4 ∨ (True → False)) → (p1 ∨ p3)) ∨ ((((p3 ∨ p5) ∨ p2) → (p3 → (p2 ∨ False))) ∧ False)) ∨ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351682815570363699316093721798 : (p4 → ((p3 ∨ ((p3 ∨ ((((p2 ∧ False) → p2) ∨ p1) → p3)) → ((p5 → False) → p3))) → ((False → p2) → (p5 → ((p4 → p2) → p2))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h6 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h7 : p4 := by
      -- One of the premise coincides with the conclusion.
      exact h1
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h8 := h5 h7
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h10 : p4 := by
      -- One of the premise coincides with the conclusion.
      exact h1
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h11 := h5 h10
    -- One of the premise coincides with the conclusion.
    exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_142385797331353383405620107570 : ((p4 ∧ ((((True → True) ∨ ((True ∧ (((True ∧ p5) → (p3 → p1)) → p4)) ∨ (p5 ∧ True))) → (True ∧ False)) → p1)) → ((True → p1) → p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h5 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h5
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135648257398110500660761224657 : (((((((True → True) → p1) ∨ p5) ∨ (True ∨ True)) ∨ ((True ∨ (p2 → True)) → True)) → (((True ∧ p5) ∨ p3) ∨ True)) ∨ ((p3 ∨ p2) → p2)) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h3
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
    case inr h6 =>
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
theorem thm_5_vars_234092860505972729994773440827 : ((True → (p4 ∧ False)) → (p3 ∨ ((((p5 ∧ p5) ∧ p1) ∧ False) ∨ ((p1 → ((p3 → ((p2 ∧ p1) ∨ ((p1 ∧ True) ∧ p5))) ∧ p5)) ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_103174607175659757972671888689 : ((((p4 ∧ p4) → (p4 → (((((((p4 → True) ∨ (True ∨ p2)) ∧ p4) → True) ∧ (p3 → True)) → p1) ∨ (False ∨ True)))) ∨ True) ∧ (p3 → True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_151648470551301272567105314427 : ((((False ∧ ((p4 ∧ (p2 ∨ (p1 ∧ False))) → ((p5 ∨ p3) ∧ (True ∧ False)))) → p2) ∧ (p2 ∨ (p4 ∨ True))) → (((p2 ∧ p5) ∨ True) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
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
theorem thm_5_vars_123393220178979417566275923578 : ((((p1 ∨ (False → ((p3 → p1) → (p2 ∧ (False ∧ (p5 → ((p4 ∨ p3) ∨ p1))))))) ∨ p5) → (((p2 ∨ p1) → False) ∧ p5)) → (p5 ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p1 ∨ (False → ((p3 → p1) → (p2 ∧ (False ∧ (p5 → ((p4 ∨ p3) ∨ p1))))))) ∨ p5) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- False on the left can always be used.
    apply False.elim h3
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- False on the left can always be used.
    apply False.elim h3
    -- Implications on the right can always be decomposed.
    intro h5
    -- False on the left can always be used.
    apply False.elim h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h2
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61375132918127439102434391285 : ((p1 ∧ ((((p2 ∧ ((p4 ∨ ((True ∨ True) ∧ p5)) ∨ p4)) ∨ ((((p5 ∧ p2) ∨ (p5 ∧ False)) → p1) ∧ (True ∧ True))) ∨ False) ∨ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171496566409922401510160740408 : (((p4 → ((p1 ∨ ((p3 → (True → (p1 ∧ (p1 → p1)))) → False)) ∧ p2)) ∧ p5) ∨ (((p2 → p1) → (p2 ∨ False)) → ((p5 → True) ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_252956787087674196125238930080 : ((True ∧ p2) → (((p5 → p5) → (p5 ∨ (p3 ∨ (False ∧ (p5 ∧ (p3 ∧ p5)))))) → (False ∨ (p5 → (((p4 → p1) → (p1 ∧ p1)) ∨ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h5
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111714823798790467067157975940 : (((((((True ∧ p2) → (((p4 → False) ∨ p5) ∧ p1)) → p1) → ((p4 ∨ False) ∨ ((p2 → (p1 ∨ p5)) ∨ p5))) → p5) ∨ False) ∨ (True ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148415030001762496544495565791 : ((((p1 ∧ ((p1 ∧ p1) ∧ ((False ∧ ((False ∧ True) ∧ p5)) ∨ p3))) → p2) → ((p5 → (p3 ∨ p5)) → p4)) ∨ (((False ∨ p1) ∧ False) → p1)) := by
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
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61889690568483027022660216427 : ((p2 ∧ (((((p4 → True) ∨ True) → ((p1 → (p2 → False)) ∨ False)) ∧ (True ∨ ((p2 ∧ (True → True)) ∧ (False → p1)))) ∨ (p3 ∧ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51623312402858565941091161992 : ((((True ∧ ((((True ∨ ((True ∨ True) ∨ (p1 ∧ True))) ∨ p4) → p2) ∧ p2)) ∧ p5) ∧ ((p4 ∨ ((p1 → p4) ∧ p1)) → (p5 ∧ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_616367696329269689022413275052 : (((((p5 ∨ (p2 ∧ (p1 ∧ (p1 ∧ (p4 ∧ (False ∨ (p5 → False))))))) ∨ (True ∨ (True ∨ ((p2 ∧ p1) → (p5 → (p4 ∨ p3)))))) ∨ p2) ∨ p2) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_779619100909873560946328523511 : (((p2 ∨ ((p2 → ((((p2 ∨ (p3 ∧ p2)) ∨ ((False → False) ∧ True)) → False) ∨ ((p2 ∨ (p1 ∨ (p1 ∧ (p4 → p1)))) ∨ p5))) ∨ True)) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_783594189108918987552127706534 : (((p3 ∨ ((((p5 → (p5 → (False ∧ False))) ∨ p3) ∨ (p1 ∧ True)) → (((p2 ∨ (((p2 ∨ p4) ∨ (p5 → p2)) ∨ p5)) ∨ p2) ∧ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159635082880074225950013450004 : (((((p3 ∨ ((p2 → (p5 ∧ (p5 → True))) ∨ ((p1 → p4) ∨ p1))) → (True ∧ True)) ∨ p5) ∨ p1) → (((p1 ∧ p1) ∧ False) ∨ (True ∧ True))) := by
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
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248675034275959424618085346860 : ((p3 ∨ p1) ∨ (p5 → (((((p1 ∧ p2) ∨ p1) ∨ (p1 ∨ (True → p3))) ∨ ((True → False) ∨ p5)) ∨ ((p4 → (p2 ∨ (False → p2))) → p1)))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187653514284188822345578215947 : ((True → ((((p1 → (p1 ∨ True)) ∨ (p3 → False)) ∧ p4) ∧ p5)) → (((p2 ∨ p3) → (p4 → p5)) ∧ (True ∨ (((p5 ∧ p2) ∨ p2) ∨ False)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h5 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h6 := h1 h5
    -- We need to get the right conjuct of h6 based on <expert-advice>.
    let h7 := h6.right
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h8 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h9 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h10 := h1 h9
    -- We need to get the right conjuct of h10 based on <expert-advice>.
    let h11 := h10.right
    -- One of the premise coincides with the conclusion.
    exact h11
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147382986791967574154095393083 : ((((p3 → (p1 → ((True ∧ (p1 ∧ (True → False))) ∧ True))) ∨ (((p5 ∧ p2) ∧ p3) ∨ (p1 ∧ p2))) ∨ p2) ∨ ((False → p2) ∨ (p2 → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50021030291970257031441406761 : ((((((False ∨ False) ∨ p3) ∨ True) ∧ ((True ∧ (p5 ∨ True)) ∧ (True ∨ (p1 ∧ ((True ∨ p4) ∧ p3))))) ∧ ((p3 → True) ∧ (p2 ∨ True))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
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
theorem thm_5_vars_84675798603416867456055105046 : (((((False → (((False ∨ p2) ∨ (p4 ∧ (False → False))) → p5)) ∨ p2) ∨ p1) ∧ (((p1 ∨ (False ∧ p3)) → p1) → (p2 ∧ (True ∧ False)))) → p1) := by
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
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h6 : ((p1 ∨ (False ∧ p3)) → p1) := by
        -- Implications on the right can always be decomposed.
        intro h7
        -- Disjunctions on the left can always be decomposed.
        cases h7
        case inl h8 =>
          -- One of the premise coincides with the conclusion.
          exact h8
        case inr h9 =>
          -- Conjunctions on the left can always be decomposed.
          let h10 := h9.left
          let h11 := h9.right
          -- False on the left can always be used.
          apply False.elim h10
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h12 := h3 h6
      -- We need to get the right conjuct of h12 based on <expert-advice>.
      let h13 := h12.right
      -- We need to get the right conjuct of h13 based on <expert-advice>.
      let h14 := h13.right
      -- False on the left can always be used.
      apply False.elim h14
    case inr h15 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h16 : ((p1 ∨ (False ∧ p3)) → p1) := by
        -- Implications on the right can always be decomposed.
        intro h17
        -- Disjunctions on the left can always be decomposed.
        cases h17
        case inl h18 =>
          -- One of the premise coincides with the conclusion.
          exact h18
        case inr h19 =>
          -- Conjunctions on the left can always be decomposed.
          let h20 := h19.left
          let h21 := h19.right
          -- False on the left can always be used.
          apply False.elim h20
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h22 := h3 h16
      -- We need to get the right conjuct of h22 based on <expert-advice>.
      let h23 := h22.right
      -- We need to get the right conjuct of h23 based on <expert-advice>.
      let h24 := h23.right
      -- False on the left can always be used.
      apply False.elim h24
  case inr h25 =>
    -- One of the premise coincides with the conclusion.
    exact h25



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_654281105076798862376576097039 : ((((((False ∨ ((((p3 → False) → (((False ∨ ((False ∨ p1) → p4)) → p1) ∧ p4)) ∨ p4) ∧ p3)) ∨ (p5 ∨ p1)) ∨ True) ∨ (True ∨ p5)) ∨ False) ∧ True) := by
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
theorem thm_5_vars_64245363016811527841816452668 : ((False ∨ (p2 ∨ (((((((p5 → ((p4 ∧ (p4 ∨ p2)) ∧ p3)) ∨ False) → (p2 ∨ p4)) ∨ p2) → p5) → ((False ∨ False) ∨ p2)) → p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205068271506873552082740135883 : (((p3 → (True ∨ (False → p3))) → p1) ∨ (False ∨ (((True ∨ (p2 → p4)) ∨ True) → ((((((False → p5) ∨ True) ∧ p5) → p2) → p5) ∨ True)))) := by
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
theorem thm_5_vars_180289044781661253078154113712 : ((((((False ∧ p1) → (p4 ∨ p3)) ∧ (False ∨ p3)) ∧ p3) ∧ (p4 ∨ False)) → ((((p3 ∧ (p3 ∨ (p5 ∧ (p1 ∨ True)))) → p1) ∨ False) ∨ True)) := by
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
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h11 =>
      -- False on the left can always be used.
      apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258118667271178964850225001892 : ((p4 ∨ p3) → ((((True ∨ False) ∧ (p4 → ((p1 → p4) → p1))) ∨ (p2 → p4)) → (((p1 → (p5 ∧ False)) → p3) ∨ ((False → p1) → p4)))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h7 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h8
        -- One of the premise coincides with the conclusion.
        exact h7
      case inr h9 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h10
        -- One of the premise coincides with the conclusion.
        exact h9
    case inr h11 =>
      -- False on the left can always be used.
      apply False.elim h11
  case inr h12 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h13 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h14
      -- One of the premise coincides with the conclusion.
      exact h13
    case inr h15 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h16
      -- One of the premise coincides with the conclusion.
      exact h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319590990957611712307343621796 : (p4 ∨ ((False → ((((True ∧ (False → p5)) ∧ True) ∨ False) → p1)) → ((p5 → ((p4 ∧ p2) → ((False ∨ p5) ∧ (p1 ∨ True)))) ∨ (p1 → p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Conjunctions on the left can always be decomposed.
  let h6 := h3.left
  let h7 := h3.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_264978294981716885440750682190 : (True ∧ ((p5 ∨ p3) → (p4 ∨ ((p1 ∨ p1) ∨ (((((p5 ∨ p3) ∧ p5) → False) ∨ (((((p3 ∧ True) ∨ p3) ∨ p3) ∨ True) ∧ True)) ∨ p1))))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_265528199431389996686421330416 : (True ∧ (False ∨ (((p1 ∧ (True ∧ p5)) ∧ ((p2 ∧ ((p3 → p1) → (p2 → p4))) ∨ ((False ∨ p4) ∨ (False ∨ p1)))) ∨ (False → (p5 ∨ p5))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166824004088505268345820847336 : (((((p5 ∨ (((p3 → p5) ∧ p3) → (False ∧ (p3 ∧ (p5 → True))))) → True) ∨ p3) ∧ True) → (p4 ∨ (p2 ∨ (p4 → ((p1 ∨ p4) ∧ True))))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h7
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134909027160990262022476281559 : ((((False ∨ (p4 ∨ ((p1 → ((p4 ∧ True) ∧ (((p2 → p4) ∧ p4) → (p2 ∧ p2)))) ∨ False))) ∧ p3) ∧ (False → p4)) ∨ (True → (p1 → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114449598210255625650881649579 : (((((((p3 ∨ (((True ∨ False) → False) ∧ False)) ∨ (p1 → p2)) ∧ (p2 → p4)) ∧ True) ∧ p2) → (((True ∧ p4) → False) → p3)) ∨ (p3 → p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  cases h7
  case inl h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- One of the premise coincides with the conclusion.
      exact h10
    case inr h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- False on the left can always be used.
      apply False.elim h13
  case inr h14 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h15 : (True ∧ p4) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
      have h16 : p2 := by
        -- One of the premise coincides with the conclusion.
        exact h4
      -- We have shown the premise of h8, we can now drive its conclusion.
      let h17 := h8 h16
      -- One of the premise coincides with the conclusion.
      exact h17
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h18 := h2 h15
    -- False on the left can always be used.
    apply False.elim h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184173243709227320410706475464 : (((p1 → (((p4 → (p5 ∧ p4)) → False) ∨ (False ∨ p2))) ∨ True) ∨ (((False ∨ (p3 ∨ (False ∧ (True ∨ ((p2 ∧ p5) → p1))))) ∨ p4) ∨ True)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_355865876642651736536974389255 : (p5 → (((((False ∧ False) ∧ p3) ∨ p2) ∨ ((True ∧ p5) → (False ∧ (True ∨ (p4 ∧ ((False → p5) ∨ (p5 ∨ p3))))))) ∨ ((p3 ∨ p2) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_625065234831866641201474339968 : ((((True → ((p4 ∨ ((p4 ∧ (((True ∧ ((False ∨ (p2 → True)) → p3)) → p2) ∧ p4)) ∧ (True → (False ∨ (False ∧ p3))))) ∨ p3)) ∨ True) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_187773851535888239205365327593 : ((p3 → (((((p1 ∧ p2) ∧ p4) ∧ (p3 ∨ p4)) ∨ p4) ∧ p5)) → ((p2 → (((p4 ∧ p1) ∧ ((False ∨ (p3 ∨ p2)) ∧ p4)) ∨ True)) ∨ p4)) := by
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
theorem thm_5_vars_58453456901960926386624838893 : (((p3 ∨ p2) ∧ ((p3 ∨ (True ∧ p3)) ∧ ((((p3 → p3) → p2) ∧ (False ∨ (p5 → (p5 ∧ p2)))) → (p4 ∨ ((p2 ∧ True) → p1))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_676206495713004073533044427434 : ((((((False → False) → True) ∧ ((p4 → p4) ∧ (p1 ∧ (p5 → (True ∧ ((True ∧ True) → (p4 ∧ p2))))))) ∧ (True → (p4 ∧ (False ∧ p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



