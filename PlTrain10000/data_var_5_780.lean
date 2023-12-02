variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_252532613020334328157473747957 : ((p5 → p2) ∨ ((p4 ∨ (((p4 ∨ False) → p5) ∧ (p3 ∧ (p4 ∧ True)))) ∨ ((p4 ∧ p1) → ((p3 ∨ (True → ((True ∨ p4) → p3))) → p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h1.left
    let h8 := h1.right
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h9 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h10 := h6 h9
    -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
    have h11 : (True ∨ p4) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h10, we can now drive its conclusion.
    let h12 := h10 h11
    -- One of the premise coincides with the conclusion.
    exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199450994548628911216820151155 : (((p3 ∧ (p4 ∨ ((p5 → False) ∨ p2))) ∨ p1) → (p5 ∨ ((False ∨ (False ∨ ((True ∧ ((p4 → p2) → (False → p2))) ∨ (p4 ∨ False)))) ∨ p2))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
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
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- True on the right can always be proven directly.
        apply True.intro
        -- Implications on the right can always be decomposed.
        intro h8
        -- Implications on the right can always be decomposed.
        intro h9
        -- False on the left can always be used.
        apply False.elim h9
      case inr h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h10
  case inr h11 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Implications on the right can always be decomposed.
    intro h12
    -- Implications on the right can always be decomposed.
    intro h13
    -- False on the left can always be used.
    apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_689387880958584695094017821115 : ((((((p4 ∧ (((p3 ∧ False) → p1) → (p4 → p1))) → (p4 ∧ p1)) → (p3 ∧ p1)) ∨ ((p4 → ((p5 ∧ (p2 → p3)) ∧ True)) ∧ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137311717786570280405101322486 : ((p2 ∧ ((p4 → ((p2 → p1) ∧ (p5 ∨ (False ∧ (p5 ∨ p3))))) ∨ (((((True → False) ∨ False) ∨ p4) ∨ True) → p3))) ∨ (p1 → (p3 ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_701985490434695553361584622901 : ((((p4 ∨ (p2 ∧ (((p5 ∨ p4) → p2) ∧ (True ∨ False)))) ∧ ((p5 ∧ False) ∧ (True → ((p2 → (True ∨ p1)) ∧ ((p5 → False) ∨ p3))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_755004206644502301280191651407 : (((False ∧ (True → (((((p1 ∨ ((False → p4) → p5)) → (((p4 ∨ (p4 ∧ (p2 ∨ p2))) → p1) → p1)) ∨ p3) ∨ (p3 ∧ p1)) ∨ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157331768175248490676496927848 : (((False ∨ ((p1 ∨ False) ∧ (((((p5 → True) ∧ p3) → p4) ∨ p1) ∧ ((p2 → False) → p2)))) → False) ∨ (True ∨ ((p3 ∧ True) ∨ (p1 → p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_238142465680332494207185597917 : ((True ∨ p3) ∧ ((p2 ∨ (p3 ∧ ((p4 ∨ p3) → False))) ∨ (((p5 ∨ (p2 ∧ True)) ∧ (True ∧ False)) ∨ (((p3 ∨ p1) → p3) ∨ (False → p4))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230972250444615714973887543028 : (((p4 ∧ p2) ∨ p1) → (((p3 ∧ (False → True)) ∧ (p1 ∧ (((((p4 → (p4 → True)) → p5) → (p3 → (p2 ∨ p1))) → p5) ∨ p5))) ∨ True)) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214486652949531887453682089837 : (((p1 ∧ p4) ∧ (p4 ∧ p2)) ∨ ((p4 → p1) → ((p5 ∧ p2) ∨ (True ∧ ((p1 ∧ (((True ∧ p4) ∧ (p5 ∧ p3)) ∧ (p2 ∧ p4))) → p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- Conjunctions on the left can always be decomposed.
  let h9 := h7.left
  let h10 := h7.right
  -- Conjunctions on the left can always be decomposed.
  let h11 := h8.left
  let h12 := h8.right
  -- Conjunctions on the left can always be decomposed.
  let h13 := h6.left
  let h14 := h6.right
  -- One of the premise coincides with the conclusion.
  exact h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342599731657664786059649876516 : (p2 → ((((p2 ∨ (p5 ∧ (p5 ∨ (p2 ∨ p3)))) ∨ True) ∨ (p4 ∧ p3)) → (((False ∨ True) ∧ (p4 → (p4 ∨ (p1 → (p5 ∧ False))))) ∧ p2))) := by
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
        -- Conjunctions on the left can always be decomposed.
        let h7 := h6.left
        let h8 := h6.right
        -- Disjunctions on the left can always be decomposed.
        cases h8
        case inl h9 =>
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
    -- Conjunctions on the left can always be decomposed.
    let h15 := h14.left
    let h16 := h14.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- Implications on the right can always be decomposed.
  intro h17
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h18 =>
    -- Disjunctions on the left can always be decomposed.
    cases h18
    case inl h19 =>
      -- Disjunctions on the left can always be decomposed.
      cases h19
      case inl h20 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h17
      case inr h21 =>
        -- Conjunctions on the left can always be decomposed.
        let h22 := h21.left
        let h23 := h21.right
        -- Disjunctions on the left can always be decomposed.
        cases h23
        case inl h24 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h17
        case inr h25 =>
          -- Disjunctions on the left can always be decomposed.
          cases h25
          case inl h26 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h17
          case inr h27 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h17
    case inr h28 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h17
  case inr h29 =>
    -- Conjunctions on the left can always be decomposed.
    let h30 := h29.left
    let h31 := h29.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h30
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h32 =>
    -- Disjunctions on the left can always be decomposed.
    cases h32
    case inl h33 =>
      -- Disjunctions on the left can always be decomposed.
      cases h33
      case inl h34 =>
        -- One of the premise coincides with the conclusion.
        exact h1
      case inr h35 =>
        -- Conjunctions on the left can always be decomposed.
        let h36 := h35.left
        let h37 := h35.right
        -- Disjunctions on the left can always be decomposed.
        cases h37
        case inl h38 =>
          -- One of the premise coincides with the conclusion.
          exact h1
        case inr h39 =>
          -- Disjunctions on the left can always be decomposed.
          cases h39
          case inl h40 =>
            -- One of the premise coincides with the conclusion.
            exact h1
          case inr h41 =>
            -- One of the premise coincides with the conclusion.
            exact h1
    case inr h42 =>
      -- One of the premise coincides with the conclusion.
      exact h1
  case inr h43 =>
    -- Conjunctions on the left can always be decomposed.
    let h44 := h43.left
    let h45 := h43.right
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149823691317491720182667203935 : ((p1 ∨ (((True → True) ∧ (p3 ∧ ((p2 ∨ p4) ∧ ((p5 ∨ p4) ∨ (False ∨ (p4 ∧ (False → p5))))))) → p2)) ∨ ((False → p4) ∧ (p2 → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42549868331304504702864945732 : (((p1 ∨ (((p2 ∨ False) ∨ p2) → (((p5 ∧ ((p4 ∨ ((p3 ∨ False) ∧ (True ∧ p4))) ∨ True)) → p1) → (p3 ∧ (False ∧ p1))))) ∨ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_765843935240817902364793556946 : (((p4 ∧ ((p3 → ((False ∧ (p4 → True)) ∨ True)) ∧ (((p1 ∧ p2) ∧ False) ∨ (p3 → (((False ∨ (p1 ∧ (p1 ∧ p3))) ∨ p5) ∨ p4))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232972013638751984653838804058 : ((p3 ∧ (False → p5)) → ((((p1 → p3) → p4) ∨ True) ∨ ((p4 → (p2 → (((True ∧ (p1 → p1)) ∨ True) → (p1 → (p5 ∨ True))))) ∨ False))) := by
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
theorem thm_5_vars_44971544912574963133928841872 : ((((False → p1) ∧ (((p1 → ((p4 → p3) ∨ ((p4 ∨ False) → p4))) ∨ p5) ∧ (p3 ∧ (True ∨ (False ∨ ((p1 → False) → p5)))))) → p3) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    cases h8
    case inl h9 =>
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- False on the left can always be used.
        apply False.elim h11
      case inr h12 =>
        -- One of the premise coincides with the conclusion.
        exact h7
  case inr h13 =>
    -- Conjunctions on the left can always be decomposed.
    let h14 := h5.left
    let h15 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h15
    case inl h16 =>
      -- One of the premise coincides with the conclusion.
      exact h14
    case inr h17 =>
      -- Disjunctions on the left can always be decomposed.
      cases h17
      case inl h18 =>
        -- False on the left can always be used.
        apply False.elim h18
      case inr h19 =>
        -- One of the premise coincides with the conclusion.
        exact h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319475745532750196898906879593 : (p4 ∨ ((((p2 ∧ (p1 ∨ (False ∨ p2))) ∨ (p2 → (p2 ∨ False))) ∧ p2) → ((((True ∧ ((p5 → p4) ∨ True)) ∨ p4) ∨ (p5 ∨ p2)) ∨ True))) := by
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
    cases h6
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- False on the left can always be used.
        apply False.elim h9
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
theorem thm_5_vars_37751561732703967979615287762 : (((((False ∨ ((False → (p2 ∨ True)) → p4)) → (p3 → ((False ∧ ((False ∨ (True ∧ (p1 → p3))) ∧ (p1 ∧ False))) → p3))) → p4) ∧ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42361997666450215054346988430 : (((p3 ∧ (p2 ∨ (((p1 → (True → p3)) ∨ (p2 → ((False → ((((p3 ∧ p3) ∨ True) ∧ p2) → p4)) ∨ (True ∨ False)))) → p1))) ∨ True) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115004855445620226960393539516 : ((((p3 ∨ (p2 ∨ p3)) ∧ (((p5 ∧ False) ∧ False) ∨ (p3 ∧ True))) ∧ (((p4 ∧ p2) ∧ p1) ∨ (p5 ∧ (p1 ∨ (False → p1))))) ∨ (p1 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187624277103250027486415260220 : ((p5 ∨ ((((False ∨ p5) → ((p2 ∨ p4) ∧ p5)) → p5) ∧ p2)) → (p5 ∧ ((p4 ∨ p1) ∨ (((p3 ∧ (p3 ∧ p5)) → (p5 → p1)) ∨ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h6 : ((False ∨ p5) → ((p2 ∨ p4) ∧ p5)) := by
      -- Implications on the right can always be decomposed.
      intro h7
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- False on the left can always be used.
        apply False.elim h8
      case inr h9 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h5
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h10 =>
        -- False on the left can always be used.
        apply False.elim h10
      case inr h11 =>
        -- One of the premise coincides with the conclusion.
        exact h11
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h12 := h4 h6
    -- One of the premise coincides with the conclusion.
    exact h12
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h13 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h13
  case inr h14 =>
    -- Conjunctions on the left can always be decomposed.
    let h15 := h14.left
    let h16 := h14.right
    -- We want to use the implication h15 based on <expert-advice>. So we show its premise.
    have h17 : ((False ∨ p5) → ((p2 ∨ p4) ∧ p5)) := by
      -- Implications on the right can always be decomposed.
      intro h18
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Disjunctions on the left can always be decomposed.
      cases h18
      case inl h19 =>
        -- False on the left can always be used.
        apply False.elim h19
      case inr h20 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h16
      -- Disjunctions on the left can always be decomposed.
      cases h18
      case inl h21 =>
        -- False on the left can always be used.
        apply False.elim h21
      case inr h22 =>
        -- One of the premise coincides with the conclusion.
        exact h22
    -- We have shown the premise of h15, we can now drive its conclusion.
    let h23 := h15 h17
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h23



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49847650563709140905883256402 : (((((p5 → ((((((False ∨ p1) ∨ (p1 ∧ p4)) ∧ p5) ∨ p3) → True) → (False ∨ p1))) ∨ p5) ∧ p4) ∧ ((p5 ∧ False) ∨ (p2 ∨ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193824163028302687579211703028 : ((p5 ∧ ((False ∨ True) → (p1 ∧ ((p2 → p1) ∨ p3)))) → (((p4 → (((False ∨ p3) → False) ∧ ((p3 → p2) → False))) ∨ True) ∨ (True ∧ p5))) := by
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
theorem thm_5_vars_620191194350720004889052826797 : (((((p3 ∧ p1) ∨ (((p3 ∧ p1) → (((p3 ∧ p1) ∨ (True → True)) → p2)) ∧ (p3 → (((p5 → (False ∧ p1)) ∨ p2) ∧ p2)))) ∨ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149436146693616177340589368214 : ((True ∧ (p2 → (p1 ∨ (((p2 ∧ True) ∧ (p1 → (p5 ∨ (((p4 ∨ True) → (p5 ∧ p2)) → p4)))) ∧ True)))) ∨ ((False → p1) ∧ (p1 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308593301905330897795370954518 : (p2 ∨ (((p1 ∨ (p5 → p1)) ∨ ((p3 → p5) ∧ (False ∨ ((False ∨ p4) ∨ (p3 → ((((p5 → p2) → (p4 ∨ p3)) → p1) ∧ True)))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58661735245776569704209714722 : (((p1 → p4) ∧ ((p3 ∧ p4) ∧ ((((((p1 → ((p1 → p5) ∧ (True → p1))) → (False → p2)) ∨ (p3 ∨ p5)) ∨ True) → p1) ∧ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64069031859653049266474946908 : ((False ∨ ((((((p2 ∨ ((True ∨ p2) ∨ p3)) → p2) → p1) ∨ p2) ∧ ((p1 ∨ p1) ∧ p2)) ∨ ((p2 ∨ ((p5 → p1) ∨ True)) ∨ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346591304353852055393022639896 : (p3 → ((((p3 → (((True → p4) → (False ∨ p2)) → (p4 → False))) ∧ ((False ∨ (True → (p2 ∨ p2))) ∨ p4)) ∨ True) ∨ (p2 ∧ (p2 ∨ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_602483077601131236125832475 : (((p1 → ((p3 ∨ p1) → (p5 → (p1 ∧ (p2 ∧ ((p1 ∧ ((p5 ∧ (p5 ∧ (p4 ∧ True))) ∨ p1)) ∨ (p5 → False))))))) → p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_188871303286266259513360083402 : (((p4 ∨ ((p4 → False) ∧ False)) ∨ ((p3 → p5) ∨ True)) ∧ ((p5 ∧ True) → (p5 ∧ ((p2 ∧ p2) ∨ (False → ((p3 ∧ (True ∨ p3)) ∨ p5)))))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h6
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57283568508917638868191412075 : ((((True → p5) → p2) ∨ (p5 ∧ (((False ∧ p2) → p2) ∧ ((((p3 ∧ (p5 → ((p4 ∨ p5) ∧ False))) ∧ (True ∨ p5)) ∨ p3) → p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_668007467575316631989092368145 : ((((p4 ∨ ((p1 ∨ (p2 → (p1 ∧ p1))) → ((((False ∨ p5) ∨ p4) ∧ p4) → (p1 → ((p5 ∨ p3) ∧ p3))))) ∧ ((False → p2) ∨ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_169514416233953987378805378047 : (((p1 ∧ (((p3 ∨ (p4 → (True ∨ p3))) ∧ p4) → ((p3 ∨ True) ∧ p1))) ∨ True) ∧ (((False ∨ True) → False) → (((p2 ∧ True) → p1) ∧ p4))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h5 : (False ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h5
  -- False on the left can always be used.
  apply False.elim h6
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h7 : (False ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h8 := h1 h7
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49737558539886121842538401171 : (((p3 ∧ (((p3 ∧ ((((False ∧ (False ∨ p4)) → p2) → p5) → ((p2 → p2) ∧ True))) ∧ p2) ∧ (False → False))) → ((p4 → p5) ∧ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160555160535198362178695589254 : ((((((p2 → ((p1 ∨ (True ∨ p3)) → p4)) → True) ∨ p2) ∨ p2) → ((p3 ∧ False) ∧ (p2 ∨ p5))) → (((True ∧ False) ∧ (p2 ∨ p2)) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((((p2 → ((p1 ∨ (True ∨ p3)) → p4)) → True) ∨ p2) ∨ p2) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_660777583206561312489430031263 : ((((((True ∨ p5) ∧ (p5 ∧ (p4 ∧ ((((p5 ∧ p1) ∧ ((p5 ∨ (p5 ∧ False)) ∧ p5)) → (p1 → p3)) ∧ p1)))) → True) → (p3 → p3)) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_149562559772263019865991338906 : ((p2 ∧ ((p1 ∧ p3) ∨ (True ∧ (p5 ∨ (p1 ∨ ((p3 → ((p5 ∨ ((False ∨ p5) ∧ True)) ∨ p1)) → p3)))))) ∨ (((p3 → True) ∧ True) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_675363166672649376179739447344 : (((((((True → ((p5 → (False → p3)) ∨ (p3 ∧ p3))) ∨ ((p5 ∨ p2) → p1)) ∨ (p4 ∧ p3)) → p5) ∧ ((p2 ∨ (p4 ∧ p4)) ∧ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134526103635538910646116009776 : (((((p2 ∧ ((((p3 → (p2 → p4)) ∨ (p2 ∧ p2)) ∧ ((p4 ∨ (p2 ∨ p2)) → False)) → p3)) ∧ False) → p1) → p1) ∨ (p1 ∨ (p3 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_666929571802777750912962734504 : (((((p3 ∨ (False → (p2 ∧ (p2 ∨ p2)))) → ((True ∧ (p1 → p5)) ∨ (p3 ∨ (True ∨ (True ∧ (p1 ∨ p4)))))) ∧ ((p3 → p5) → p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193629896487688911394536402816 : ((True ∧ ((p1 → True) → (((p5 ∨ p1) ∨ True) ∧ p2))) → (p2 ∧ ((p5 → (((p5 → p3) ∨ (p5 → ((p4 ∧ p3) ∨ p3))) ∨ p5)) ∨ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : (p1 → True) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h4
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- One of the premise coincides with the conclusion.
  exact h7
  -- Conjunctions on the left can always be decomposed.
  let h8 := h1.left
  let h9 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h10
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44797718523203730267188784184 : (((((p2 → p3) ∨ p5) ∧ (p4 ∨ (((((p3 ∨ True) ∨ (p3 ∨ ((p3 ∨ (p2 ∧ p4)) ∨ True))) ∧ p4) → p4) ∧ (p3 → p4)))) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174645875403457169468288230961 : ((((True → p2) ∧ p4) ∧ ((((p2 → False) ∧ ((p2 → True) ∨ p1)) ∨ p1) ∨ p1)) → (p3 → (False ∨ (p1 ∨ ((p3 ∨ p1) ∨ (p3 ∧ p2)))))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h2
      case inr h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h12
    case inr h13 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h13
  case inr h14 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40449979516694312467773741212 : (((((((p1 ∧ p3) ∨ (p2 → p3)) ∧ p4) → (((((p2 → p2) → False) ∧ (True ∧ p5)) ∨ False) ∧ ((p2 → p2) ∧ p2))) ∨ p1) ∨ True) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257518659532975237255387894024 : ((p3 ∨ False) → (((p2 ∧ True) ∧ p4) ∨ (((p1 ∨ (True ∧ ((p2 ∨ True) → p4))) ∧ p5) ∨ ((p5 → p3) ∨ ((True → (p2 ∨ True)) ∧ p1))))) := by
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
    -- Implications on the right can always be decomposed.
    intro h3
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h4 =>
    -- False on the left can always be used.
    apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299255698656197008819157385861 : (False ∨ (((((p2 ∨ p4) → ((((p3 ∨ (True → ((p1 ∧ p2) ∨ p5))) ∨ False) ∧ p3) ∨ p4)) ∧ True) ∨ ((p1 ∨ True) → (True ∨ p2))) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336440730902327841125793586077 : (p1 → ((p4 ∨ (((p2 ∨ ((p4 → (p3 → p3)) ∨ ((p2 ∧ (p4 ∨ p4)) ∨ ((p1 → True) ∧ p1)))) → (p3 ∧ (False ∧ False))) ∨ p1)) ∨ p3)) := by
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
theorem thm_5_vars_37079750204091450460049090345 : ((((((((p2 ∨ (((((True ∨ p3) → p3) → p5) ∨ (p3 → False)) ∨ (p4 → p2))) → False) → p2) ∨ (p3 ∧ p3)) ∨ False) ∧ True) ∧ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37976571367715902067009060099 : ((((((((p4 ∧ True) → (p3 ∧ (False → (False ∧ p1)))) → p5) → ((p2 → (True → p1)) ∨ False)) → (True → p5)) ∨ (p3 → p3)) ∧ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300161877577094968725434674111 : (False ∨ ((p2 → ((((p4 ∧ p3) → p1) → ((p4 ∧ ((p3 → True) ∨ (p5 ∨ p3))) ∧ False)) ∨ (((False ∨ True) → p2) → True))) ∨ (p4 ∧ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_205972319197336285910243762744 : ((p1 ∧ ((p4 ∨ (p5 → p5)) ∨ p3)) ∨ ((p3 ∨ p3) → (((((p1 ∨ p1) → (p5 → (p4 ∧ ((p2 → p5) → p2)))) → p5) → p1) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_301996905110978584880951261756 : (False ∨ ((p4 → p4) → ((p1 → ((p2 → ((True ∧ True) → p4)) ∧ (p4 → p2))) ∨ ((p3 → (p3 → True)) ∨ ((False ∨ (p2 ∧ p1)) → p1))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56916956929240841629988685796 : (((p5 ∧ (False → True)) ∧ (((p1 ∨ ((((p5 ∨ False) → ((p1 ∧ p1) → (True ∧ p1))) → ((p4 ∨ p1) ∨ p4)) ∧ p2)) ∨ p2) ∧ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_255458780363143959699755267119 : ((p5 ∧ p1) → ((True ∧ p1) → ((p2 ∨ (p3 ∨ ((p2 ∧ (p2 ∨ p4)) ∨ ((p2 ∨ ((p5 → p4) ∨ p3)) ∨ ((p5 ∨ p4) ∨ p2))))) ∨ p5))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59732644300911669358621974522 : (((p1 ∧ True) → (((((p3 ∧ (p5 ∨ ((False ∧ ((((p4 ∧ p4) ∨ True) → p4) → (p5 ∧ p4))) ∧ False))) ∨ p1) ∨ True) ∧ True) ∨ p5)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40904743636235005730186721377 : ((((False ∧ ((p2 ∨ ((((True ∧ (p2 ∨ p4)) → (p3 ∧ (p1 ∨ p5))) ∨ p2) → (True ∧ (p3 ∧ p2)))) ∧ p3)) ∧ (p5 → p4)) ∨ True) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39669555020738666017699644233 : (((p4 ∨ ((((p5 ∨ (False ∧ True)) ∨ p5) → (((((p3 ∧ p1) ∧ p5) → (p4 → p4)) ∧ p3) ∧ ((p2 → p5) ∨ p4))) ∧ p4)) ∧ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_247892994352247241883896553543 : ((p1 ∨ p3) ∨ ((((p5 ∧ (p5 ∧ True)) → ((p4 ∨ ((p5 ∨ ((p4 → p5) ∨ p3)) → ((p2 → True) ∨ p3))) → (p5 ∧ p1))) → p3) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258417161922885488141027084017 : ((p5 ∨ p1) → ((((False ∧ True) ∧ ((p3 ∨ p5) → (((p1 ∨ True) ∧ (p3 → (True ∧ p5))) → p2))) ∧ p2) ∨ ((False ∨ False) → (p1 ∨ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- False on the left can always be used.
      apply False.elim h4
    case inr h5 =>
      -- False on the left can always be used.
      apply False.elim h5
  case inr h6 =>
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
      -- False on the left can always be used.
      apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45912639309185104612343054112 : (((p4 → ((p2 ∧ (p3 ∧ (p1 → (True → ((((True ∧ True) ∨ False) ∨ p2) → p1))))) → ((False ∨ ((p1 → p4) ∧ p1)) → p4))) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346766368368822703922900600191 : (p3 → ((((p2 ∧ (p1 ∨ (((p5 ∨ False) ∧ (p3 → True)) ∧ (((p1 → p4) ∧ p3) ∨ p1)))) ∨ p4) ∨ p4) ∨ (p5 → (p3 ∨ (p3 → p2))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315835881425050519026263412875 : (p3 ∨ ((True → p1) → (p2 → (((p3 ∨ (p2 ∨ False)) → ((True ∨ p1) → (True → ((p4 ∧ p3) ∨ (p5 → p2))))) ∧ (p3 → (p1 ∨ False)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h11
        -- One of the premise coincides with the conclusion.
        exact h2
      case inr h12 =>
        -- False on the left can always be used.
        apply False.elim h12
  case inr h13 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h14 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h15
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h16 =>
      -- Disjunctions on the left can always be decomposed.
      cases h16
      case inl h17 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h18
        -- One of the premise coincides with the conclusion.
        exact h2
      case inr h19 =>
        -- False on the left can always be used.
        apply False.elim h19
  -- Implications on the right can always be decomposed.
  intro h20
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h21 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h22 := h1 h21
  -- One of the premise coincides with the conclusion.
  exact h22



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208755868749926712990846707200 : ((p2 ∧ (((p3 → p3) ∧ True) ∧ p2)) → (((False ∧ (((p2 ∧ p2) ∨ p5) → p4)) ∨ (p4 ∨ ((p3 ∧ False) ∨ p5))) ∨ ((p2 → True) ∨ p3))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h8
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52027694432626642951904195795 : (((p2 ∨ ((p4 ∧ (p3 ∨ ((p4 → p3) ∨ (p2 ∨ ((p1 → False) ∨ False))))) ∨ False)) ∨ (((p2 ∧ (p2 ∨ p5)) → (p2 → p2)) ∨ True)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40362520982864442283097987409 : (((((((p5 → ((True ∨ p5) ∨ p3)) → False) ∨ (p1 → ((False ∨ (p1 ∧ ((True → True) ∧ (p4 ∧ p2)))) ∨ p2))) → p5) ∨ p1) ∨ True) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_102942082452656664553863859339 : ((((((((p3 → p5) ∧ (False → p3)) ∧ (True ∨ True)) → p4) ∨ ((p2 ∨ p2) ∨ False)) ∨ (p1 → ((False ∨ p5) ∨ False))) ∨ True) ∧ (p4 ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351988773112369453405364587457 : (p4 → (((((p5 → True) → p3) ∧ (p2 ∨ p2)) ∧ p2) ∨ (p3 ∨ ((((False → (True → False)) ∧ p1) ∧ p5) ∨ ((p3 ∨ p4) ∨ (p2 ∧ False)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_698924763572117890062582726336 : ((((p3 ∧ (p2 ∧ (p1 ∧ (p1 ∧ (p4 ∧ (p4 → (p2 ∧ p5))))))) ∨ (False ∨ (p3 ∨ (p5 ∨ (((p3 ∧ p5) ∨ p2) → (p5 → True)))))) ∨ p2) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314275905677020726369791467080 : (p3 ∨ ((False ∨ (((False ∧ p2) ∧ (p2 → True)) ∧ ((p5 → ((p5 ∨ p1) → (p4 ∧ ((p4 → p1) ∨ True)))) ∧ True))) ∨ (p2 ∨ (p4 → p4)))) := by
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
theorem thm_5_vars_54268530495226312547418495205 : (((((p4 ∨ p2) ∨ True) ∧ ((p5 ∨ p1) → p4)) ∧ (((p1 → ((((p1 → p4) → p3) → p2) → p2)) ∧ (p5 ∧ p2)) ∨ (False → p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53609586231818472486023749608 : (((((p2 ∨ ((p5 ∧ True) ∧ False)) ∨ p1) ∨ (p3 ∨ p3)) ∧ (((p3 ∨ p1) → (p2 → p4)) ∧ (((False ∧ (True → True)) ∧ True) → p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_697100850279654525501481968661 : (((((p3 → ((p5 ∧ True) → False)) ∧ ((p1 ∧ (p5 ∧ p1)) → False)) ∧ ((False → (((p2 ∨ p4) → True) ∨ p3)) → (True → (p3 ∧ p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54624363464226435695351243884 : (((((((p2 ∨ p4) ∨ True) ∧ p4) → True) ∧ p4) → (((p2 → ((p1 ∨ (p5 ∨ p1)) → (p2 → p3))) ∨ (p2 ∨ (p3 ∨ p2))) ∨ True)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_325054279078062833698537870215 : (p5 ∨ ((p1 ∨ p2) → (((((True → ((False → (p4 ∨ False)) → True)) ∨ False) ∧ False) ∨ p3) ∨ (((False ∧ (p3 ∧ p5)) ∨ (False ∧ True)) → False)))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- False on the left can always be used.
      apply False.elim h5
    case inr h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- False on the left can always be used.
      apply False.elim h8
  case inr h10 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h11
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h12.left
      let h14 := h12.right
      -- False on the left can always be used.
      apply False.elim h13
    case inr h15 =>
      -- Conjunctions on the left can always be decomposed.
      let h16 := h15.left
      let h17 := h15.right
      -- False on the left can always be used.
      apply False.elim h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_252099245293247203679092997659 : ((p4 → p2) ∨ ((((p5 ∧ (p1 → ((p2 → p5) → (p1 ∨ False)))) ∨ p5) → (p2 ∨ (((p1 ∧ p5) ∨ p1) ∨ True))) ∨ (False → (p4 ∧ p3)))) := by
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
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55607058856012295628373243314 : (((False → (False ∨ ((p5 ∨ p1) → p2))) → (True → (((((p1 ∧ p5) ∨ p1) ∨ (p1 ∧ (True ∧ p2))) ∧ p4) ∧ ((p3 → False) ∧ False)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190554822368604779381996966399 : (((((p5 ∨ (p2 ∧ p3)) ∧ p5) → (p2 ∧ p3)) → False) ∨ (False → (((p4 → (False ∧ (((True ∨ p1) → True) → p4))) → p4) ∧ (p4 → True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179159156305323740057339364153 : ((p2 ∧ ((((p1 ∧ True) → p3) ∧ (p1 ∨ True)) → (p3 → (True ∧ p4)))) ∨ ((((True → p5) → p4) ∨ p3) ∨ (True ∨ ((True → p4) ∧ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_329383895767126330118435443619 : (True → ((p3 → (p3 ∨ p2)) → (((p5 → ((False → p3) ∨ (True → p1))) → ((p1 ∧ True) ∧ True)) ∨ (((p4 ∨ (p2 ∨ p1)) ∨ False) → True)))) := by
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
theorem thm_5_vars_353936601243918162839121356460 : (p4 → (p2 → (p2 ∧ (p1 ∨ ((((True ∧ False) → (False → (p4 ∧ (p5 ∨ (p3 → p3))))) → ((p3 ∨ False) ∧ (True → (True → True)))) ∨ p2))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234241658539604109801209042650 : ((False → (p2 ∨ p4)) → ((((((True → p2) → False) ∨ p3) ∨ ((False ∧ (p4 ∨ p4)) → (False ∨ ((p2 → True) ∧ (p1 ∧ p1))))) ∨ False) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114610179138390732682458320902 : (((p5 ∨ (((p4 ∨ (p5 ∧ p1)) ∧ (p4 ∧ (p1 → ((p4 ∨ False) ∧ p5)))) ∨ p3)) ∧ (p5 → ((p4 ∧ p2) → (False ∨ p3)))) ∨ (False → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_729908075169537831146331857770 : (((((p3 ∧ True) → False) → ((((p1 → (p1 ∧ p5)) ∨ (p2 ∨ False)) ∧ (p5 ∨ (((p1 → True) → (p4 → p4)) → (p1 → p1)))) ∧ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47347264990211990680734855393 : ((((p2 → True) ∧ (((p4 → p3) ∧ p5) ∨ ((p5 ∧ (p1 ∨ ((p1 → p4) → (p3 ∨ True)))) ∨ (True → (p4 ∨ True))))) ∨ (p5 → p4)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54714426471414771053232990181 : ((((((True ∧ True) ∧ p4) → True) → (p5 → p2)) → ((((p2 ∨ False) ∧ p1) ∨ p2) → (p5 ∨ (p3 ∨ (p2 ∧ (False → (p1 ∧ p4))))))) ∨ p4) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h6
      -- Implications on the right can always be decomposed.
      intro h7
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- False on the left can always be used.
      apply False.elim h7
      -- False on the left can always be used.
      apply False.elim h7
    case inr h8 =>
      -- False on the left can always be used.
      apply False.elim h8
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h9
    -- Implications on the right can always be decomposed.
    intro h10
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- False on the left can always be used.
    apply False.elim h10
    -- False on the left can always be used.
    apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_196838054307016130493484491054 : (((p4 ∧ (True ∧ ((p5 ∧ p5) ∨ p5))) ∧ p4) ∨ ((((p1 ∨ p4) ∧ (True ∧ True)) ∧ ((True ∨ True) → p2)) → ((p3 → (p3 ∧ p3)) → p2))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h6.left
    let h9 := h6.right
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h10 : (True ∨ True) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h11 := h4 h10
    -- One of the premise coincides with the conclusion.
    exact h11
  case inr h12 =>
    -- Conjunctions on the left can always be decomposed.
    let h13 := h6.left
    let h14 := h6.right
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h15 : (True ∨ True) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h16 := h4 h15
    -- One of the premise coincides with the conclusion.
    exact h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_653413991904921403673594545419 : ((((p4 → ((p3 ∨ (((p2 ∧ ((True ∨ p2) → p4)) ∧ ((False ∨ (False ∨ p1)) ∨ False)) → (p1 → (p3 ∨ p1)))) ∧ p1)) ∧ (p1 ∨ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_226197565492839577921515482777 : (((p2 ∨ False) ∨ False) ∨ ((p2 → ((((True → ((((p2 ∨ False) → (p2 ∨ p2)) → p1) ∨ p4)) ∨ p2) → p4) → (p4 ∨ p5))) ∨ (p1 ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : ((True → ((((p2 ∨ False) → (p2 ∨ p2)) → p1) ∨ p4)) ∨ p2) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158095238600516047214313231344 : ((((p2 ∧ (p2 ∨ p3)) ∧ p4) ∧ (((p4 → True) ∨ p5) ∨ ((False → (False ∧ (p1 ∨ p4))) ∨ True))) ∨ ((p5 → (p4 ∨ p5)) ∨ (p3 ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_710619928198492713494129582959 : (((((p4 → (p2 ∨ p3)) ∧ (p5 → p3)) ∧ (p3 ∧ (p5 ∨ ((((((True ∧ p3) ∧ p1) → p1) ∧ p5) ∨ (p2 → (p3 → True))) ∨ p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_729382729951836217748136449258 : (((((p3 ∧ p3) ∨ False) → ((((p2 → p4) ∧ False) ∨ (((p4 ∨ (((False → (p3 → (False → p3))) ∧ p5) → False)) ∨ True) ∧ p5)) ∧ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322570146822721131061373611893 : (p5 ∨ ((p3 ∨ (p3 ∨ ((p1 ∨ (p4 ∨ True)) ∨ (((p4 → ((p1 ∨ True) → (((p3 → p2) ∧ p3) → True))) ∧ p5) → (p1 ∧ p4))))) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_867389367758857151232137855644 : (((((p4 → True) ∧ ((((False ∨ False) ∨ p4) ∧ (p3 ∧ p1)) ∨ (p2 ∨ (True ∧ (False → ((True → ((True ∧ True) ∧ p3)) ∨ True)))))) → p3) → p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p4 → True) ∧ ((((False ∨ False) ∨ p4) ∧ (p3 ∧ p1)) ∨ (p2 ∨ (True ∧ (False → ((True → ((True ∧ True) ∧ p3)) ∨ True)))))) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Implications on the right can always be decomposed.
    intro h4
    -- False on the left can always be used.
    apply False.elim h4
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_686132999445176147563978656356 : (((((p2 → (p5 ∧ ((True → p1) ∧ (p5 ∧ ((p3 → p1) → p4))))) ∨ ((True → p5) ∧ False)) → ((True → (False ∨ (p2 → p4))) ∨ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_747721993988645149780134708040 : ((((False → False) → (((((((True ∨ True) ∧ (False ∨ p1)) → (p2 ∨ False)) → False) ∧ (p2 ∧ (False → p1))) → (p4 ∧ p2)) ∨ (p5 ∧ p1))) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h7 : (((True ∨ True) ∧ (False ∨ p1)) → (p2 ∨ False)) := by
    -- Implications on the right can always be decomposed.
    intro h8
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h12 =>
        -- False on the left can always be used.
        apply False.elim h12
      case inr h13 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h5
    case inr h14 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h15 =>
        -- False on the left can always be used.
        apply False.elim h15
      case inr h16 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h5
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h17 := h3 h7
  -- False on the left can always be used.
  apply False.elim h17
  -- Conjunctions on the left can always be decomposed.
  let h18 := h2.left
  let h19 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h20 := h19.left
  let h21 := h19.right
  -- One of the premise coincides with the conclusion.
  exact h20
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_222222064054484023631457589289 : (((True → False) → False) ∧ ((p3 ∧ ((((p4 ∨ (((True → p1) ∨ p4) ∨ p5)) → (True → (p5 → p1))) ∨ p5) → p5)) ∨ (p3 → (p3 ∧ True)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134381581498953534249505138131 : (((p4 ∨ (((False ∧ False) ∨ ((p1 ∧ ((p3 ∨ p2) ∧ p3)) ∨ ((p3 ∧ (p5 ∧ p4)) ∨ p3))) ∧ (p3 → p2))) ∨ p5) ∨ (p5 → (p5 ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217347952399279470374467846786 : (((p2 ∨ (True ∨ p3)) ∨ p5) → ((p1 ∧ False) ∨ (((p2 → (p4 ∨ ((((p3 ∨ (p3 ∧ p2)) ∧ p1) → p4) → False))) ∨ (False → p1)) ∨ p3))) := by
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h4
      -- False on the left can always be used.
      apply False.elim h4
    case inr h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h7
        -- False on the left can always be used.
        apply False.elim h7
      case inr h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h8
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h10
    -- False on the left can always be used.
    apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_325755010992752418572071929303 : (p5 ∨ (p2 ∨ (((False ∧ ((p2 ∧ (p4 ∨ (((p3 ∧ p3) → p3) ∨ p2))) ∧ False)) → p4) → ((((p5 ∨ True) ∨ (p2 ∧ p3)) → p3) ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



