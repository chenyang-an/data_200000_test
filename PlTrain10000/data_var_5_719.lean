variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_662197186014901161818355219351 : (((((((p1 ∧ p4) ∧ p5) ∨ (p3 → (p5 ∧ (True → p1)))) ∧ ((p3 ∧ ((p2 ∨ p1) ∨ (p5 ∧ p1))) → (False ∨ p3))) → (p4 ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67645547222375326683932258662 : ((p1 → (p2 ∨ (((((p5 ∨ (((p1 → (((p2 ∧ p2) ∨ (p1 → (p5 → p3))) ∨ True)) ∨ p1) ∨ False)) → p2) ∨ p2) ∨ True) ∨ True))) ∨ p2) := by
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
theorem thm_5_vars_231051555025117363193964376224 : (((True ∨ p2) ∨ p1) → (p3 ∨ ((p5 → (False ∨ ((((True → (p1 → p4)) → p4) ∨ (False ∨ p4)) ∨ True))) ∨ ((False ∧ p3) ∨ (p1 → False))))) := by
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
      -- Implications on the right can always be decomposed.
      intro h4
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h6
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h8
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171677925446124941344905193866 : (((p1 ∨ (((p2 ∧ p4) ∧ p3) ∧ (p5 ∧ (((p1 → True) ∨ p4) → p2)))) ∨ True) ∨ ((False ∧ (True ∧ p1)) ∨ (((False ∧ p2) ∧ p3) → p5))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147418803182077924019667128627 : (((((p5 ∧ True) ∧ False) ∧ (((p4 → (p3 → (((p3 → p3) → True) ∧ (p5 ∧ p3)))) ∧ p5) ∧ p2)) ∨ p5) ∨ ((True ∧ p5) → (p4 → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184030377558596363228166471095 : ((((((p5 ∨ p3) → (p4 → False)) ∧ (p5 → p4)) → p5) ∨ p3) ∨ (((p3 → ((p2 → p4) ∧ (p2 ∧ True))) ∧ (p1 → (p1 ∧ p1))) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_21530611559169327150789885226 : (((False ∧ ((p5 ∧ p3) ∧ ((p5 ∨ p4) ∨ (p2 → True)))) ∨ ((p1 ∨ (False → ((p3 → (p4 → (p5 → (p5 ∧ p5)))) ∨ p2))) ∨ p5)) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_127274122599928448923434033552 : ((p2 ∨ (((((True → p4) → False) → ((((((True → False) ∧ p2) ∧ (False ∧ False)) ∧ True) → p5) ∨ (p2 ∧ p2))) ∧ p3) → p1)) → (p5 → p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h4 =>
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137032698414064077699686353690 : (((p5 ∨ False) → (p3 ∨ (((((p5 ∨ p3) → p3) ∧ (p3 → (p5 ∧ p4))) → (p3 ∧ False)) ∨ ((False ∨ p4) ∨ p5)))) ∨ (False ∧ (True → p3))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- False on the left can always be used.
    apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227178228460940218528521729820 : (((True → True) → p3) ∨ (((((p3 ∧ (((((p4 → (p1 ∧ False)) → p1) → p4) ∧ p4) → p2)) ∧ (p4 ∨ True)) → p2) ∧ (p1 → p1)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160506011052305726409627070654 : ((((p4 ∨ False) ∨ ((p2 → True) ∧ (p5 ∨ ((p5 ∧ False) ∧ p4)))) ∧ ((p4 ∧ (False ∧ p5)) ∨ p2)) → (p2 ∧ ((p2 → (False ∧ p4)) ∨ True))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h6 =>
        -- Conjunctions on the left can always be decomposed.
        let h7 := h6.left
        let h8 := h6.right
        -- Conjunctions on the left can always be decomposed.
        let h9 := h8.left
        let h10 := h8.right
        -- False on the left can always be used.
        apply False.elim h9
      case inr h11 =>
        -- One of the premise coincides with the conclusion.
        exact h11
    case inr h12 =>
      -- False on the left can always be used.
      apply False.elim h12
  case inr h13 =>
    -- Conjunctions on the left can always be decomposed.
    let h14 := h13.left
    let h15 := h13.right
    -- Disjunctions on the left can always be decomposed.
    cases h15
    case inl h16 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h17 =>
        -- Conjunctions on the left can always be decomposed.
        let h18 := h17.left
        let h19 := h17.right
        -- Conjunctions on the left can always be decomposed.
        let h20 := h19.left
        let h21 := h19.right
        -- False on the left can always be used.
        apply False.elim h20
      case inr h22 =>
        -- One of the premise coincides with the conclusion.
        exact h22
    case inr h23 =>
      -- Conjunctions on the left can always be decomposed.
      let h24 := h23.left
      let h25 := h23.right
      -- Conjunctions on the left can always be decomposed.
      let h26 := h24.left
      let h27 := h24.right
      -- False on the left can always be used.
      apply False.elim h27
  -- Conjunctions on the left can always be decomposed.
  let h28 := h1.left
  let h29 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h28
  case inl h30 =>
    -- Disjunctions on the left can always be decomposed.
    cases h30
    case inl h31 =>
      -- Disjunctions on the left can always be decomposed.
      cases h29
      case inl h32 =>
        -- Conjunctions on the left can always be decomposed.
        let h33 := h32.left
        let h34 := h32.right
        -- Conjunctions on the left can always be decomposed.
        let h35 := h34.left
        let h36 := h34.right
        -- False on the left can always be used.
        apply False.elim h35
      case inr h37 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h38 =>
      -- False on the left can always be used.
      apply False.elim h38
  case inr h39 =>
    -- Conjunctions on the left can always be decomposed.
    let h40 := h39.left
    let h41 := h39.right
    -- Disjunctions on the left can always be decomposed.
    cases h41
    case inl h42 =>
      -- Disjunctions on the left can always be decomposed.
      cases h29
      case inl h43 =>
        -- Conjunctions on the left can always be decomposed.
        let h44 := h43.left
        let h45 := h43.right
        -- Conjunctions on the left can always be decomposed.
        let h46 := h45.left
        let h47 := h45.right
        -- False on the left can always be used.
        apply False.elim h46
      case inr h48 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h49 =>
      -- Conjunctions on the left can always be decomposed.
      let h50 := h49.left
      let h51 := h49.right
      -- Conjunctions on the left can always be decomposed.
      let h52 := h50.left
      let h53 := h50.right
      -- False on the left can always be used.
      apply False.elim h53



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158987372769248740405187998224 : ((p3 ∨ ((p3 ∧ (False ∨ p5)) ∨ ((p4 ∨ (p2 ∨ p1)) → ((p3 ∧ (p5 ∨ p3)) ∨ (p3 → p5))))) ∨ ((p1 → p4) → ((p1 ∧ p3) → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h5 : p1 := by
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h5
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_764536278577546279352461028682 : (((p4 ∧ ((((p1 → (p5 → (((p4 ∨ (p4 ∨ p2)) ∧ p3) ∨ ((True ∧ ((p1 → p5) ∨ (p5 → False))) ∨ False)))) → p1) → p3) ∨ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167100276295282628965246812395 : (((((True ∨ p2) ∨ ((p2 ∧ (p5 ∧ (p2 ∧ (p2 ∨ p4)))) ∧ p4)) ∨ (p1 → p1)) ∨ p2) → ((p2 → ((p5 ∨ False) → (p3 ∨ True))) ∨ p1)) := by
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
        -- Disjunctions on the left can always be decomposed.
        cases h4
        case inl h5 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Implications on the right can always be decomposed.
          intro h6
          -- Implications on the right can always be decomposed.
          intro h7
          -- Disjunctions on the left can always be decomposed.
          cases h7
          case inl h8 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h9 =>
            -- False on the left can always be used.
            apply False.elim h9
        case inr h10 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Implications on the right can always be decomposed.
          intro h11
          -- Implications on the right can always be decomposed.
          intro h12
          -- Disjunctions on the left can always be decomposed.
          cases h12
          case inl h13 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h14 =>
            -- False on the left can always be used.
            apply False.elim h14
      case inr h15 =>
        -- Conjunctions on the left can always be decomposed.
        let h16 := h15.left
        let h17 := h15.right
        -- Conjunctions on the left can always be decomposed.
        let h18 := h16.left
        let h19 := h16.right
        -- Conjunctions on the left can always be decomposed.
        let h20 := h19.left
        let h21 := h19.right
        -- Conjunctions on the left can always be decomposed.
        let h22 := h21.left
        let h23 := h21.right
        -- Disjunctions on the left can always be decomposed.
        cases h23
        case inl h24 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Implications on the right can always be decomposed.
          intro h25
          -- Implications on the right can always be decomposed.
          intro h26
          -- Disjunctions on the left can always be decomposed.
          cases h26
          case inl h27 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h28 =>
            -- False on the left can always be used.
            apply False.elim h28
        case inr h29 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Implications on the right can always be decomposed.
          intro h30
          -- Implications on the right can always be decomposed.
          intro h31
          -- Disjunctions on the left can always be decomposed.
          cases h31
          case inl h32 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h33 =>
            -- False on the left can always be used.
            apply False.elim h33
    case inr h34 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h35
      -- Implications on the right can always be decomposed.
      intro h36
      -- Disjunctions on the left can always be decomposed.
      cases h36
      case inl h37 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h38 =>
        -- False on the left can always be used.
        apply False.elim h38
  case inr h39 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h40
    -- Implications on the right can always be decomposed.
    intro h41
    -- Disjunctions on the left can always be decomposed.
    cases h41
    case inl h42 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h43 =>
      -- False on the left can always be used.
      apply False.elim h43



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314478734811560133629162876108 : (p3 ∨ (((False ∧ p3) → ((((p5 ∨ ((p5 → p1) → (p3 → p3))) → (p4 → (p2 ∧ p5))) → p2) ∨ True)) → ((p3 → False) ∨ (True ∨ True)))) := by
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
theorem thm_5_vars_302512171712453306045087940410 : (False ∨ (False ∨ (((((p5 ∨ ((p5 → ((p5 ∧ p2) ∨ p3)) → p4)) ∨ True) ∧ (p1 ∧ (p4 → (p4 ∧ p5)))) ∨ True) ∨ (p5 ∧ (True ∧ p3))))) := by
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
theorem thm_5_vars_325918449980075333454000504199 : (p5 ∨ (p5 ∨ ((p3 ∧ ((((p1 ∨ False) ∨ ((p2 ∧ (p1 ∨ ((p1 ∧ False) → p4))) ∧ ((False ∧ False) ∧ p5))) → p1) → (p5 ∨ p1))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207646248252520748372609139904 : ((((p4 ∨ True) ∧ (p4 → p2)) → p5) → ((((p5 → p1) ∨ ((True ∧ ((p1 ∨ False) ∧ ((p4 → p2) ∧ p2))) ∧ (p3 → p2))) ∧ p2) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_151186544504654885589063958345 : ((((((True ∧ (p1 ∨ False)) → p5) ∨ (False ∧ p3)) ∧ (((p3 ∧ (p1 ∧ p5)) ∨ p1) ∧ (p2 ∨ False))) → p4) → (((True → p5) ∨ True) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_718689109549555498285466454731 : (((((True → p5) ∧ (True ∧ True)) ∨ (((p1 ∧ False) ∨ ((p4 ∧ p4) → p4)) → (p2 ∧ (((p2 ∨ p2) → p4) → ((p1 → p5) → p5))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_720652115902983194819959387317 : ((((((True → p5) ∨ True) → p5) → ((((p3 → ((((False ∨ (p3 ∧ False)) ∨ False) → p2) → p5)) ∨ p5) ∧ p3) ∨ ((False ∨ p5) → p5))) ∨ p5) ∧ True) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- One of the premise coincides with the conclusion.
    exact h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44495546253219543067147881655 : ((((((p3 ∨ p3) ∨ (p2 → p1)) → (True ∨ (p2 ∧ p2))) ∧ (((((False ∨ False) → p1) ∨ p4) ∧ ((p4 ∨ p2) ∨ False)) → p1)) → p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63942548216416550080513988081 : ((False ∨ ((((p3 ∧ True) ∧ (p1 → p5)) ∧ ((((p2 ∨ ((True ∧ p4) → p1)) ∨ (((p5 ∨ p1) ∨ p4) ∧ False)) → p2) ∨ True)) ∨ True)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_590024789927492867035219236497 : (((((((p2 ∧ (((p5 ∧ True) ∧ (p1 ∨ p4)) ∨ ((p1 ∧ p2) → False))) → True) → (((False → p1) ∧ (p4 ∨ p3)) ∨ p4)) → p4) ∧ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213160324557528716958075317303 : ((((p3 ∧ False) ∨ p3) ∧ False) ∨ ((True → True) ∧ ((((((p3 ∧ p5) → p1) ∧ p1) → p3) ∨ (p1 ∧ p3)) ∨ (p3 → (True ∨ (True ∨ p2)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164813518695533385943959355172 : ((((p2 → True) ∧ ((((((False ∨ (p1 ∨ p3)) ∧ False) → False) ∨ p1) → p4) ∧ p3)) ∨ p3) ∨ (p1 ∨ (((p5 ∧ p2) → p4) → (True ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_597111527190054390939617197747 : (((((p3 ∨ (p4 ∨ ((p3 ∨ p3) ∨ p5))) → ((p2 ∧ p4) → (((p4 ∧ p1) ∧ p5) ∨ (p4 ∨ ((False → False) ∨ (p5 → p5)))))) ∧ True) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Disjunctions on the left can always be decomposed.
        cases h9
        case inl h10 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h4
        case inr h11 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h4
      case inr h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h4
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_189295261528650096344095500695 : (((p5 ∨ True) → (((False ∨ p5) ∨ (p3 ∨ p2)) ∨ True)) ∧ ((True ∨ (p3 ∧ ((True ∧ (((p1 ∧ p1) ∨ p3) ∨ p1)) → p1))) ∨ (p1 → p2))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_618199376502866619488601526379 : (((((((p1 ∨ p5) → p3) ∧ p5) ∨ (p5 ∨ (((p2 → p3) ∨ (p1 ∨ (p2 ∧ True))) ∧ (((p2 ∧ p3) → p4) ∨ (p2 → p5))))) ∨ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231336017453232973365806712535 : (((True → p3) ∨ p5) → (p5 → ((((p3 ∧ ((p4 → (True ∧ p1)) ∧ p5)) → False) ∨ (p4 → (((False → (p5 ∧ p4)) ∨ True) → False))) ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137718399919565115201493840853 : ((p1 ∨ ((p2 ∧ p1) ∧ ((((p5 → ((p3 → ((True → True) → (p1 → p3))) ∧ True)) ∧ (p3 ∧ True)) ∨ p1) ∧ p2))) ∨ ((False ∧ p1) → p3)) := by
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
theorem thm_5_vars_336462667293273494747936683712 : (p1 → ((p1 → (((((((p2 ∨ False) → (p4 ∨ p3)) → (True ∨ True)) ∧ p1) ∨ (True → ((p3 ∧ p3) → p1))) → (p2 ∧ True)) ∧ p1)) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_75725331927521638322946337285 : (((((True → ((((p1 → p5) ∧ (p1 ∧ (p1 ∧ p4))) → (p2 ∨ p5)) → ((True → True) ∧ (p5 → p1)))) ∨ (False → p5)) ∨ True) → p2) → p2) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((True → ((((p1 → p5) ∧ (p1 ∧ (p1 ∧ p4))) → (p2 ∨ p5)) → ((True → True) ∧ (p5 → p1)))) ∨ (False → p5)) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_648347965888439480597341777768 : (((((((True ∧ False) ∧ ((((p2 ∨ ((True ∧ p2) → p2)) ∧ p2) ∧ (((False ∨ p3) → p2) ∧ True)) ∧ p5)) ∧ p1) ∨ p2) ∧ (True ∨ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_175901965272237554867902418957 : ((((False ∨ (p2 ∧ p4)) → (False ∨ (((p1 → False) ∨ p1) ∨ True))) ∨ p4) ∧ ((p2 ∨ ((p2 → True) ∧ ((p5 ∧ p4) ∨ (p4 → True)))) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166288032587607116393958390664 : ((p4 ∧ (((p3 → p2) ∨ (True ∧ ((p2 ∨ p5) ∧ ((p3 ∨ False) ∧ p3)))) → (p3 → p4))) ∨ (p3 → ((((True ∨ True) ∨ True) ∨ p1) ∨ p2))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_16850938925179457229734836044 : ((((p1 ∧ p4) ∧ (p4 → ((((p1 ∧ (p2 ∧ (p1 ∧ p2))) ∧ False) ∨ p3) ∨ (p4 ∨ (p4 ∧ (p3 ∨ p3)))))) ∨ ((True ∨ False) ∨ True)) ∧ True) := by
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
theorem thm_5_vars_305178210224790654037925470858 : (p1 ∨ (((p3 ∨ ((p4 → False) ∨ (p4 ∧ p5))) ∧ ((p3 → (p1 → ((p5 ∧ True) → p2))) ∨ (p2 → False))) ∨ (p3 → (p4 → (p4 → p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173639881718625282750377510577 : (((p4 → (((p5 → (True → (p5 ∨ True))) ∨ p3) ∨ (True ∧ (p3 ∧ p1)))) ∧ p3) → ((p4 → ((p5 ∨ p2) ∧ (p3 ∧ (p2 ∨ p2)))) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_239598461433777037425151378011 : ((p3 ∨ True) ∧ ((p3 ∧ ((True ∨ (True → (p4 ∨ False))) ∧ p2)) ∨ (((p4 → (p1 ∧ False)) → (p4 → p3)) ∨ (((False ∧ p2) → False) ∨ True)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_39390991086948512475524819381 : (((p3 ∧ (p4 → ((((p1 ∨ False) ∨ (p4 ∧ ((False ∧ p1) ∧ ((p1 ∨ True) → p3)))) ∧ ((False → True) ∧ p3)) ∧ (p5 → False)))) ∧ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134657804990271279474843583847 : ((((p1 ∧ (((p5 ∨ False) ∨ (p4 → (False ∨ p2))) ∨ True)) ∧ (((p3 ∨ (p3 ∧ p1)) → (p5 ∨ True)) → p3)) → False) ∨ (True ∨ (True ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_797078346534020596587877930539 : (((p1 → (((p2 ∨ (p2 → ((p3 ∨ (p5 ∧ False)) ∧ False))) ∧ (((p2 ∧ (True ∨ p1)) → ((p4 ∧ (False ∧ p5)) ∧ False)) ∨ p5)) ∧ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_20243118281487951585904224259 : ((((((p3 → True) ∧ p2) ∧ p3) ∧ ((False ∨ (True ∧ p4)) ∧ (True → p5))) ∨ (p2 → (p5 ∨ (p1 ∨ (p1 → (p4 ∨ (p1 ∨ p2))))))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193531608304310486200953986856 : (((p5 → p3) ∨ ((p2 → p2) → ((True → p3) ∧ p2))) → (((p1 → p4) ∨ p5) ∨ ((p5 ∨ ((p4 → True) ∧ (True → (p4 ∧ True)))) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
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
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232936134241783093857211160493 : ((p3 ∧ (p1 ∨ p2)) → (True → ((p5 ∨ (((True → p1) ∨ True) ∧ (((p2 → False) ∨ p1) ∨ ((p1 ∧ p5) ∧ (False ∨ p1))))) ∨ (p5 ∨ p3)))) := by
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
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_358146683030840026598495924059 : (p5 → (p2 ∨ (p3 → (p2 → (p5 ∧ (((((True ∨ (p2 ∨ p5)) ∨ (p3 ∨ p1)) ∨ False) → (p4 ∨ True)) ∧ (True ∨ (p3 ∨ (p5 ∧ p5))))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h4
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
        -- Disjunctions on the left can always be decomposed.
        cases h8
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
      cases h11
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_729630125231561799379565377933 : (((((True → False) ∨ p2) → ((True → (((p2 → p1) ∨ (p2 → (p5 ∨ False))) ∧ (False → (False → True)))) → ((p2 ∧ (p2 → p2)) ∨ p3))) ∨ p5) ∧ True) := by
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
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h4 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h5 := h3 h4
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h6
    -- Implications on the right can always be decomposed.
    intro h7
    -- One of the premise coincides with the conclusion.
    exact h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323993163947362658416739465017 : (p5 ∨ ((((p1 → p1) ∧ ((p5 ∧ p5) ∨ p4)) ∨ (p3 → ((p1 ∨ p1) ∨ True))) ∨ (p1 → ((p2 → (True ∧ (p3 ∨ (p3 ∧ p3)))) ∨ False)))) := by
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
theorem thm_5_vars_150698455988763013024654812589 : (((p5 → (p1 ∧ ((((True → (p3 ∧ True)) → ((p4 ∧ (p2 ∧ p1)) ∧ p4)) ∧ (True → p2)) ∧ p2))) ∧ p5) → (False ∨ ((p3 ∧ p4) → p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h7 : p5 := by
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h8 := h2 h7
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- We need to get the right conjuct of h9 based on <expert-advice>.
  let h10 := h9.right
  -- One of the premise coincides with the conclusion.
  exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308549416952531679950642732108 : (p2 ∨ ((((p3 ∨ (p5 → (p1 → (True ∨ p1)))) ∨ True) ∧ ((p2 ∧ (p1 ∨ (p4 → (((p5 → p1) ∨ p3) → p2)))) → (p4 ∨ False))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356013617124099913799102243220 : (p5 → (((((((p2 → p5) ∧ p4) → (p5 ∧ (p2 ∨ p5))) → p1) ∧ ((p2 ∧ p1) → (p4 ∧ False))) ∨ p3) ∨ ((p4 ∨ (p3 ∨ p2)) → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_596493882477352221992220178882 : ((((((((False ∨ p1) ∧ True) ∧ (p1 ∨ p3)) → p5) → (((p5 ∨ p4) → (p2 → ((((p5 ∨ p3) → True) ∨ p3) → p5))) ∨ p2)) ∧ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177875932454044696401448169914 : (((((((True ∨ (p5 ∧ False)) ∨ (p3 ∨ False)) ∧ p3) → p1) → p1) ∨ True) ∨ (p4 ∨ ((p3 ∨ (((p1 ∧ p1) → p3) ∧ p1)) ∨ (False ∧ p4)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_595940107659955437069399084236 : ((((((p4 ∨ p4) ∨ ((p1 ∧ p1) → (True ∧ (p2 ∧ False)))) ∨ ((p1 ∨ (p2 ∧ (p5 → (p4 ∧ ((False ∧ True) → p2))))) → p2)) ∧ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233322128721272766671962393512 : ((True ∨ (False → False)) → (((p5 → (True ∧ (True ∧ ((p4 ∨ p5) ∧ True)))) → (True → ((p5 ∨ True) ∧ False))) ∨ (False ∨ ((False → False) ∨ p3)))) := by
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
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342172232618575782342569278223 : (p2 → ((False ∧ ((p3 ∧ (p5 → ((p3 ∨ ((p1 → p5) ∧ False)) ∨ (p2 ∨ (True ∨ (p4 → False)))))) ∨ p1)) ∨ ((True ∨ False) → (True ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- False on the left can always be used.
    apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214808393135159864783400332217 : (((p2 ∨ p5) ∨ (p4 ∨ p4)) ∨ (p1 ∨ (((p3 → False) ∨ ((p1 → True) ∨ (p3 ∧ (p4 → True)))) ∧ ((True ∨ (p4 ∨ p4)) ∨ (p3 ∧ p3))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317813556309798907350113381848 : (p4 ∨ ((((p1 → p2) ∧ (True ∧ (p5 ∨ p5))) → ((((((p3 ∧ True) ∧ p1) ∨ (p1 ∨ p3)) ∨ (p4 ∨ p1)) ∧ p4) → (p5 → False))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_669354787376197712364567016395 : (((((p1 ∧ (((True → p2) ∧ ((True ∧ (p3 ∨ (p4 ∧ p2))) ∨ (True ∧ (p5 ∨ True)))) ∧ p3)) ∧ (p2 ∨ p4)) ∨ ((p1 ∨ True) ∨ p5)) ∨ p4) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168429714782770914237462365435 : (((False ∨ p4) → (p1 → (((p3 ∧ p3) ∨ p1) → (False ∧ (((p4 ∨ p4) ∧ False) ∧ False))))) → ((True → p4) ∨ (((p2 → p2) ∨ True) ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39449315653860524577440199736 : (((p5 ∧ (((((False ∨ False) → False) ∧ ((p2 ∨ True) ∨ p5)) → ((p4 → p4) ∧ p3)) → ((p4 → ((False → False) ∨ True)) ∧ p1))) ∧ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187099541561454058992857364531 : (((p5 → p5) ∧ (p5 ∧ ((((p5 → p3) ∧ p5) ∧ p3) ∧ p4))) → ((((p1 → (p5 → p2)) ∧ p2) ∧ (p2 ∧ p1)) ∨ ((p4 ∧ p3) ∨ p1))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- Conjunctions on the left can always be decomposed.
  let h10 := h8.left
  let h11 := h8.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h7
  -- One of the premise coincides with the conclusion.
  exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147095868064849085606755291937 : ((((p5 ∨ (p3 ∨ p3)) ∧ (p3 ∨ (((False → (p1 ∧ p4)) ∨ (p2 ∨ (p4 → p1))) ∨ (True ∨ p5)))) ∧ p3) ∨ (True ∨ (False ∨ (True ∧ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205178020532912469759960310157 : (((p1 ∨ (p4 ∨ p3)) ∧ (p2 → p4)) ∨ (((p2 → False) ∨ ((p5 ∨ (True ∨ (p2 ∨ (False ∨ p5)))) ∨ (p2 ∧ (p2 ∨ (p2 ∧ False))))) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136904723062472956076920351310 : (((p5 ∨ p4) ∨ (((p4 ∨ p1) ∨ (p1 ∧ ((False ∨ (p1 → ((True ∧ p5) ∧ ((p4 ∨ True) ∧ p4)))) ∨ p4))) ∧ True)) ∨ (p2 → (False → False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_195707099909858816047795776823 : (((True ∨ p3) ∨ ((p4 ∨ p2) ∧ (p3 ∨ True))) ∧ (p1 ∨ ((p5 ∨ p4) → (False ∨ (((p1 ∧ (p5 ∨ True)) → False) ∨ (p1 → (False → p2))))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
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
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- Implications on the right can always be decomposed.
    intro h7
    -- False on the left can always be used.
    apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172891625211401006455713551049 : ((p1 ∧ (True → ((((p5 → (p5 → True)) ∨ (False → p5)) → p2) ∧ (p1 ∨ p2)))) ∨ (((p1 → p5) → p5) → ((p2 ∨ True) ∨ (True ∧ p1)))) := by
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
theorem thm_5_vars_607923090083564774981403480861 : (((((p1 → (((p4 ∧ False) ∨ ((p3 → True) → (((p2 ∧ ((True → p4) → p1)) ∧ p5) ∨ (False ∧ p3)))) ∧ (p4 ∨ p4))) ∧ p2) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234024652115892519283721069288 : ((p5 ∨ (True → True)) → (p3 → ((((p5 ∨ (p5 ∨ (((p4 → p3) ∧ True) → False))) ∨ p2) ∧ (p3 ∧ ((p1 → False) ∨ p2))) ∨ (True ∨ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233081340312458763815468643139 : ((p4 ∧ (True → p1)) → ((p3 ∧ False) ∨ ((((((False ∧ (p4 → p4)) ∨ p4) → (True → ((p4 ∨ p1) → p2))) ∨ (p1 ∧ p1)) ∨ p2) ∧ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- One of the premise coincides with the conclusion.
  exact h5
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h6 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h7 := h3 h6
  -- One of the premise coincides with the conclusion.
  exact h7
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h8 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h9 := h3 h8
  -- One of the premise coincides with the conclusion.
  exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174248293144343065576871831025 : (((False → ((p3 ∧ (p4 ∧ (((p2 ∧ p4) → True) ∨ p3))) ∨ False)) → (p3 ∧ False)) → (p2 ∧ ((p5 ∨ p3) ∨ ((False ∧ p5) ∨ (p2 ∨ p3))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (False → ((p3 ∧ (p4 ∧ (((p2 ∧ p4) → True) ∨ p3))) ∨ False)) := by
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
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h6 : (False → ((p3 ∧ (p4 ∧ (((p2 ∧ p4) → True) ∨ p3))) ∨ False)) := by
    -- Implications on the right can always be decomposed.
    intro h7
    -- False on the left can always be used.
    apply False.elim h7
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h8 := h1 h6
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- False on the left can always be used.
  apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345339242067907556534782212230 : (p3 → ((((True ∨ True) → (p4 → (((False → (p2 ∧ ((True ∧ True) → False))) ∨ (p1 → p1)) → ((True ∧ (p2 ∨ False)) → False)))) ∧ False) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138744493950413487285326353741 : (((((p3 ∨ p4) ∨ p2) ∧ ((p4 → ((p3 ∨ p3) ∨ p2)) → (((p3 ∨ ((p5 ∧ p2) ∨ p5)) ∨ p5) → p4))) ∧ p2) → ((p5 → p4) ∨ p4)) := by
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
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h8 : (p4 → ((p3 ∨ p3) ∨ p2)) := by
        -- Implications on the right can always be decomposed.
        intro h9
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h3
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h10 := h5 h8
      -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
      have h11 : ((p3 ∨ ((p5 ∧ p2) ∨ p5)) ∨ p5) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h7
      -- We have shown the premise of h10, we can now drive its conclusion.
      let h12 := h10 h11
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h12
    case inr h13 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h13
  case inr h14 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h15
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h16 : (p4 → ((p3 ∨ p3) ∨ p2)) := by
      -- Implications on the right can always be decomposed.
      intro h17
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h18 := h5 h16
    -- We want to use the implication h18 based on <expert-advice>. So we show its premise.
    have h19 : ((p3 ∨ ((p5 ∧ p2) ∨ p5)) ∨ p5) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h15
    -- We have shown the premise of h18, we can now drive its conclusion.
    let h20 := h18 h19
    -- One of the premise coincides with the conclusion.
    exact h20



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68674797033612328929455960343 : ((p4 → ((p5 → (((False ∨ ((True → (p3 ∨ ((p3 ∨ (p4 ∧ p2)) ∨ (p2 ∨ p2)))) → True)) ∧ True) ∨ ((p5 ∨ p4) → False))) → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48990051075444319929066957284 : (((((p2 ∨ p5) → (((p3 → (((True → p4) → (False ∨ p1)) → (p2 ∧ True))) → False) ∧ (p1 → p2))) ∨ p5) ∨ ((True ∨ True) ∨ False)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184071891522429132535488120585 : ((((p1 → (p5 → (p5 ∧ p2))) ∧ (False ∧ (p2 → p2))) ∨ p3) ∨ ((((p4 ∧ ((p2 ∨ False) → (True ∨ False))) ∧ p2) → p3) ∨ (p2 → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_731813656092889746211048920238 : ((((p4 → (True ∧ p4)) → (p1 → ((p1 ∧ (True ∧ p3)) → ((True ∧ (p1 ∧ p5)) ∧ (p1 ∧ ((False ∧ ((p2 → p1) → True)) ∧ p1)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_637661270616414518982124129744 : ((((((((p2 → (p5 ∨ False)) ∨ p4) → (False ∧ p1)) ∧ p2) → ((True ∨ (p1 ∨ (p5 → p5))) → ((False ∨ (p3 → True)) ∨ p4))) → p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134762441789574262653136377886 : ((((p3 ∨ p5) → (((p1 ∨ (False ∧ (p1 ∨ p1))) ∨ (p5 → (p4 → (p3 → p5)))) ∨ (False ∨ (p2 → p2)))) → p3) ∨ ((p1 → True) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147565700936541703988585085820 : (((((p3 → (((True ∨ (True ∨ p4)) → ((p4 ∨ (False → p4)) → p4)) → p2)) ∨ (p3 ∨ p2)) ∧ p1) → p2) ∨ ((True ∧ (p4 → p4)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166717488609271432038011295019 : ((p3 → (((p2 ∧ p3) ∨ p5) → (((p2 → (p1 → (p4 ∨ (p5 ∨ p5)))) → p4) → p4))) ∨ ((p4 → p5) ∨ (False → ((True ∧ p3) → p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135785807777340429095766820545 : ((((False ∨ ((True ∧ (p1 ∨ p3)) ∧ (p2 ∧ p1))) ∨ ((p1 → True) ∨ p1)) → ((p3 ∧ p3) ∨ (True ∧ (p3 → p3)))) ∨ (p5 ∨ (p4 ∧ p5))) := by
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
      -- False on the left can always be used.
      apply False.elim h3
    case inr h4 =>
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- Conjunctions on the left can always be decomposed.
      let h7 := h5.left
      let h8 := h5.right
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Conjunctions on the left can always be decomposed.
        let h10 := h6.left
        let h11 := h6.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- True on the right can always be proven directly.
        apply True.intro
        -- Implications on the right can always be decomposed.
        intro h12
        -- One of the premise coincides with the conclusion.
        exact h12
      case inr h13 =>
        -- Conjunctions on the left can always be decomposed.
        let h14 := h6.left
        let h15 := h6.right
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h13
        -- One of the premise coincides with the conclusion.
        exact h13
  case inr h16 =>
    -- Disjunctions on the left can always be decomposed.
    cases h16
    case inl h17 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- Implications on the right can always be decomposed.
      intro h18
      -- One of the premise coincides with the conclusion.
      exact h18
    case inr h19 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- Implications on the right can always be decomposed.
      intro h20
      -- One of the premise coincides with the conclusion.
      exact h20



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341710226240671398816904251543 : (p2 → ((((p1 ∧ True) → ((p5 → True) ∧ ((p1 ∧ p5) ∧ ((True → p3) ∨ True)))) ∨ ((p4 ∧ (p2 ∨ p2)) → (p1 ∧ p1))) ∨ (False ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_768701018651494088500989263335 : (((p5 ∧ (((p2 → p4) → ((p1 ∧ p2) → (p3 ∧ (p5 ∨ p1)))) ∨ ((((p2 ∨ ((p1 → (True ∧ False)) ∧ p5)) ∧ True) ∧ p4) → p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305039480902867868306198277018 : (p1 ∨ ((p4 → ((((False ∨ ((False ∧ p3) ∧ (p2 → (p4 → p2)))) ∧ False) ∧ p4) ∧ ((p2 ∧ p4) ∧ (p3 → p2)))) ∨ (p3 → (False ∨ True)))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_216682587261153697121879559079 : ((((p2 → p5) ∨ p5) ∧ p2) → (((((p5 ∨ False) ∨ True) → p3) ∧ (False → (((p2 ∨ (p1 → p4)) → False) ∨ (p3 → (p4 ∨ p5))))) ∨ p2)) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53791150451955480157303252816 : ((((((((p5 → p1) ∨ p1) ∨ p1) ∨ False) ∨ p1) → p1) ∨ ((p2 ∨ (p3 ∧ ((p3 → ((p3 → p2) ∨ p3)) ∨ p3))) ∧ (p2 ∨ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299263011976720123571683074728 : (False ∨ ((((p5 → p4) → (True → (((p2 ∧ (((p2 ∨ p2) ∧ True) ∨ (False ∨ p2))) ∨ p4) → False))) → ((p4 ∨ p2) → (p1 → p2))) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h5 : (p5 → p4) := by
      -- Implications on the right can always be decomposed.
      intro h6
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h7 := h1 h5
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h8 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h9 := h7 h8
    -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
    have h10 : ((p2 ∧ (((p2 ∨ p2) ∧ True) ∨ (False ∨ p2))) ∨ p4) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h9, we can now drive its conclusion.
    let h11 := h9 h10
    -- False on the left can always be used.
    apply False.elim h11
  case inr h12 =>
    -- One of the premise coincides with the conclusion.
    exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_329146652661069485285975575087 : (True → (((p4 ∧ (p5 → p1)) ∧ True) → ((((((p1 ∧ True) ∧ True) ∧ p5) ∧ False) ∨ (True → p1)) → ((p2 ∧ (p4 → False)) ∨ (False → p2))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
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
    let h11 := h9.left
    let h12 := h9.right
    -- False on the left can always be used.
    apply False.elim h6
  case inr h13 =>
    -- Conjunctions on the left can always be decomposed.
    let h14 := h2.left
    let h15 := h2.right
    -- Conjunctions on the left can always be decomposed.
    let h16 := h14.left
    let h17 := h14.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h18
    -- False on the left can always be used.
    apply False.elim h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173157423990981359834112125546 : ((p3 ∨ (p3 ∧ ((((p1 ∧ p1) ∨ p2) ∧ (p3 → p5)) ∨ ((p5 ∧ p2) ∧ False)))) ∨ ((((p2 ∧ (False → p1)) ∧ p5) ∧ p3) → (True ∨ p5))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_81968307498492225478551527072 : (((((p5 → (p4 ∧ (p5 ∧ (False ∧ (p1 → p4))))) ∨ p2) → (((p5 ∨ p3) ∧ (p3 ∨ p5)) ∨ (True ∨ p1))) → ((True ∨ p1) ∧ p1)) → p1) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p5 → (p4 ∧ (p5 ∧ (False ∧ (p1 → p4))))) ∨ p2) → (((p5 ∨ p3) ∧ (p3 ∨ p5)) ∨ (True ∨ p1))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h2
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174253864301379775448193910858 : ((((((p4 ∨ (p4 → p5)) ∨ (p3 → p3)) ∧ p1) ∧ p5) ∧ ((True ∨ p1) → p3)) → ((p3 → (p5 → ((False → p1) ∨ p2))) ∧ (p3 ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h12
      -- False on the left can always be used.
      apply False.elim h12
    case inr h13 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h14
      -- False on the left can always be used.
      apply False.elim h14
  case inr h15 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h16
    -- False on the left can always be used.
    apply False.elim h16
  -- Conjunctions on the left can always be decomposed.
  let h17 := h1.left
  let h18 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h19 := h17.left
  let h20 := h17.right
  -- Conjunctions on the left can always be decomposed.
  let h21 := h19.left
  let h22 := h19.right
  -- Disjunctions on the left can always be decomposed.
  cases h21
  case inl h23 =>
    -- Disjunctions on the left can always be decomposed.
    cases h23
    case inl h24 =>
      -- We want to use the implication h18 based on <expert-advice>. So we show its premise.
      have h25 : (True ∨ p1) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h18, we can now drive its conclusion.
      let h26 := h18 h25
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h26
    case inr h27 =>
      -- We want to use the implication h18 based on <expert-advice>. So we show its premise.
      have h28 : (True ∨ p1) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h18, we can now drive its conclusion.
      let h29 := h18 h28
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h29
  case inr h30 =>
    -- We want to use the implication h18 based on <expert-advice>. So we show its premise.
    have h31 : (True ∨ p1) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h18, we can now drive its conclusion.
    let h32 := h18 h31
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h32



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230849371550515625359489212847 : (((p1 ∧ p1) ∨ p2) → ((p2 → ((((((p3 → False) ∨ p3) ∧ p3) → ((p5 ∧ p1) ∨ p5)) → p1) ∧ ((p5 ∧ p1) → (False → p2)))) ∨ True)) := by
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
theorem thm_5_vars_149921566787769567827618491304 : ((p3 ∨ ((((p2 ∨ ((((True ∨ p3) ∨ (p3 ∧ p2)) ∨ (False ∨ p1)) ∧ p5)) ∨ False) → p3) → (False ∧ p5))) ∨ ((p4 ∧ True) ∨ (True ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_212788238267961510410820005788 : ((p1 → (p3 ∨ (p3 ∨ p1))) ∧ (p4 → (p4 ∧ (((p1 → (((((p2 → True) → (p1 ∧ False)) ∧ True) ∧ p3) ∧ True)) ∧ p2) ∨ (False → p2))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_760046124154453979126541273002 : (((p2 ∧ (((p2 ∧ p4) ∨ False) ∧ (p3 ∧ ((p1 ∧ (p2 ∧ (((p3 ∧ p4) ∨ (p3 ∧ ((p1 → p4) ∨ (p3 ∨ p1)))) ∨ p1))) ∨ False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_765062135864925468026317183309 : (((p4 ∧ (((p2 → ((p2 ∨ (((True → False) ∨ (p1 ∨ p2)) ∧ (p3 ∨ p2))) → p3)) ∨ ((p2 → (True ∨ p1)) ∨ p1)) ∧ (p3 ∧ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259762817765619782806747774628 : ((p1 → p2) → ((p3 → ((p5 ∨ p5) → (True → False))) → (((p2 → p4) ∨ ((p2 → p1) ∨ p2)) ∨ ((p4 ∧ p3) ∨ (True ∨ (True ∨ p2)))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66118644269548075481429058724 : ((p5 ∨ ((p1 ∨ (p4 ∨ (p1 ∧ (p3 → ((p5 → ((((False ∧ p3) ∧ (p1 → p2)) ∨ (p5 → (p4 ∧ True))) → True)) ∧ p4))))) → p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



