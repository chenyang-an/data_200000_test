variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43173753898328020358163977274 : (((((p3 → (False ∨ p1)) → ((((True ∧ p3) → ((False ∧ (p2 → ((True ∧ p4) ∨ p3))) ∨ p4)) ∧ (p2 ∧ p4)) ∨ p1)) ∧ p4) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164897292138508412006539920778 : (((((((((False → (p2 ∧ True)) → p1) ∨ p1) ∨ (p1 ∧ p3)) ∧ p1) ∨ p2) ∧ True) → False) ∨ (((p2 ∧ p3) → p5) ∨ (p3 ∨ (False → p5)))) := by
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
theorem thm_5_vars_140370722507377485110500802217 : ((((True → (p5 ∧ True)) ∨ ((True ∨ ((p1 → p4) ∧ (p4 ∨ True))) ∨ ((p4 → p3) ∨ p2))) ∨ ((p5 ∧ True) ∨ False)) → ((p1 ∨ True) ∨ p4)) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h5 =>
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
          -- Conjunctions on the left can always be decomposed.
          let h8 := h7.left
          let h9 := h7.right
          -- Disjunctions on the left can always be decomposed.
          cases h9
          case inl h10 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h11 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
      case inr h12 =>
        -- Disjunctions on the left can always be decomposed.
        cases h12
        case inl h13 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h14 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
  case inr h15 =>
    -- Disjunctions on the left can always be decomposed.
    cases h15
    case inl h16 =>
      -- Conjunctions on the left can always be decomposed.
      let h17 := h16.left
      let h18 := h16.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h19 =>
      -- False on the left can always be used.
      apply False.elim h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309311937010549904510222536960 : (p2 ∨ ((((p1 → (((p2 ∧ (p3 → p2)) ∨ (True → p2)) → p5)) ∨ ((p1 ∧ ((True ∧ (p3 → p3)) → False)) ∧ True)) ∨ p2) ∨ (p4 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319480522164004801696559596468 : (p4 ∨ (((((False ∧ p4) ∧ (p1 ∨ (p2 ∧ (False → p5)))) ∧ p2) → False) → (p5 ∨ (p2 → ((p2 ∨ p3) ∨ ((p3 ∨ True) ∧ (False → p5))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55806134469748159909455970087 : ((((False ∧ p1) → (True ∧ p2)) ∧ (p4 ∨ ((True → (((False ∨ p2) → p5) ∧ ((p3 → p2) ∨ p1))) ∧ (((p4 ∧ p2) → p5) → False)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68495095136037280652306104232 : ((p3 → (p1 ∨ (p4 → (False ∨ ((p2 ∨ p4) → (((p4 ∨ (False ∨ p3)) → p1) ∨ ((p5 → ((p1 ∧ False) ∨ (p1 ∨ True))) ∨ False))))))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h7
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50385917883932894240597588786 : ((((p2 ∧ p4) ∨ ((p3 ∧ False) ∨ (p5 → (p2 → (p4 ∨ ((True → ((True ∨ p5) ∨ p2)) ∨ p5)))))) ∨ ((True ∧ (False → p5)) ∨ False)) ∨ p5) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49509786700297394149504940849 : (((((((p2 ∧ p3) → (p1 ∧ (p3 → (((False → (False ∧ p3)) ∨ p2) ∨ p2)))) ∨ p1) ∧ p4) ∧ (p2 ∨ p5)) → (p5 ∧ (p2 ∧ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244757920511528732870287406783 : ((p1 ∧ False) ∨ ((p3 ∨ (((p5 ∧ p3) ∧ (False ∧ (p2 ∧ (False ∧ p4)))) ∧ p4)) ∨ (((False ∧ (p2 ∧ p1)) ∧ (True ∧ p2)) → (p4 ∨ p3)))) := by
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
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62803745362254205747425538369 : ((p4 ∧ (((p4 ∧ ((False ∨ (p5 → ((True ∧ p1) ∧ False))) → p2)) ∧ (p1 ∧ p3)) ∨ (p3 → (p5 ∨ (p1 → ((p3 ∧ p4) → p5)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_751476536232493585945457275333 : (((True ∧ (True ∧ (((p3 ∨ (((p1 ∧ p4) ∨ False) ∨ (False ∧ (False ∨ (((p4 → (p2 ∨ (p3 → p3))) ∨ p5) ∧ p5))))) ∧ p1) ∨ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_778086820641023824589424106117 : (((p1 ∨ ((p2 → p1) ∧ (p4 ∧ (((p5 ∧ (False → p1)) ∨ ((((p4 ∧ p1) ∨ (True ∨ False)) ∧ (True ∨ p2)) ∧ (True ∧ p5))) ∨ p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161316944412276704301077743258 : ((True ∧ ((((p2 ∨ (False ∧ (p2 → (p4 → p2)))) ∧ p3) → p1) ∧ ((True ∨ p3) ∧ (True ∨ True)))) → ((((p4 ∨ p4) ∨ p2) → p3) ∨ True)) := by
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
  cases h6
  case inl h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
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
    cases h7
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_788083655548047607170166266228 : (((p5 ∨ (((p1 → (((p5 ∨ p1) → ((p5 → (((p1 → False) ∨ True) ∧ ((True ∨ p1) ∨ (False ∨ p2)))) ∧ False)) ∧ False)) → p4) ∧ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231052831812622176266014843430 : (((True ∨ p2) ∨ p3) → ((p3 ∧ ((p4 ∨ ((((True → p1) ∨ False) → p1) ∨ (p4 → p2))) ∨ p3)) → ((p5 ∧ p1) ∨ (True → (p1 → True))))) := by
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
    cases h5
    case inl h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h7 =>
        -- Disjunctions on the left can always be decomposed.
        cases h7
        case inl h8 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h9
          -- Implications on the right can always be decomposed.
          intro h10
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h11 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h12
          -- Implications on the right can always be decomposed.
          intro h13
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h14 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h15
        -- Implications on the right can always be decomposed.
        intro h16
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h17 =>
      -- Disjunctions on the left can always be decomposed.
      cases h17
      case inl h18 =>
        -- Disjunctions on the left can always be decomposed.
        cases h1
        case inl h19 =>
          -- Disjunctions on the left can always be decomposed.
          cases h19
          case inl h20 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h21
            -- Implications on the right can always be decomposed.
            intro h22
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h23 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h24
            -- Implications on the right can always be decomposed.
            intro h25
            -- True on the right can always be proven directly.
            apply True.intro
        case inr h26 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h27
          -- Implications on the right can always be decomposed.
          intro h28
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h29 =>
        -- Disjunctions on the left can always be decomposed.
        cases h1
        case inl h30 =>
          -- Disjunctions on the left can always be decomposed.
          cases h30
          case inl h31 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h32
            -- Implications on the right can always be decomposed.
            intro h33
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h34 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h35
            -- Implications on the right can always be decomposed.
            intro h36
            -- True on the right can always be proven directly.
            apply True.intro
        case inr h37 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h38
          -- Implications on the right can always be decomposed.
          intro h39
          -- True on the right can always be proven directly.
          apply True.intro
  case inr h40 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h41 =>
      -- Disjunctions on the left can always be decomposed.
      cases h41
      case inl h42 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h43
        -- Implications on the right can always be decomposed.
        intro h44
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h45 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h46
        -- Implications on the right can always be decomposed.
        intro h47
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h48 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h49
      -- Implications on the right can always be decomposed.
      intro h50
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_175349357871061644117268565392 : ((p5 ∨ ((((p5 ∧ (True ∧ p5)) ∨ p5) ∧ (p1 ∨ True)) ∨ ((p4 → p5) ∧ p3))) → (False ∨ ((p1 → (False ∧ p3)) → ((p1 ∧ p3) → p2)))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h7 : p1 := by
      -- One of the premise coincides with the conclusion.
      exact h5
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h8 := h3 h7
    -- We need to get the left conjuct of h8 based on <expert-advice>.
    let h9 := h8.left
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
      cases h12
      case inl h14 =>
        -- Conjunctions on the left can always be decomposed.
        let h15 := h14.left
        let h16 := h14.right
        -- Conjunctions on the left can always be decomposed.
        let h17 := h16.left
        let h18 := h16.right
        -- Disjunctions on the left can always be decomposed.
        cases h13
        case inl h19 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h20
          -- Implications on the right can always be decomposed.
          intro h21
          -- Conjunctions on the left can always be decomposed.
          let h22 := h21.left
          let h23 := h21.right
          -- We want to use the implication h20 based on <expert-advice>. So we show its premise.
          have h24 : p1 := by
            -- One of the premise coincides with the conclusion.
            exact h22
          -- We have shown the premise of h20, we can now drive its conclusion.
          let h25 := h20 h24
          -- We need to get the left conjuct of h25 based on <expert-advice>.
          let h26 := h25.left
          -- False on the left can always be used.
          apply False.elim h26
        case inr h27 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h28
          -- Implications on the right can always be decomposed.
          intro h29
          -- Conjunctions on the left can always be decomposed.
          let h30 := h29.left
          let h31 := h29.right
          -- We want to use the implication h28 based on <expert-advice>. So we show its premise.
          have h32 : p1 := by
            -- One of the premise coincides with the conclusion.
            exact h30
          -- We have shown the premise of h28, we can now drive its conclusion.
          let h33 := h28 h32
          -- We need to get the left conjuct of h33 based on <expert-advice>.
          let h34 := h33.left
          -- False on the left can always be used.
          apply False.elim h34
      case inr h35 =>
        -- Disjunctions on the left can always be decomposed.
        cases h13
        case inl h36 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h37
          -- Implications on the right can always be decomposed.
          intro h38
          -- Conjunctions on the left can always be decomposed.
          let h39 := h38.left
          let h40 := h38.right
          -- We want to use the implication h37 based on <expert-advice>. So we show its premise.
          have h41 : p1 := by
            -- One of the premise coincides with the conclusion.
            exact h39
          -- We have shown the premise of h37, we can now drive its conclusion.
          let h42 := h37 h41
          -- We need to get the left conjuct of h42 based on <expert-advice>.
          let h43 := h42.left
          -- False on the left can always be used.
          apply False.elim h43
        case inr h44 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h45
          -- Implications on the right can always be decomposed.
          intro h46
          -- Conjunctions on the left can always be decomposed.
          let h47 := h46.left
          let h48 := h46.right
          -- We want to use the implication h45 based on <expert-advice>. So we show its premise.
          have h49 : p1 := by
            -- One of the premise coincides with the conclusion.
            exact h47
          -- We have shown the premise of h45, we can now drive its conclusion.
          let h50 := h45 h49
          -- We need to get the left conjuct of h50 based on <expert-advice>.
          let h51 := h50.left
          -- False on the left can always be used.
          apply False.elim h51
    case inr h52 =>
      -- Conjunctions on the left can always be decomposed.
      let h53 := h52.left
      let h54 := h52.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h55
      -- Implications on the right can always be decomposed.
      intro h56
      -- Conjunctions on the left can always be decomposed.
      let h57 := h56.left
      let h58 := h56.right
      -- We want to use the implication h55 based on <expert-advice>. So we show its premise.
      have h59 : p1 := by
        -- One of the premise coincides with the conclusion.
        exact h57
      -- We have shown the premise of h55, we can now drive its conclusion.
      let h60 := h55 h59
      -- We need to get the left conjuct of h60 based on <expert-advice>.
      let h61 := h60.left
      -- False on the left can always be used.
      apply False.elim h61



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1570506687325284423729481356 : ((p4 → ((p2 ∨ ((((p3 ∨ (p5 ∨ (p4 ∧ ((p1 ∧ p2) ∨ p3)))) ∨ p1) ∨ p1) ∨ True)) ∨ ((p5 ∨ p4) → p1))) ∨ (p4 → False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_621012013721259772031002016728 : (((((False → False) → (True → ((((((p3 ∧ (False ∧ (((p2 ∧ p2) ∨ p3) ∨ p2))) ∨ True) → p5) ∧ (False ∨ p5)) → p3) ∧ p2))) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_683515255388975255435122391514 : ((((p4 → ((((p1 → p5) ∧ p1) ∧ ((p3 ∧ True) ∨ p4)) ∧ ((p5 ∧ p4) → (p1 ∧ p4)))) ∧ (p1 ∧ ((True → p5) ∧ (p4 → p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164706726767549528562147005435 : ((((p2 ∧ (((p3 ∧ (False ∨ p1)) ∧ (p5 ∧ p4)) ∧ ((p1 → p3) ∧ p3))) ∨ p5) ∨ p2) ∨ ((True ∨ (p5 → ((True → True) ∨ p1))) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160935691296187534201844314778 : (((True → ((p1 → p5) ∧ p2)) → (((p2 ∧ (p2 → p4)) ∨ False) → ((False ∨ p2) ∨ (False → p2)))) → ((p3 ∨ p1) ∨ (p3 → (p2 ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322201616462399127188712084184 : (p5 ∨ (((((((p4 → (((True ∧ (False ∨ False)) → (False ∨ True)) ∨ p3)) → True) ∧ True) → (p5 ∧ (p2 → (p3 ∧ True)))) ∨ p4) ∧ True) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_668644819255440797789065413787 : (((((p4 ∨ ((((False ∨ p2) ∧ True) ∨ False) → ((p5 ∨ (((False ∨ p3) → (p4 ∧ p2)) ∨ False)) ∧ False))) ∧ True) ∨ (p1 → (False → p1))) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46917110052874322025180192883 : (((((((False → (p4 ∧ p3)) ∧ p1) ∧ (p4 ∨ False)) → ((((p2 → p3) ∨ (p2 ∨ True)) ∨ (p5 → p2)) → False)) ∨ p2) ∨ (True ∨ False)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137160417213901662367779799964 : ((False ∧ ((((p2 ∧ (p4 ∨ p4)) → ((p4 ∨ p1) ∧ (False ∨ (((p3 ∧ p3) ∧ p2) → (True ∧ p2))))) ∨ p2) → p3)) ∨ ((p3 → p3) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_679051833151280336248600636761 : ((((False ∨ (False ∧ (p1 → (((p4 → (p5 → False)) ∧ False) ∨ (True ∧ (((p4 ∧ p2) ∧ p3) → p1)))))) ∨ (p1 ∧ ((p2 → p2) ∨ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_751108868125776071786360485881 : (((True ∧ ((p3 → (p2 ∧ (p5 → p5))) → (((p4 → (True ∨ ((p4 ∧ (p2 → False)) ∧ (((p5 ∧ True) ∧ True) ∧ p3)))) → False) → p1))) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (p4 → (True ∨ ((p4 ∧ (p2 → False)) ∧ (((p5 ∧ True) ∧ True) ∧ p3)))) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h3
  -- False on the left can always be used.
  apply False.elim h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158202925717628606889592790957 : ((((True ∨ p1) ∨ p5) ∧ ((p3 ∨ (p3 ∨ (((p4 → (p2 ∨ p5)) ∨ p4) ∧ p1))) ∧ (True → p5))) ∨ (p4 → (((p4 → p2) → p2) ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : p4 := by
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_606273443652981570034692565225 : ((((((p4 ∨ ((((p2 ∨ False) ∨ (((p1 → p4) ∨ (True ∨ True)) ∧ ((p1 ∧ (p2 ∧ p1)) ∨ p2))) ∧ False) ∧ p5)) ∧ p2) ∧ p2) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171716724272875354545882648179 : (((((((p4 → (False ∨ (p2 → (p1 → p3)))) → False) ∧ False) → p4) ∧ True) → False) ∨ ((True ∨ (p4 ∨ ((p5 → p1) → p3))) → (p1 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208637870083839560260286687373 : ((True ∧ ((False ∨ p3) ∨ (True ∨ p5))) → ((((p2 ∧ (p3 ∨ (p2 ∨ p3))) ∧ True) → False) ∨ ((p2 → ((p3 ∧ p5) → (p5 ∨ False))) ∨ p5))) := by
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
      -- False on the left can always be used.
      apply False.elim h5
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h7
      -- Implications on the right can always be decomposed.
      intro h8
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h10
  case inr h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h13
      -- Implications on the right can always be decomposed.
      intro h14
      -- Conjunctions on the left can always be decomposed.
      let h15 := h14.left
      let h16 := h14.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h16
    case inr h17 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65728224895242677826869582968 : ((p4 ∨ (((p5 ∨ (p3 ∨ p3)) ∨ ((p4 ∨ (((((p5 → True) ∧ True) ∨ p1) ∧ (p4 → True)) ∨ p3)) ∨ (p1 → p1))) → (p5 → p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207354405506884811346700233250 : ((((p3 ∧ True) → (p4 ∧ p4)) ∨ p1) → ((((p3 → (False ∨ p4)) ∧ (p1 ∨ (p5 → p4))) → (((p5 ∧ p3) ∨ p5) ∨ False)) ∨ (p1 ∨ True))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304857461411370975289833181318 : (p1 ∨ ((((p1 ∧ (p1 ∨ p4)) → False) ∧ (((p1 ∨ (True → p2)) ∨ (p4 → (p3 → (p4 ∧ ((p4 ∨ p1) → p5))))) ∧ p1)) → (p1 ∧ p3))) := by
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
  let h4 := h3.left
  let h5 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h8 =>
      -- One of the premise coincides with the conclusion.
      exact h5
  case inr h9 =>
    -- One of the premise coincides with the conclusion.
    exact h5
  -- Conjunctions on the left can always be decomposed.
  let h10 := h1.left
  let h11 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h12 := h11.left
  let h13 := h11.right
  -- Disjunctions on the left can always be decomposed.
  cases h12
  case inl h14 =>
    -- Disjunctions on the left can always be decomposed.
    cases h14
    case inl h15 =>
      -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
      have h16 : (p1 ∧ (p1 ∨ p4)) := by
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h13
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h13
      -- We have shown the premise of h10, we can now drive its conclusion.
      let h17 := h10 h16
      -- False on the left can always be used.
      apply False.elim h17
    case inr h18 =>
      -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
      have h19 : (p1 ∧ (p1 ∨ p4)) := by
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h13
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h13
      -- We have shown the premise of h10, we can now drive its conclusion.
      let h20 := h10 h19
      -- False on the left can always be used.
      apply False.elim h20
  case inr h21 =>
    -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
    have h22 : (p1 ∧ (p1 ∨ p4)) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h13
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h13
    -- We have shown the premise of h10, we can now drive its conclusion.
    let h23 := h10 h22
    -- False on the left can always be used.
    apply False.elim h23



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307286111800655305931010661058 : (p1 ∨ (p2 ∨ (p2 ∨ ((True → (p4 → ((p3 → p1) ∨ ((p2 ∨ ((((True → p4) → p4) ∧ ((p2 ∧ p4) → p3)) → p4)) ∧ True)))) ∨ p4)))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_729697331568674483822034018792 : (((((p1 → p4) ∨ p4) → ((False ∨ ((p2 ∧ (p5 → ((False → False) → p4))) → p3)) → ((p5 ∧ p4) ∨ ((p4 ∧ (p2 → p1)) → True)))) ∨ False) ∧ True) := by
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
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- True on the right can always be proven directly.
      apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111888694358256071778978791307 : (((((p5 → p4) ∨ ((p1 → False) ∧ (((p4 ∨ (p3 ∨ p5)) ∨ True) → p4))) ∧ (((p4 ∧ False) ∧ False) ∨ (p5 → p1))) ∨ p4) ∨ (False ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165244650974045349677585949999 : (((p1 ∨ (((p1 ∨ p1) → ((p4 ∨ True) ∧ (p1 ∨ (False ∨ p3)))) → p5)) ∨ (p1 ∨ p4)) ∨ (True ∨ (p3 ∧ (p3 ∧ ((p4 → p3) → True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51169333505151509464599201258 : ((((((p5 ∧ (p3 → (p4 ∨ (p5 ∨ (False → True))))) ∧ (p4 → p5)) → p3) ∨ (p1 ∧ True)) ∨ (p3 ∧ ((p2 ∧ (False ∧ p3)) ∧ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134371710377434839925681053933 : (((p2 ∨ (True ∧ ((((p3 ∧ ((((True ∨ (p1 → p4)) ∨ p5) ∧ True) ∨ p5)) → True) ∧ True) → (p1 → p3)))) ∨ p5) ∨ ((p3 ∧ p3) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_312350447653019105080301839405 : (p2 ∨ (p3 → (((p3 → ((p5 → ((p1 → (p1 ∧ ((p3 ∨ (p2 → (p3 ∧ (p1 ∧ True)))) → False))) ∧ True)) ∧ p2)) ∨ (p4 ∨ p3)) ∨ p4))) := by
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
theorem thm_5_vars_515988166759905856411272642919 : ((((p2 → p1) ∨ ((((((((p3 ∧ (((True ∧ False) ∧ p4) ∧ p1)) → (p2 ∧ (p3 ∧ p1))) → False) ∧ p4) ∧ False) ∧ p3) ∧ p3) ∨ True)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113025673523549798768944388602 : (((True ∨ ((p5 ∨ ((((((p1 ∧ p4) ∨ True) ∨ (p4 → False)) ∧ p4) ∧ True) → (p2 ∧ p1))) ∨ (p5 → (p4 → False)))) → p4) ∨ (p1 → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_923300348446973554082051036675 : (((((((p3 ∨ False) ∧ True) ∨ (p4 → ((p3 ∧ p2) → p4))) → False) ∧ ((p2 ∨ p5) → (((p1 ∧ p2) ∧ (p4 → (p3 ∧ True))) → p4))) → False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (((p3 ∨ False) ∧ True) ∨ (p4 → ((p3 ∧ p2) → p4))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Implications on the right can always be decomposed.
    intro h6
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h9 := h2 h4
  -- False on the left can always be used.
  apply False.elim h9
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_636641298474086132917000932845 : ((((((((p3 ∧ ((p5 → p1) → p2)) → (p1 → (False ∧ p3))) ∨ p4) → p5) ∨ ((p2 ∨ ((p4 → False) ∨ p3)) → (p5 ∧ True))) → False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_588448734928134311545305215028 : ((((((p4 → (p3 ∨ p4)) → (p5 ∧ (((p5 ∧ (((False ∧ False) → p4) ∧ (((p1 ∨ False) → p4) ∧ p5))) ∧ p5) → p4))) ∨ False) ∧ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_753429946976533227189697289129 : (((False ∧ (((p5 ∧ p5) ∨ (((p3 ∧ ((p4 ∧ (p1 → p2)) ∧ ((p1 ∨ p3) ∧ p1))) → (p3 → p3)) ∧ False)) ∨ (p2 ∨ (False ∧ p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299376016986775074667275319485 : (False ∨ (((p3 → p5) ∨ ((((p2 → (p5 → ((p3 ∨ True) ∧ p5))) ∨ p5) → (False ∨ (((p4 ∨ False) ∧ False) ∧ p1))) → (p3 ∧ p2))) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p2 → (p5 → ((p3 ∨ True) ∧ p5))) ∨ p5) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h2
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h8.left
    let h11 := h8.right
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h12 =>
      -- False on the left can always be used.
      apply False.elim h11
    case inr h13 =>
      -- False on the left can always be used.
      apply False.elim h13
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h14 : ((p2 → (p5 → ((p3 ∨ True) ∧ p5))) ∨ p5) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h15
    -- Implications on the right can always be decomposed.
    intro h16
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
    -- One of the premise coincides with the conclusion.
    exact h16
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h17 := h1 h14
  -- Disjunctions on the left can always be decomposed.
  cases h17
  case inl h18 =>
    -- False on the left can always be used.
    apply False.elim h18
  case inr h19 =>
    -- Conjunctions on the left can always be decomposed.
    let h20 := h19.left
    let h21 := h19.right
    -- Conjunctions on the left can always be decomposed.
    let h22 := h20.left
    let h23 := h20.right
    -- Disjunctions on the left can always be decomposed.
    cases h22
    case inl h24 =>
      -- False on the left can always be used.
      apply False.elim h23
    case inr h25 =>
      -- False on the left can always be used.
      apply False.elim h25



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338552488695322514015218914346 : (p1 → ((p3 ∨ (p5 ∧ p4)) ∨ (((p4 ∧ p5) ∨ (p4 → True)) ∧ ((True → (p1 → p2)) → (True ∨ ((((p3 ∧ False) ∨ False) → p5) ∧ p2)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_262756396910694872430518323762 : (True ∧ (((p3 → ((p4 → p5) ∧ (True ∧ False))) ∧ (p3 ∧ ((((False ∨ (p5 → (p3 ∨ (p1 → (True ∧ True))))) ∨ p3) ∧ True) ∧ p5))) → p4)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- False on the left can always be used.
      apply False.elim h11
    case inr h12 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h13 : p3 := by
        -- One of the premise coincides with the conclusion.
        exact h4
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h14 := h2 h13
      -- We need to get the right conjuct of h14 based on <expert-advice>.
      let h15 := h14.right
      -- We need to get the right conjuct of h15 based on <expert-advice>.
      let h16 := h15.right
      -- False on the left can always be used.
      apply False.elim h16
  case inr h17 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h18 : p3 := by
      -- One of the premise coincides with the conclusion.
      exact h17
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h19 := h2 h18
    -- We need to get the right conjuct of h19 based on <expert-advice>.
    let h20 := h19.right
    -- We need to get the right conjuct of h20 based on <expert-advice>.
    let h21 := h20.right
    -- False on the left can always be used.
    apply False.elim h21



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319565255668473062532439886869 : (p4 ∨ (((((False ∨ p1) ∧ p3) → (True ∧ (p3 ∧ p1))) ∧ p4) → (((False ∧ (True ∧ p4)) ∧ ((p2 ∨ p4) ∨ False)) ∨ ((False ∧ p5) ∨ p4)))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46964634375669606608759939952 : ((((((p3 ∨ (p1 ∨ ((p2 → p2) ∨ (((p1 ∨ p5) → p2) ∨ p3)))) → (((True ∧ p3) → True) ∨ p5)) ∨ p2) → False) ∨ (False → p3)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345567478603276309242407814409 : (p3 → ((((p4 ∨ p3) ∧ True) ∧ (((((p3 ∧ ((p5 → p2) ∧ p2)) → True) → True) ∧ ((((p4 ∨ p3) ∧ p4) ∨ p5) ∨ p3)) → p4)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300385368775325346473222743132 : (False ∨ ((((((False → (False → p2)) → False) ∧ p4) ∧ p2) ∨ ((False ∨ p3) → (False ∧ (True → ((p5 ∨ p1) ∧ True))))) ∨ (True ∨ (p3 ∨ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_151805470880098558260125986303 : (((((False → ((((True ∧ (p1 ∧ p2)) → p4) ∨ p5) ∧ p2)) → p1) → p2) ∧ (((p1 ∧ p2) → p5) ∧ p1)) → ((True ∧ p1) → (p5 ∧ p5))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h7 := h6.left
  let h8 := h6.right
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h9 : ((False → ((((True ∧ (p1 ∧ p2)) → p4) ∨ p5) ∧ p2)) → p1) := by
    -- Implications on the right can always be decomposed.
    intro h10
    -- One of the premise coincides with the conclusion.
    exact h8
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h11 := h5 h9
  -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
  have h12 : (p1 ∧ p2) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h8
    -- One of the premise coincides with the conclusion.
    exact h11
  -- We have shown the premise of h7, we can now drive its conclusion.
  let h13 := h7 h12
  -- One of the premise coincides with the conclusion.
  exact h13
  -- Conjunctions on the left can always be decomposed.
  let h14 := h2.left
  let h15 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h16 := h1.left
  let h17 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h18 := h17.left
  let h19 := h17.right
  -- We want to use the implication h16 based on <expert-advice>. So we show its premise.
  have h20 : ((False → ((((True ∧ (p1 ∧ p2)) → p4) ∨ p5) ∧ p2)) → p1) := by
    -- Implications on the right can always be decomposed.
    intro h21
    -- One of the premise coincides with the conclusion.
    exact h19
  -- We have shown the premise of h16, we can now drive its conclusion.
  let h22 := h16 h20
  -- We want to use the implication h18 based on <expert-advice>. So we show its premise.
  have h23 : (p1 ∧ p2) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h19
    -- One of the premise coincides with the conclusion.
    exact h22
  -- We have shown the premise of h18, we can now drive its conclusion.
  let h24 := h18 h23
  -- One of the premise coincides with the conclusion.
  exact h24



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137953835807967542314662616205 : ((p5 ∨ ((((p1 ∨ (p5 ∧ ((True → (True ∨ ((p3 ∧ False) ∧ p3))) ∧ p4))) → (False → (p3 ∨ p5))) ∨ p3) → p5)) ∨ ((False ∧ True) → p5)) := by
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
theorem thm_5_vars_778313375630497829392447955946 : (((p1 ∨ (False ∧ ((((p4 → p4) → (p1 ∧ True)) ∧ (p2 → (p1 → p4))) ∨ (((p4 → (p2 ∨ (p4 ∧ (p1 ∧ p1)))) ∨ p5) ∨ p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45035023045216574507560533054 : ((((p3 ∨ p3) ∨ (((((p3 ∨ p1) ∨ (False ∨ (p1 ∧ p4))) → p2) ∨ ((p5 → True) ∨ p1)) ∨ ((False ∧ p4) → (False ∧ p1)))) → p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258663565948929248571750211487 : ((p5 ∨ p5) → ((((p1 ∨ p1) ∨ p2) ∧ ((p4 → ((False → (p2 ∨ p4)) ∧ p1)) ∧ p1)) ∨ (((p4 ∨ False) → True) ∨ (p3 ∨ (p5 → p1))))) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180594006710001807752552440149 : (((p2 → (True → ((False ∨ True) ∨ (p4 ∨ p5)))) → (p4 ∧ (p3 ∨ p3))) → (p1 ∨ (((p4 ∨ (p5 ∨ p2)) ∨ (p2 ∧ True)) → (True ∧ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p2 → (True → ((False ∨ True) ∨ (p4 ∨ p5)))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h2
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h7
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- One of the premise coincides with the conclusion.
      exact h9
    case inr h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- One of the premise coincides with the conclusion.
        exact h6
      case inr h12 =>
        -- One of the premise coincides with the conclusion.
        exact h6
  case inr h13 =>
    -- Conjunctions on the left can always be decomposed.
    let h14 := h13.left
    let h15 := h13.right
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356664691953775299435251683953 : (p5 → ((True ∧ (((p2 → (p2 ∨ p5)) → p1) → False)) → (((False ∧ True) → False) ∧ (((((p2 → p1) → False) → False) ∧ (p4 ∨ p2)) → p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- False on the left can always be used.
  apply False.elim h4
  -- Implications on the right can always be decomposed.
  intro h6
  -- Conjunctions on the left can always be decomposed.
  let h7 := h6.left
  let h8 := h6.right
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h2.left
    let h11 := h2.right
    -- One of the premise coincides with the conclusion.
    exact h9
  case inr h12 =>
    -- Conjunctions on the left can always be decomposed.
    let h13 := h2.left
    let h14 := h2.right
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h15 : ((p2 → p1) → False) := by
      -- Implications on the right can always be decomposed.
      intro h16
      -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
      have h17 : ((p2 → (p2 ∨ p5)) → p1) := by
        -- Implications on the right can always be decomposed.
        intro h18
        -- We want to use the implication h16 based on <expert-advice>. So we show its premise.
        have h19 : p2 := by
          -- One of the premise coincides with the conclusion.
          exact h12
        -- We have shown the premise of h16, we can now drive its conclusion.
        let h20 := h16 h19
        -- One of the premise coincides with the conclusion.
        exact h20
      -- We have shown the premise of h14, we can now drive its conclusion.
      let h21 := h14 h17
      -- False on the left can always be used.
      apply False.elim h21
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h22 := h7 h15
    -- False on the left can always be used.
    apply False.elim h22



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37696416851043435954118577851 : (((((((p2 → ((p3 → ((p3 ∧ (False → p4)) ∧ ((p4 → p5) ∧ True))) → p1)) ∨ p1) ∨ True) ∧ (p3 ∧ (p1 ∨ p1))) → False) ∧ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166193913909189338209886057325 : ((p1 ∧ ((((p2 ∧ p2) → p3) ∨ (p3 → (p5 ∧ p2))) → (p4 ∧ ((p1 ∧ p3) ∧ p4)))) ∨ (p2 → ((((False ∧ p1) ∧ False) → True) ∨ p3))) := by
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
theorem thm_5_vars_136802334821480093877449775913 : (((p3 → p1) ∧ (((((p3 ∨ ((p4 ∧ p4) ∨ (p3 ∧ True))) ∧ (p4 → (p4 → (p2 → p3)))) ∨ False) ∨ True) ∧ p3)) ∨ (p1 ∨ (p1 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191079141193887646153505903777 : ((((p4 ∧ p2) ∧ p1) ∧ ((p5 ∨ False) ∧ (p1 ∧ False))) ∨ (False ∨ (True ∨ ((((p2 ∨ True) ∧ (False ∨ p1)) ∨ (p1 ∨ p2)) ∧ (True → p1))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219564547658665140623363111181 : ((True → ((p2 ∨ False) ∨ p2)) → ((((p2 ∧ ((((False ∧ (p5 ∧ True)) ∨ p4) ∧ (p3 → (p2 → p4))) ∨ p5)) ∨ (False ∨ True)) ∧ True) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117129340715541630411943235464 : (((p4 → p4) → ((((False ∨ ((p2 ∧ (p4 ∨ (((p5 ∧ False) ∧ p4) ∧ p3))) → p5)) ∧ (False ∧ False)) ∨ (True ∨ p1)) ∨ p5)) ∨ (p3 ∧ p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39015622981127138110344923301 : ((((True → False) ∧ (((p3 → False) → ((((False → (p5 ∨ True)) ∨ (p5 ∨ (False ∨ (p5 ∨ (True ∨ p1))))) ∨ p3) → p1)) ∧ p3)) ∧ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177735081301669714407917726054 : (((((p3 → p2) → p1) ∧ (p2 ∨ (False ∨ ((p4 ∧ p2) → False)))) ∧ p5) ∨ (False → ((p3 → p1) ∧ ((p4 → p4) → (False ∧ (True ∨ p2)))))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200772961673911605711372403196 : ((p4 ∧ ((p5 ∨ (p4 → p5)) ∨ (p3 → p5))) → ((p1 ∧ p2) ∨ (p4 ∨ (((True ∨ True) → p1) ∨ ((p5 ∧ (p1 → p2)) → (False ∧ p5)))))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h2
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114731997942731030120293799982 : (((((p3 ∨ (False ∧ p5)) ∧ (p4 ∧ p3)) ∨ (p3 ∨ (((p4 → False) → p5) → p3))) → ((p2 → ((False ∧ p3) → False)) → p4)) ∨ (True → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184073581585342115391332219975 : (((((p5 ∨ (p4 ∧ p4)) ∨ p5) ∨ (True ∧ (p3 → False))) ∨ False) ∨ ((((False ∨ (True ∧ True)) → p2) → (p3 ∨ (p5 → p2))) ∧ (True ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : (False ∨ (True ∧ True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- One of the premise coincides with the conclusion.
  exact h4
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51698105899698526774511298286 : ((((p3 ∨ ((p3 → (False ∨ p4)) ∧ (p4 ∨ (p1 ∨ True)))) ∧ ((p4 ∨ True) ∨ True)) ∧ ((((p2 ∧ p5) → (True ∧ p3)) → p4) → p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58821184225523565888571429600 : (((p5 → p5) ∧ ((((((p3 ∨ ((((p2 → True) ∨ True) ∧ (p2 → True)) → p3)) ∧ (p1 ∧ True)) ∧ p2) ∨ (p3 ∨ p4)) ∧ p5) ∧ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249913054432240020883826534103 : ((True → p1) ∨ ((((p3 ∨ True) ∧ (p4 → p1)) ∨ (((p5 → (True → False)) ∨ ((p1 ∧ p4) ∨ p3)) → (p3 ∨ p1))) ∨ ((False → True) ∨ p4))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42586932261409313737327318903 : (((p2 ∨ ((False ∨ ((p1 ∨ p4) ∧ False)) ∧ ((p2 → ((p2 ∨ True) → ((p2 ∨ p3) ∨ p2))) ∧ ((False ∨ (p4 ∧ p5)) ∨ True)))) ∨ True) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310489664013527881970651596436 : (p2 ∨ (((p2 ∧ ((p2 ∨ p2) ∨ p1)) ∨ True) ∨ ((p2 ∨ ((((p4 ∨ ((p4 → p2) ∧ ((False → p3) ∨ True))) ∧ p5) ∨ False) ∧ p5)) → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50538352764631121560514527540 : (((((p2 ∧ ((p1 → (False ∧ True)) → ((False → (p2 → (True → p5))) ∧ p4))) → (p4 ∨ p3)) ∨ False) → (p5 ∧ ((p5 ∨ p1) → p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43604491658376332158532547287 : ((((((p4 ∨ ((p3 ∧ ((p3 → ((p4 → (False → p5)) ∧ (p2 → p1))) → p5)) → (p1 → (p5 ∨ p4)))) ∨ False) → False) → True) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164714663768016878988052631245 : (((((((p3 ∨ (True ∧ (p2 ∧ p4))) → (p3 ∨ (p3 → p5))) ∧ p2) ∨ p4) → p5) ∨ p1) ∨ ((True → ((p1 ∨ True) → p4)) → (p4 ∨ p5))) := by
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
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : (p1 ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48246388507705581116775592888 : (((p1 ∧ (((p1 → p5) → (p5 → ((p1 → ((p4 → p4) → (p1 ∧ (p5 ∧ (p5 ∧ (True ∧ p1)))))) ∧ p4))) → p3)) → (p2 → p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167469231802974953616523614994 : (((p3 → ((p3 ∨ (p2 → p4)) ∨ (((p4 ∧ True) → p4) ∧ (p1 → (p2 ∨ p2))))) → p5) → (True → ((p3 ∧ p4) → ((True ∧ False) ∨ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192690048766743488080841669948 : ((((((False → False) → p1) → p2) ∨ (p2 ∧ p3)) → p4) → ((((False → (((p1 → (False ∨ (p1 → p4))) ∨ p4) → True)) → p1) ∨ True) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_597260429815118675781508647111 : ((((((True ∨ p1) → (p4 ∧ p5)) ∧ (((p1 → (p4 → (p3 ∧ (False ∧ p2)))) ∧ (p5 ∨ (False ∨ (True → (p2 ∨ p5))))) ∨ p1)) ∧ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50323124477781273184031425583 : ((((p5 ∧ ((((p4 ∨ p2) ∨ p1) → (p3 ∨ False)) ∧ p3)) ∨ (p3 ∨ ((p5 ∧ (p4 ∧ p1)) → p4))) ∨ (p3 → ((p2 → False) → p5))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  let h4 := h3.left
  let h5 := h3.right
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_782332854181447399277514798759 : (((p3 ∨ ((((((True → p1) ∨ ((p1 ∨ p4) → (p4 ∨ (((p4 ∧ (p3 ∧ p1)) → p1) ∨ (p1 ∨ False))))) → p5) ∧ False) ∧ p2) ∨ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317760495074364579731846149057 : (p4 ∨ (((((((p3 → True) → ((p3 → (p1 → (p5 → p2))) ∨ p4)) → p1) ∨ p2) ∨ True) ∨ ((p2 → (True ∧ p1)) → (p4 ∧ p5))) ∨ False)) := by
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
theorem thm_5_vars_615365496102683789568529826171 : ((((((((p3 ∧ p4) ∨ p1) ∨ False) → (((p1 → p4) ∨ (p1 → p5)) ∨ (True ∧ p4))) ∨ (p3 ∨ (p4 ∧ ((p1 → False) ∨ p3)))) ∨ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156956760692564390106111479267 : ((((((p5 ∨ False) ∧ ((p1 ∧ (True → True)) ∨ (False → p4))) → p2) ∨ (p2 → (p5 ∨ p5))) ∨ True) ∨ (((p3 → (True ∨ p1)) ∨ True) ∧ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_631784640304740027019111283009 : (((((((False ∧ False) → (((p3 ∧ (p3 ∨ p1)) ∧ p3) ∨ p1)) → (p5 ∧ ((((False → False) ∨ (p2 ∧ p5)) → p3) ∧ p1))) → True) → False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258698950821532120325064210320 : ((True → True) → ((((((True → p2) ∨ False) ∧ p1) → False) ∨ ((p2 ∨ p5) ∨ (True ∨ (((True ∨ p3) ∧ p2) → ((p4 ∧ p1) ∨ p5))))) ∧ True)) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_36421298460982834475646440843 : ((p4 → (((((True → p3) ∨ p3) ∨ (p5 → p1)) → False) ∨ ((p3 ∨ (False → (p3 ∧ (p1 → True)))) ∨ (True → (p5 ∧ (False ∧ p2)))))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152527760052139275351106894038 : (((p5 → (p4 ∧ False)) ∨ (((((p3 → True) → p2) → (p1 ∧ True)) ∨ True) ∨ ((p3 ∧ p4) → (p1 ∨ p2)))) → (p5 → (p1 ∨ (True ∨ p3)))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
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
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2093263375252996126519179015 : (((True → False) → (p4 ∨ ((False ∧ (p2 → (p3 → (p3 → False)))) ∨ (False ∨ (p5 → p4))))) ∨ ((((True ∨ p3) ∨ p2) → p5) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173579710359080827718004349395 : ((((True → p5) → ((p2 ∨ (p1 → p1)) ∨ ((p3 → (p2 ∨ True)) → p3))) ∧ p4) → (((p3 ∧ p5) ∨ (p2 ∨ (p2 ∨ (p4 ∨ p3)))) ∨ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
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
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186150197900793927604425136027 : ((((p2 ∨ False) ∧ (p4 ∧ ((p1 → (True → p3)) ∧ True))) ∨ p3) → (((((True ∨ (p2 ∨ True)) → p3) ∨ False) ∨ False) ∨ (p1 → (p5 ∨ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h4.left
      let h7 := h4.right
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h10
    case inr h11 =>
      -- False on the left can always be used.
      apply False.elim h11
  case inr h12 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h13
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_355541798371260112400493806191 : (p5 → (((((p3 ∧ (p5 → (True ∧ (p1 ∨ ((p2 → (p1 ∨ p1)) ∨ p3))))) ∨ p1) → (p4 ∧ ((True ∧ True) → p4))) ∨ p1) ∨ (p5 ∧ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_252764209786788364294182701566 : ((True ∧ True) → ((p4 ∨ (p5 ∧ (p5 ∧ ((((p3 → (False ∧ (True → ((p1 → p5) ∨ True)))) ∨ (False → True)) → p4) ∧ p5)))) ∨ (p4 → p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_397525078179794391872135854078 : ((((p2 ∨ (((p4 → (((p3 ∧ False) ∨ p2) ∨ p4)) → (True → p3)) → (((((p3 ∨ p2) ∨ p2) → False) ∨ p3) ∧ (p3 ∨ p3)))) ∨ p5) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p4 → (((p3 ∧ False) ∨ p2) ∨ p4)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h5 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h6 := h4 h5
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h6
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h7 : (p4 → (((p3 ∧ False) ∨ p2) ∨ p4)) := by
    -- Implications on the right can always be decomposed.
    intro h8
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h8
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h9 := h1 h7
  -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
  have h10 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h9, we can now drive its conclusion.
  let h11 := h9 h10
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h11
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



