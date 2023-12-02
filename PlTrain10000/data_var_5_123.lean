variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134257518248604689003361777636 : ((((p3 ∧ (p3 ∨ True)) ∨ ((False ∨ (p2 ∧ ((True ∨ (True ∨ False)) ∧ p4))) ∧ ((p5 ∧ True) ∨ (True ∧ True)))) ∨ p1) ∨ ((p3 → p3) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225510518058900217132978603300 : (((p5 ∨ p4) ∧ True) ∨ (((((p5 ∧ p2) ∧ p5) ∨ p1) ∨ ((p4 → (False ∨ ((p3 ∧ p1) ∧ (p4 ∧ ((p1 ∧ p5) ∨ p3))))) → True)) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208321180181610337638821561397 : (((False → p5) ∧ ((p1 ∨ p1) ∧ p1)) → (((p5 ∨ (p2 ∧ (p1 ∧ (p3 → p4)))) → p1) ∧ (p3 ∨ ((p4 ∨ True) ∨ ((p3 → p4) → True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h1.left
    let h5 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h9 =>
      -- One of the premise coincides with the conclusion.
      exact h7
  case inr h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- Conjunctions on the left can always be decomposed.
    let h13 := h12.left
    let h14 := h12.right
    -- Conjunctions on the left can always be decomposed.
    let h15 := h1.left
    let h16 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h17 := h16.left
    let h18 := h16.right
    -- Disjunctions on the left can always be decomposed.
    cases h17
    case inl h19 =>
      -- One of the premise coincides with the conclusion.
      exact h18
    case inr h20 =>
      -- One of the premise coincides with the conclusion.
      exact h18
  -- Conjunctions on the left can always be decomposed.
  let h21 := h1.left
  let h22 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h23 := h22.left
  let h24 := h22.right
  -- Disjunctions on the left can always be decomposed.
  cases h23
  case inl h25 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h26 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68287329801302312719312014903 : ((p3 → (((p2 → p4) ∨ ((p2 → (False ∨ ((p5 ∧ (True ∧ (p2 → True))) ∧ (p1 ∨ (False → False))))) → False)) ∧ ((p4 ∨ p1) → p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_318553101519854419817636878793 : (p4 ∨ ((((((True → ((True ∧ p1) ∨ False)) ∧ ((p1 ∧ p4) ∧ p3)) ∧ ((p5 → ((False ∨ p2) ∨ p1)) ∨ p3)) ∧ p1) ∨ p5) ∨ (False → False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150890509027749601824923111810 : (((((p4 ∧ p4) ∧ p4) ∧ (p2 → (((((p3 → (p1 ∧ False)) ∨ (False ∧ p1)) → p5) ∨ p2) ∧ True))) ∨ p2) → (p1 ∨ (p2 ∨ (p3 ∨ p4)))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158782541024199698146077555524 : ((p5 ∧ ((((p4 → p2) ∧ ((False → (p3 ∨ (p5 → False))) → ((p5 ∧ False) → p3))) → p3) ∨ p1)) ∨ (p2 → (p5 ∨ ((True ∨ False) ∨ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_692178879029385974475388410572 : ((((((p3 ∨ ((p1 ∨ (True ∨ ((p1 ∨ True) ∨ p5))) ∧ p5)) → p1) ∨ p3) ∧ (False → (p4 ∧ ((False → (p5 → p3)) ∧ (p5 → p4))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186235929519118275658529796650 : ((((((p5 ∨ (True ∧ (p2 ∨ p2))) ∧ p1) ∧ p4) ∧ p4) → p3) → (p3 → ((p3 ∧ ((p1 → p5) ∨ ((True → p1) → (p4 → p1)))) ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_608410356489047917317777158118 : (((((((((p3 ∨ ((p3 ∨ p3) → (p3 ∨ p1))) ∨ (p4 ∧ ((True ∧ p1) ∨ p3))) ∧ (p5 → (p4 ∨ p1))) ∧ p2) → False) ∨ True) ∨ p4) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_311949686926541966609186723144 : (p2 ∨ (p3 ∨ (((p4 ∨ (p1 ∧ (p3 → p4))) ∨ (True ∨ p3)) ∧ (True ∨ (p4 ∧ ((p1 ∨ (p3 ∧ ((p4 → True) ∧ (False ∧ p2)))) ∧ True)))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161837601802369279637836073228 : ((True → (((((False ∧ (True ∨ p5)) ∨ (p4 ∨ False)) → p2) → (p2 ∨ (p3 ∨ True))) → (True → p2))) → ((p3 ∧ False) ∨ (p2 ∨ (p1 → True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263389829608967077950698079083 : (True ∧ ((((((p3 ∧ ((False ∨ p5) ∧ False)) → ((False ∨ p4) ∧ True)) → (p1 ∧ (p5 → False))) ∨ p1) → (p4 → p3)) ∨ (p1 ∨ (True ∨ p5)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_163672412555968962442645161662 : (((True → p4) ∨ ((p3 ∨ p3) → ((p2 ∨ (((p1 → p3) → False) ∨ p3)) ∨ (p2 → p4)))) ∧ (p1 ∨ (p1 → (True ∨ (p5 ∨ (p2 ∨ p5)))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_684575739516863052731871540787 : (((((p5 ∧ ((p2 → False) → p3)) ∨ ((p2 ∧ (p5 → (False → (p2 ∧ (p1 → p1))))) ∧ False)) ∨ ((p4 ∨ (p3 → (p1 → p3))) ∨ p1)) ∨ p1) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158682717977301745591177858601 : ((p2 ∧ ((True → (p3 → (False ∨ (p4 ∨ ((p4 ∨ p5) ∧ p1))))) ∨ ((p2 → (False → p4)) ∧ p4))) ∨ ((p2 ∧ (p5 ∧ p3)) → (p4 ∨ p3))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_251415600212580586633457275151 : ((p2 → p5) ∨ ((((p1 ∨ (p2 ∧ p4)) ∨ (((p3 → p2) → False) → ((((p1 ∨ p2) ∧ (p4 ∨ False)) → p3) → p4))) ∧ (p3 ∨ p4)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_608437084165887279904276713856 : (((((((p2 → ((p4 ∧ (((p1 ∧ (False ∨ p1)) ∨ False) ∧ p3)) → ((((True ∨ True) ∧ p3) ∧ p4) ∧ p2))) ∨ True) → p3) ∨ p2) ∨ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114816898521679578937682686682 : (((True ∧ (((((True → p3) ∨ False) → False) → (p2 ∧ (p2 → p4))) ∨ p4)) ∧ (True ∧ ((p4 ∨ p4) → ((p1 ∧ True) → p5)))) ∨ (p4 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346475257098667020271695922794 : (p3 → (((p2 ∨ p4) ∧ (True ∨ ((((p2 ∨ (p3 ∧ (((False ∧ p4) ∨ p1) ∨ p4))) ∧ ((True ∨ p5) ∨ False)) ∧ p3) ∨ False))) → (p5 ∨ p3))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Conjunctions on the left can always be decomposed.
        let h9 := h8.left
        let h10 := h8.right
        -- Conjunctions on the left can always be decomposed.
        let h11 := h9.left
        let h12 := h9.right
        -- Disjunctions on the left can always be decomposed.
        cases h11
        case inl h13 =>
          -- Disjunctions on the left can always be decomposed.
          cases h12
          case inl h14 =>
            -- Disjunctions on the left can always be decomposed.
            cases h14
            case inl h15 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- One of the premise coincides with the conclusion.
              exact h1
            case inr h16 =>
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- One of the premise coincides with the conclusion.
              exact h16
          case inr h17 =>
            -- False on the left can always be used.
            apply False.elim h17
        case inr h18 =>
          -- Conjunctions on the left can always be decomposed.
          let h19 := h18.left
          let h20 := h18.right
          -- Disjunctions on the left can always be decomposed.
          cases h20
          case inl h21 =>
            -- Disjunctions on the left can always be decomposed.
            cases h21
            case inl h22 =>
              -- Conjunctions on the left can always be decomposed.
              let h23 := h22.left
              let h24 := h22.right
              -- False on the left can always be used.
              apply False.elim h23
            case inr h25 =>
              -- Disjunctions on the left can always be decomposed.
              cases h12
              case inl h26 =>
                -- Disjunctions on the left can always be decomposed.
                cases h26
                case inl h27 =>
                  -- Show the right disjunct based on <expert-advice>.
                  apply Or.inr
                  -- One of the premise coincides with the conclusion.
                  exact h1
                case inr h28 =>
                  -- Show the left disjunct based on <expert-advice>.
                  apply Or.inl
                  -- One of the premise coincides with the conclusion.
                  exact h28
              case inr h29 =>
                -- False on the left can always be used.
                apply False.elim h29
          case inr h30 =>
            -- Disjunctions on the left can always be decomposed.
            cases h12
            case inl h31 =>
              -- Disjunctions on the left can always be decomposed.
              cases h31
              case inl h32 =>
                -- Show the right disjunct based on <expert-advice>.
                apply Or.inr
                -- One of the premise coincides with the conclusion.
                exact h1
              case inr h33 =>
                -- Show the left disjunct based on <expert-advice>.
                apply Or.inl
                -- One of the premise coincides with the conclusion.
                exact h33
            case inr h34 =>
              -- False on the left can always be used.
              apply False.elim h34
      case inr h35 =>
        -- False on the left can always be used.
        apply False.elim h35
  case inr h36 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h37 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h38 =>
      -- Disjunctions on the left can always be decomposed.
      cases h38
      case inl h39 =>
        -- Conjunctions on the left can always be decomposed.
        let h40 := h39.left
        let h41 := h39.right
        -- Conjunctions on the left can always be decomposed.
        let h42 := h40.left
        let h43 := h40.right
        -- Disjunctions on the left can always be decomposed.
        cases h42
        case inl h44 =>
          -- Disjunctions on the left can always be decomposed.
          cases h43
          case inl h45 =>
            -- Disjunctions on the left can always be decomposed.
            cases h45
            case inl h46 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- One of the premise coincides with the conclusion.
              exact h1
            case inr h47 =>
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- One of the premise coincides with the conclusion.
              exact h47
          case inr h48 =>
            -- False on the left can always be used.
            apply False.elim h48
        case inr h49 =>
          -- Conjunctions on the left can always be decomposed.
          let h50 := h49.left
          let h51 := h49.right
          -- Disjunctions on the left can always be decomposed.
          cases h51
          case inl h52 =>
            -- Disjunctions on the left can always be decomposed.
            cases h52
            case inl h53 =>
              -- Conjunctions on the left can always be decomposed.
              let h54 := h53.left
              let h55 := h53.right
              -- False on the left can always be used.
              apply False.elim h54
            case inr h56 =>
              -- Disjunctions on the left can always be decomposed.
              cases h43
              case inl h57 =>
                -- Disjunctions on the left can always be decomposed.
                cases h57
                case inl h58 =>
                  -- Show the right disjunct based on <expert-advice>.
                  apply Or.inr
                  -- One of the premise coincides with the conclusion.
                  exact h1
                case inr h59 =>
                  -- Show the left disjunct based on <expert-advice>.
                  apply Or.inl
                  -- One of the premise coincides with the conclusion.
                  exact h59
              case inr h60 =>
                -- False on the left can always be used.
                apply False.elim h60
          case inr h61 =>
            -- Disjunctions on the left can always be decomposed.
            cases h43
            case inl h62 =>
              -- Disjunctions on the left can always be decomposed.
              cases h62
              case inl h63 =>
                -- Show the right disjunct based on <expert-advice>.
                apply Or.inr
                -- One of the premise coincides with the conclusion.
                exact h1
              case inr h64 =>
                -- Show the left disjunct based on <expert-advice>.
                apply Or.inl
                -- One of the premise coincides with the conclusion.
                exact h64
            case inr h65 =>
              -- False on the left can always be used.
              apply False.elim h65
      case inr h66 =>
        -- False on the left can always be used.
        apply False.elim h66



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314640179116610782798132700742 : (p3 ∨ (((False ∧ (p2 → (p4 ∨ ((p1 ∧ p3) ∨ (((False ∧ p2) ∧ p2) ∧ p3))))) ∧ p4) ∨ (((p5 → p5) ∨ (p3 ∨ p3)) ∨ (True → True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45808560665410247949031625334 : (((p1 → (True ∨ (((p4 ∨ (p4 ∧ (p1 → p4))) ∧ (p1 → (p2 → (p4 → ((p3 ∧ p1) ∨ (p5 ∧ True)))))) ∨ (p1 ∧ p5)))) → p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315107175588963478817756418943 : (p3 ∨ ((((p4 ∧ p3) ∧ (p5 ∧ True)) ∧ p4) ∨ (((((p3 ∨ False) → (False → ((False → (p4 ∨ p2)) ∧ p5))) ∨ (True ∨ p2)) ∨ p2) ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_344589241585143324294392324351 : (p2 → (p1 → ((((((((p2 → p1) ∧ False) ∨ p1) → p4) ∨ p3) ∧ (p4 ∨ (((p3 → (p5 → p5)) ∧ (False → p5)) → p3))) ∨ True) ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164590422986227511159472284835 : ((((False ∨ p5) ∨ (((p3 ∨ True) → False) ∧ ((p1 ∧ (True → p1)) ∨ (p1 ∨ True)))) ∧ p4) ∨ (((False → (p5 ∨ True)) ∨ (p1 ∨ p4)) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164903992012311150882543984144 : ((((((p2 → p3) ∨ (((p3 → p4) ∧ p5) ∨ p4)) ∧ (p1 → (p1 ∧ False))) ∧ p5) → False) ∨ ((True ∨ p5) ∨ (((True → p4) ∨ p5) ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66316944662965572040729278628 : ((p5 ∨ (True ∧ (((p4 → p5) ∧ True) → (((False → ((True ∨ p3) ∧ (p5 → p3))) → (((p4 ∨ True) ∧ True) → (False ∨ False))) → False)))) ∨ p4) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h5 : (False → ((True ∨ p3) ∧ (p5 → p3))) := by
    -- Implications on the right can always be decomposed.
    intro h6
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- False on the left can always be used.
    apply False.elim h6
    -- Implications on the right can always be decomposed.
    intro h7
    -- False on the left can always be used.
    apply False.elim h6
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h8 := h2 h5
  -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
  have h9 : ((p4 ∨ True) ∧ True) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h8, we can now drive its conclusion.
  let h10 := h8 h9
  -- Disjunctions on the left can always be decomposed.
  cases h10
  case inl h11 =>
    -- False on the left can always be used.
    apply False.elim h11
  case inr h12 =>
    -- False on the left can always be used.
    apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55788838407514915177225314914 : ((((p4 ∧ p3) ∨ (False ∨ p3)) ∧ (p1 ∧ ((((p3 ∨ (True ∨ (p2 ∧ (p5 ∨ p2)))) → False) ∨ ((p3 ∧ p4) ∧ (p3 ∧ True))) → p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46613796473864666196186511363 : (((p3 ∧ ((((p1 → (p4 → ((p4 → ((p3 ∨ p3) ∧ p5)) → p3))) ∧ (p3 ∧ (True ∨ p1))) ∨ (p2 ∧ p4)) ∨ p3)) ∧ (p1 → p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_357422879402656469877297396971 : (p5 → ((p2 ∨ p4) → ((((False ∨ p3) ∨ (True ∧ p1)) ∧ (False → p3)) ∨ (p1 → ((p2 ∨ ((False ∨ p5) → p4)) ∨ ((False → p1) ∨ p4)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134556771708479241471263403267 : ((((p3 ∧ (((p1 ∧ (((p1 ∧ p4) ∨ p5) → True)) ∨ p4) ∨ ((p2 ∨ (False ∧ True)) → (p3 ∧ p3)))) → p2) → False) ∨ (False → (p2 ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_654346595898493384771825690505 : ((((((p4 ∨ (((p4 ∨ False) ∨ (p3 ∧ p5)) ∧ ((p1 ∨ p5) ∨ p1))) ∧ ((True → p3) → ((True → p2) → p4))) ∨ p4) ∨ (True ∧ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_196905544398589025852132744100 : (((p5 → (p1 ∨ ((p2 ∧ False) ∧ p2))) ∧ False) ∨ (((False ∨ False) → (p5 ∨ (((p5 ∧ False) → ((p2 ∨ p5) ∨ p4)) → (p4 → False)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138325948223245815889123875751 : ((p3 → (False ∨ ((((True ∧ (p1 → p3)) ∧ p2) → (((p2 ∨ (p3 ∧ p2)) ∨ p1) ∨ (p2 → (p2 ∧ True)))) → False))) ∨ ((True ∨ p1) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56208626356108400051659404798 : (((False ∨ (p5 ∨ (True → p3))) ∨ (p2 ∨ ((False ∨ p1) → ((p2 ∧ (p2 → (True → ((((False ∨ True) ∧ p1) ∧ p1) ∧ p1)))) → p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_740436933671014628228948547206 : ((((p1 ∨ p4) ∨ ((((p4 → True) ∨ ((p2 ∧ p1) ∧ False)) ∧ (((p5 ∧ True) ∨ p1) ∧ (((p4 ∧ False) ∧ p2) ∨ (p5 ∨ p3)))) → p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219747876252199415163913698393 : ((p2 → ((p1 ∧ p2) ∧ p3)) → ((p3 ∨ (p5 ∧ ((p1 → (False ∨ p1)) ∧ (False ∨ p3)))) ∨ ((True → p4) → (p4 ∨ ((p5 ∧ True) ∨ p4))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347027972584449856308247131679 : (p3 → ((p4 ∨ (True → ((((p2 ∧ p2) → p4) ∧ (p4 ∨ p1)) ∨ ((p5 ∧ p2) ∨ True)))) ∨ ((True ∧ (p2 ∨ ((p4 → p3) ∧ p5))) ∧ p3))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260635311070847553711435981703 : ((p3 → p2) → (p1 → ((((((((p4 ∨ p3) ∧ ((p5 ∨ p1) ∧ p4)) ∧ (p1 ∨ p2)) → p4) ∧ p5) ∨ p5) ∨ ((p2 ∨ p5) ∧ p4)) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63059170497493009266314173657 : ((p5 ∧ ((True ∧ ((((p3 ∧ (p5 ∨ p2)) ∨ ((p5 ∨ p1) ∨ True)) ∨ ((p5 ∨ (p1 → p2)) ∧ p1)) ∧ (p3 ∧ (p4 ∧ p2)))) ∧ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172435514603499214714506178214 : (((p2 → (False ∨ (p4 → False))) ∧ (p1 ∧ ((False ∨ p2) → (False ∨ (p5 → p1))))) ∨ (True ∨ (((p3 ∧ (p5 → p4)) → (p5 ∧ False)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_78316002256583790048376561286 : (((p5 → (((p3 → (((p1 ∧ p1) ∨ p1) → p5)) ∨ p5) → ((p2 ∧ (p2 → (p3 ∨ (p5 ∧ False)))) → ((False ∨ p2) → p3)))) → False) → p2) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p5 → (((p3 → (((p1 ∧ p1) ∨ p1) → p5)) ∨ p5) → ((p2 ∧ (p2 → (p3 ∨ (p5 ∧ False)))) → ((False ∨ p2) → p3)))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- Implications on the right can always be decomposed.
    intro h6
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- False on the left can always be used.
      apply False.elim h7
    case inr h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h5.left
      let h10 := h5.right
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h11 =>
        -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
        have h12 : p2 := by
          -- One of the premise coincides with the conclusion.
          exact h9
        -- We have shown the premise of h10, we can now drive its conclusion.
        let h13 := h10 h12
        -- Disjunctions on the left can always be decomposed.
        cases h13
        case inl h14 =>
          -- One of the premise coincides with the conclusion.
          exact h14
        case inr h15 =>
          -- Conjunctions on the left can always be decomposed.
          let h16 := h15.left
          let h17 := h15.right
          -- False on the left can always be used.
          apply False.elim h17
      case inr h18 =>
        -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
        have h19 : p2 := by
          -- One of the premise coincides with the conclusion.
          exact h9
        -- We have shown the premise of h10, we can now drive its conclusion.
        let h20 := h10 h19
        -- Disjunctions on the left can always be decomposed.
        cases h20
        case inl h21 =>
          -- One of the premise coincides with the conclusion.
          exact h21
        case inr h22 =>
          -- Conjunctions on the left can always be decomposed.
          let h23 := h22.left
          let h24 := h22.right
          -- False on the left can always be used.
          apply False.elim h24
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h25 := h1 h2
  -- False on the left can always be used.
  apply False.elim h25



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_785659687055090331544775869035 : (((p4 ∨ (((p3 → (((p2 ∧ ((p2 ∧ p4) ∨ False)) ∨ (((True ∨ p2) → p4) → (p3 → (p4 → (p4 ∨ p4))))) ∨ p5)) → p2) → p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_4630564557130686780303864179 : (p5 → (((((p4 → (True ∨ False)) ∨ ((((False ∨ p5) ∨ p3) ∧ p5) → (((p1 ∨ (False ∧ p2)) ∧ p5) → p1))) ∧ True) → False) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184636142176741586085551076252 : (((p3 ∨ (p5 → ((False ∧ p1) ∧ p2))) ∧ (True ∧ (p4 ∧ False))) ∨ (((True → False) → (False ∧ (p5 ∧ (((p4 ∨ p2) ∧ False) → False)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65544873936494042194558376825 : ((p3 ∨ (True → ((True ∧ (((p3 ∨ p5) ∨ (False ∧ p1)) → p3)) ∨ ((((True ∨ (p2 ∧ p2)) ∨ p5) → p5) ∨ ((p2 → p4) ∨ p5))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159239191544859090234867179393 : ((p3 → ((p2 ∧ ((p5 ∨ ((True → (p4 ∨ ((p1 → p2) ∨ True))) → p4)) ∧ p3)) ∨ (False → p5))) ∨ (((True → (p5 → False)) → False) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_94473806658374990957969489205 : ((p2 ∧ (False ∨ (True → (p3 ∧ (((p2 ∨ (p1 ∨ (p3 ∧ p3))) → ((False ∧ False) ∧ False)) ∨ ((True ∨ True) ∧ (p3 ∧ (p3 → False)))))))) → False) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
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
    -- We need to get the right conjuct of h7 based on <expert-advice>.
    let h8 := h7.right
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
      have h10 : (p2 ∨ (p1 ∨ (p3 ∧ p3))) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h2
      -- We have shown the premise of h9, we can now drive its conclusion.
      let h11 := h9 h10
      -- We need to get the right conjuct of h11 based on <expert-advice>.
      let h12 := h11.right
      -- False on the left can always be used.
      apply False.elim h12
    case inr h13 =>
      -- Conjunctions on the left can always be decomposed.
      let h14 := h13.left
      let h15 := h13.right
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h16 =>
        -- Conjunctions on the left can always be decomposed.
        let h17 := h15.left
        let h18 := h15.right
        -- We want to use the implication h18 based on <expert-advice>. So we show its premise.
        have h19 : p3 := by
          -- One of the premise coincides with the conclusion.
          exact h17
        -- We have shown the premise of h18, we can now drive its conclusion.
        let h20 := h18 h19
        -- False on the left can always be used.
        apply False.elim h20
      case inr h21 =>
        -- Conjunctions on the left can always be decomposed.
        let h22 := h15.left
        let h23 := h15.right
        -- We want to use the implication h23 based on <expert-advice>. So we show its premise.
        have h24 : p3 := by
          -- One of the premise coincides with the conclusion.
          exact h22
        -- We have shown the premise of h23, we can now drive its conclusion.
        let h25 := h23 h24
        -- False on the left can always be used.
        apply False.elim h25



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160539580205254879612414369652 : ((((False → False) ∨ ((True ∧ p3) ∨ (True ∨ (True ∨ (p1 ∧ p4))))) ∨ (False → (p3 ∧ (p5 ∨ p2)))) → ((True → (p3 ∨ (p4 → True))) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h5
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Conjunctions on the left can always be decomposed.
        let h8 := h7.left
        let h9 := h7.right
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h9
      case inr h10 =>
        -- Disjunctions on the left can always be decomposed.
        cases h10
        case inl h11 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h12
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h13 =>
          -- Disjunctions on the left can always be decomposed.
          cases h13
          case inl h14 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h15
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h16 =>
            -- Conjunctions on the left can always be decomposed.
            let h17 := h16.left
            let h18 := h16.right
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_229710451027692134758976860749 : ((p4 → (p1 ∧ p5)) ∨ (((p3 ∨ p5) → ((((p5 ∧ False) ∨ p2) → ((False ∨ (p5 ∨ True)) ∧ (p2 → p2))) → p3)) ∨ ((False → True) ∨ p4))) := by
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
theorem thm_5_vars_229510266561937464461821274112 : ((p2 → (p1 ∨ p1)) ∨ ((p3 → (((p2 ∧ ((((p5 ∨ p5) ∧ (p5 → (p3 → True))) → p1) ∨ False)) ∧ (p4 → (p3 ∨ p2))) ∧ True)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_209055302332278986356569178438 : ((p1 ∨ ((p1 ∨ True) ∧ (p3 ∧ p1))) → (((True ∧ (False ∨ p4)) ∧ (((False ∨ True) ∧ p3) ∧ (p1 ∧ (True ∨ ((True ∨ p1) → True))))) ∨ True)) := by
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
    cases h4
    case inl h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h5.left
      let h8 := h5.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h5.left
      let h11 := h5.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179728010289019411103143444103 : (((((p1 ∧ False) → (p2 → (p3 ∨ ((p2 ∧ True) ∨ p3)))) → p2) ∧ True) → ((p5 ∧ (True → False)) → ((p5 ∧ (p1 ∨ False)) ∧ (False ∨ p1)))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h5 := h1.left
  let h6 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Conjunctions on the left can always be decomposed.
  let h7 := h2.left
  let h8 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h9 := h1.left
  let h10 := h1.right
  -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
  have h11 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h8, we can now drive its conclusion.
  let h12 := h8 h11
  -- False on the left can always be used.
  apply False.elim h12
  -- Conjunctions on the left can always be decomposed.
  let h13 := h2.left
  let h14 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h15 := h1.left
  let h16 := h1.right
  -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
  have h17 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h14, we can now drive its conclusion.
  let h18 := h14 h17
  -- False on the left can always be used.
  apply False.elim h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165377888230354636061704282855 : ((((((((p4 ∧ p4) ∧ p1) ∨ p5) ∨ p5) ∨ p2) → (p1 ∧ True)) ∨ ((p1 ∧ False) ∨ True)) ∨ (p4 → (((p3 ∨ p1) ∧ (False ∧ p5)) ∨ p1))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_127808303357945795414193867600 : ((True → ((p2 → p3) → ((p2 ∨ False) → (p3 ∧ (((p2 ∨ (((p4 → p2) → True) ∧ p4)) → p2) → ((p4 ∨ p4) ∧ p5)))))) → (p5 → p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113526544893733123354769541950 : ((((p1 ∨ ((p5 ∧ (p3 → (p4 → True))) → p2)) ∨ ((p5 → (((p2 ∧ p5) → True) ∧ False)) → (p1 ∨ True))) ∨ (p4 → p3)) ∨ (p3 ∧ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_669494499178198560291781442933 : ((((((True ∨ (True → (((((True ∧ (True ∧ p4)) ∨ False) → p3) → True) ∨ p3))) ∨ (p2 ∧ p2)) → (p1 ∨ p4)) ∨ (False → (p2 ∧ True))) ∨ p3) ∧ True) := by
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
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50131976760301578072680749832 : (((p4 ∨ (p1 ∧ (((p4 → ((p5 ∨ p1) ∧ False)) ∨ (True → True)) ∧ ((p5 ∨ p4) → (p2 ∨ p4))))) ∧ (p5 → ((p4 → p4) → False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_123508757984372360158790028425 : (((((p1 → ((p2 ∨ p1) → p2)) → p2) → (((True → True) ∧ (p2 → p4)) ∧ p1)) ∧ ((True ∧ ((p4 → False) → True)) ∧ True)) → (p2 → p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h9 : ((p1 → ((p2 ∨ p1) → p2)) → p2) := by
    -- Implications on the right can always be decomposed.
    intro h10
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h11 := h3 h9
  -- We need to get the left conjuct of h11 based on <expert-advice>.
  let h12 := h11.left
  -- We need to get the right conjuct of h12 based on <expert-advice>.
  let h13 := h12.right
  -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
  have h14 : p2 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h13, we can now drive its conclusion.
  let h15 := h13 h14
  -- One of the premise coincides with the conclusion.
  exact h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_125696326674463316543736639241 : (((False ∨ True) ∨ (((p1 ∧ p1) ∨ ((False ∧ (True → p2)) ∨ ((p1 → (((p1 ∧ False) ∧ p1) → p2)) ∧ p1))) ∧ (p2 ∨ p2))) → (p4 ∨ True)) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Disjunctions on the left can always be decomposed.
      cases h7
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
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h14 =>
        -- Conjunctions on the left can always be decomposed.
        let h15 := h14.left
        let h16 := h14.right
        -- False on the left can always be used.
        apply False.elim h15
      case inr h17 =>
        -- Conjunctions on the left can always be decomposed.
        let h18 := h17.left
        let h19 := h17.right
        -- Disjunctions on the left can always be decomposed.
        cases h7
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309635836146899860798818639205 : (p2 ∨ (((p4 ∧ ((p5 → p1) → True)) ∨ (((p4 ∧ p4) ∨ (False ∧ (p3 ∨ (False ∧ (p2 ∨ (p2 ∧ False)))))) ∨ True)) ∨ (True ∧ (p1 → p1)))) := by
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
theorem thm_5_vars_44967591988643467598333076271 : ((((True → False) ∧ (p1 → (p4 ∧ ((((p2 ∧ p1) → p2) → ((((p3 ∨ (p1 ∧ p5)) ∨ (True → p5)) → p1) → True)) ∨ p2)))) → p4) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47527194091710685136648658070 : (((p4 ∨ (((((True ∧ (((((True → p3) ∧ (p5 ∧ p2)) ∧ p2) ∧ p5) ∧ p3)) → (False ∧ p5)) ∧ p2) ∧ p2) ∧ p4)) ∨ (False → p2)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_783904035013855392210982187234 : (((p3 ∨ (((p5 ∧ p3) → p2) ∨ ((((((p4 → (True ∨ False)) → p3) ∨ p4) ∧ p3) ∨ p2) ∨ ((((p3 ∧ p4) ∨ p5) ∧ p4) ∧ p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_655383131190742938057013375177 : (((((((((p5 ∨ (True → (p1 → (p1 → p3)))) → p2) → (False ∧ (p3 ∨ True))) ∨ p1) ∨ (p1 → False)) ∨ (False → p3)) ∨ (False ∨ p5)) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_597146903868116532833403385682 : (((((((p4 ∨ p5) ∨ p2) ∧ p1) ∧ ((p5 → p3) ∨ (((p4 → p4) ∨ ((p4 → (p5 → (p4 ∨ p2))) → p5)) ∧ (p2 ∨ False)))) ∧ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_325138965280348349893136040737 : (p5 ∨ (True ∧ ((p5 → ((p1 ∧ ((p2 ∧ ((((True → p1) ∨ p2) → (False ∧ p4)) → ((p2 ∨ False) ∧ False))) ∧ p1)) ∧ False)) ∨ (p2 ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_67497422895640207026365921560 : ((p1 → (((((p5 ∨ p4) ∧ p3) ∨ (p5 ∨ (p1 → True))) ∧ p3) ∨ ((((p4 ∨ p5) ∨ p3) → (((p2 → p3) → p1) ∨ p3)) ∨ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191356996035117545099566387849 : (((p3 ∨ p3) ∨ (p4 ∨ (p1 → ((p4 ∨ p5) ∨ p5)))) ∨ ((p1 → ((p2 ∧ ((p3 ∨ p2) → p5)) → ((False ∧ p2) → (p1 ∧ p5)))) ∨ False)) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- False on the left can always be used.
  apply False.elim h4
  -- Conjunctions on the left can always be decomposed.
  let h6 := h3.left
  let h7 := h3.right
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356474060959876724190740282946 : (p5 → (((True ∨ (False → (p2 ∧ p1))) → ((p2 ∨ (True ∨ p5)) ∧ p4)) → ((((p4 → p1) ∨ p1) ∨ p5) ∧ (((p2 → p1) ∨ False) ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135009812809271176437659104232 : (((p1 ∨ (p2 → (p1 ∨ ((p3 → False) → (p2 → (p4 ∨ (True ∨ ((p4 → (p5 ∧ p2)) ∨ True)))))))) ∧ (p1 ∧ False)) ∨ ((p2 ∧ p3) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54715529360483182709690299142 : (((((p2 → (p3 ∨ p5)) → False) → (False → p4)) → (p3 → ((((p3 ∧ p1) ∨ p3) ∧ p2) ∨ (((p5 ∨ p4) ∧ (p3 ∧ p3)) ∨ p3)))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_669871261906852255759336229045 : (((((False ∨ (((((p5 ∨ p2) ∨ (p3 ∨ p2)) ∧ p5) ∧ False) ∧ False)) ∨ (((p5 ∨ True) ∧ (p5 ∧ False)) → p3)) ∨ (p1 ∧ (p4 ∧ False))) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h3.left
    let h6 := h3.right
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h3.left
    let h9 := h3.right
    -- False on the left can always be used.
    apply False.elim h9
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134127542207244414820028699764 : ((((True → (p3 ∨ ((p4 → ((p4 → (p4 ∧ ((p1 ∧ False) ∨ (p3 ∨ p3)))) → p4)) → p1))) ∨ (p3 ∧ p2)) ∨ p5) ∨ (p3 → (p3 ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_705588516145404763410138616436 : (((((p2 ∧ (p5 ∧ ((p4 ∧ False) ∨ p1))) → p5) ∧ (((p4 → ((p2 ∨ p5) ∧ (p1 ∧ p1))) → ((p4 → p5) → (False ∧ p5))) ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_223435130660705494080137119942 : ((True ∨ (p5 → p5)) ∧ (((p3 ∨ (p4 ∨ p2)) ∨ (p3 ∨ (p2 ∧ (p2 ∧ (p4 → p5))))) → ((p1 ∨ (False → ((True → p2) ∨ p2))) ∨ p3))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
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
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h4 =>
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h5 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h6
        -- False on the left can always be used.
        apply False.elim h6
      case inr h7 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h8
        -- False on the left can always be used.
        apply False.elim h8
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h10
    case inr h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- Conjunctions on the left can always be decomposed.
      let h14 := h13.left
      let h15 := h13.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h16
      -- False on the left can always be used.
      apply False.elim h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_732975004450797683071015108275 : ((((p2 ∧ p3) ∧ ((p3 → True) ∧ (True → (p1 → (((True ∨ p3) ∨ p3) → (((p3 → (True ∧ False)) ∧ ((p5 → False) ∧ p3)) → False)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54519476451069477754468880802 : ((((p1 ∨ p1) ∧ ((p1 → (p5 ∨ p3)) → False)) ∨ (False → (p5 ∨ ((True → (p4 ∧ ((False → p1) → (p2 ∧ p3)))) ∧ (True ∨ p2))))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_34487322217764373887526010603 : ((True → (p4 → (((p5 ∧ (p4 ∨ p1)) ∧ p5) → ((p2 ∨ (p1 ∨ ((True ∧ p1) ∨ p2))) ∨ ((p1 → True) ∨ ((p5 → True) ∧ p4)))))) ∧ True) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h9
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h10 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h10
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178137779622466993218062877261 : ((((p3 ∨ ((p5 ∨ p1) ∨ p1)) ∨ (p2 → (p5 ∧ (p4 ∨ p3)))) → p1) ∨ (True ∨ ((((p2 ∧ True) ∨ (True → p5)) ∨ (False → p2)) ∧ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113495290476652152402481749637 : (((((((p5 ∨ p2) → (p2 ∧ (p1 ∨ (True ∨ p3)))) ∧ (True → (p2 → p5))) ∨ p5) ∨ (p4 → (p4 ∧ False))) ∨ (True → True)) ∨ (p2 ∧ True)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_724914014205618718409411389284 : ((((p5 ∨ (p4 ∨ p4)) ∧ ((((False ∨ (True ∨ True)) ∧ (((True ∨ p1) ∧ p2) → p2)) ∨ ((True ∧ True) ∨ True)) ∧ ((p5 ∧ p3) ∧ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114579333814750778215662486959 : (((((True → (False ∨ (p5 ∨ True))) ∨ p4) ∧ (p5 ∧ ((p1 ∧ (False → True)) → p5))) ∧ (((False → p4) ∧ (p4 → p1)) → p1)) ∨ (p3 → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_468012413744395824040107448063 : ((((p1 ∧ ((p1 → (p5 ∧ True)) ∧ ((True ∧ (p1 → (p5 → p3))) ∨ p1))) ∨ (((p3 ∧ (((True ∨ p1) ∧ p3) ∨ p2)) ∧ p4) ∨ True)) ∧ True) ∧ True) := by
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
theorem thm_5_vars_242594957361011186552483721190 : ((p3 → True) ∧ (p3 ∨ (((False ∧ True) → False) ∧ ((True ∧ (((True ∨ p4) ∨ p4) → False)) → ((p3 ∧ False) ∨ (p1 ∨ ((True → False) ∧ p2))))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h3
  -- Implications on the right can always be decomposed.
  intro h5
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
  have h8 : ((True ∨ p4) ∨ p4) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h7, we can now drive its conclusion.
  let h9 := h7 h8
  -- False on the left can always be used.
  apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64128558371960480062906646461 : ((False ∨ ((((p2 ∨ p4) ∨ p4) → p2) ∨ (((True ∧ ((p2 → (((True → False) ∨ (p2 ∨ True)) ∧ p4)) → True)) → (p4 → p2)) ∧ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149692711098842952956479352538 : ((p5 ∧ ((((p2 ∨ p3) ∧ p1) → (((False ∧ True) → p1) ∧ (p2 ∧ p2))) → (p3 ∧ (p3 → (True → p2))))) ∨ ((p5 → p5) ∨ (p3 ∧ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_615317438145194543558416872738 : ((((((p2 ∨ ((((False ∧ (p2 → False)) ∨ p5) → p3) ∨ (p4 ∨ (p5 ∨ p3)))) → p3) ∨ (((False ∨ p4) ∧ p3) ∧ (p1 → p2))) ∨ True) ∨ False) ∧ True) := by
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
theorem thm_5_vars_114583334208364787052714626262 : (((((p2 ∧ (p1 ∨ p1)) ∧ p1) ∨ ((False ∧ (True ∨ p3)) ∨ (p2 ∨ (False → p4)))) ∧ (p4 ∧ (p5 ∧ (p1 ∧ (p2 → True))))) ∨ (p3 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356270583069018356087368154984 : (p5 → ((p4 ∧ (((p4 ∨ ((p1 ∧ (p5 → False)) ∨ p1)) ∧ ((p1 ∧ p4) → True)) → p2)) ∨ ((p3 → (p4 ∨ ((p4 ∧ p5) ∨ p5))) ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115864315671852747853973338585 : (((p3 → ((False ∧ p2) ∧ False)) ∧ (p4 → (((((True ∨ ((p1 ∧ p2) ∧ (p5 ∧ (True ∨ p4)))) → True) ∨ p1) → p3) ∨ p4))) ∨ (p1 → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49205272842553325194943087838 : (((((p4 ∨ p1) ∨ p2) → ((p4 ∨ ((p2 → False) → (False ∨ p2))) ∧ (p1 → (p1 → (False ∧ (p4 ∧ True)))))) ∨ (True ∨ (p4 ∧ p5))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134336131600639414017022918779 : (((p4 ∧ (((False ∨ (p2 ∧ (((True ∧ p2) ∧ ((p4 ∨ p2) ∧ (p5 ∨ p4))) → (p3 → False)))) ∧ False) ∧ False)) ∨ False) ∨ ((False → False) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228087598013019336931444741804 : ((p4 ∧ (False ∨ p1)) ∨ (((True ∨ p5) → ((p5 ∨ (p4 → (((True → (((p2 → p1) ∧ p1) ∨ p4)) → p2) ∨ True))) → (False ∧ p1))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_26818902759544680663188756208 : (((False ∨ p5) ∨ (p2 ∨ ((((False ∧ (False → p4)) ∧ ((p2 ∧ p1) → ((p5 ∨ (p5 → p3)) ∧ p1))) ∨ (True ∨ (p4 ∧ False))) ∨ p1))) ∧ True) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206494787882141961965773033954 : ((p5 ∨ ((True ∨ p3) ∧ (True ∧ p4))) ∨ ((((p2 ∨ ((((False ∧ (p4 ∨ (p3 ∧ True))) ∧ p4) → p1) ∧ p5)) → True) → (p3 ∨ False)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_764899404977033437434283608249 : (((p4 ∧ ((((p5 ∨ ((p4 ∨ (p3 ∨ p1)) ∧ True)) → p5) → ((p1 ∧ ((True → p4) → (True ∨ True))) → ((True → p5) ∨ p2))) → p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263113556127326699249304665506 : (True ∧ ((((p3 → (p4 ∨ p5)) ∨ (p4 ∨ (p5 → ((p4 ∨ (True → True)) → (p5 ∧ p2))))) ∧ (p5 ∧ (p3 ∧ (p2 → p2)))) ∨ (p4 → p4))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42817521636059861966933580895 : (((p1 → (((p4 → (((True → p2) ∨ p1) ∧ (((p5 → p1) → (p4 → p4)) ∧ p2))) → True) → ((p2 ∧ (p4 ∨ p2)) ∧ p5))) ∨ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_786961540344454011292051952047 : (((p4 ∨ ((p2 ∧ True) ∧ ((p3 ∧ p3) ∨ (p3 ∨ ((True → p2) ∨ (((True ∨ p4) ∧ p1) → (((p3 → p2) ∨ (p4 ∧ False)) → True))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



