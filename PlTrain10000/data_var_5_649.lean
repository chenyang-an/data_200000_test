variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_722187744452452791594102604555 : ((((p4 → (False ∨ (p1 → p1))) → ((p4 ∨ (p5 ∨ p5)) ∧ ((((p4 → (p2 → p2)) ∧ (p3 → (p1 ∧ p3))) ∧ p3) → (p2 → p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_664307583712177786704261777748 : ((((p2 ∨ (((((((False ∨ p5) ∧ p3) → (True ∨ (False ∨ p4))) ∨ (p2 → False)) → (p1 ∧ p4)) ∧ p3) ∧ (p5 → p3))) → (p5 ∨ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50174396024942536219612942664 : (((((p5 ∨ ((((p2 ∧ ((False ∨ p4) ∨ True)) ∧ p3) ∧ ((True ∧ p3) ∨ p1)) → False)) ∨ True) ∧ p2) ∨ (p2 ∧ ((p4 ∧ p1) ∨ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313011487202925132958244936016 : (p3 ∨ ((((((p1 ∧ p3) → (p3 → p1)) ∨ p2) → ((((p2 ∨ p2) → p3) ∨ p1) ∧ (p3 → (p4 ∨ ((p1 → p4) ∧ p1))))) ∨ True) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_264102711216756786813746363056 : (True ∧ (((p1 → (False ∧ p3)) ∧ (((p3 ∧ p5) → p4) ∨ False)) → (((p3 ∧ p4) → False) ∨ ((True ∧ True) → (((p3 ∨ p5) → p3) ∨ True))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h8 =>
    -- False on the left can always be used.
    apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350027056950933997276236192533 : (p4 → (((((p4 ∧ ((p4 ∧ p5) → False)) → (p2 ∧ ((p3 ∨ p4) ∨ ((((p3 ∧ True) → p5) ∧ True) → p4)))) → (p2 ∧ p4)) → p2) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161251024594497730308216232242 : (((True ∨ False) → (((((False ∨ p2) ∨ p3) ∨ p1) ∧ (((False → p2) ∧ p5) ∧ (p2 ∨ p5))) ∨ p5)) → (((p3 ∨ p3) ∧ p1) → (False ∨ p5))) := by
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
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h6 : (True ∨ False) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h7 := h1 h6
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h11 =>
        -- Disjunctions on the left can always be decomposed.
        cases h11
        case inl h12 =>
          -- Disjunctions on the left can always be decomposed.
          cases h12
          case inl h13 =>
            -- False on the left can always be used.
            apply False.elim h13
          case inr h14 =>
            -- Conjunctions on the left can always be decomposed.
            let h15 := h10.left
            let h16 := h10.right
            -- Conjunctions on the left can always be decomposed.
            let h17 := h15.left
            let h18 := h15.right
            -- Disjunctions on the left can always be decomposed.
            cases h16
            case inl h19 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- One of the premise coincides with the conclusion.
              exact h18
            case inr h20 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- One of the premise coincides with the conclusion.
              exact h20
        case inr h21 =>
          -- Conjunctions on the left can always be decomposed.
          let h22 := h10.left
          let h23 := h10.right
          -- Conjunctions on the left can always be decomposed.
          let h24 := h22.left
          let h25 := h22.right
          -- Disjunctions on the left can always be decomposed.
          cases h23
          case inl h26 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h25
          case inr h27 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h27
      case inr h28 =>
        -- Conjunctions on the left can always be decomposed.
        let h29 := h10.left
        let h30 := h10.right
        -- Conjunctions on the left can always be decomposed.
        let h31 := h29.left
        let h32 := h29.right
        -- Disjunctions on the left can always be decomposed.
        cases h30
        case inl h33 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h32
        case inr h34 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h34
    case inr h35 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h35
  case inr h36 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h37 : (True ∨ False) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h38 := h1 h37
    -- Disjunctions on the left can always be decomposed.
    cases h38
    case inl h39 =>
      -- Conjunctions on the left can always be decomposed.
      let h40 := h39.left
      let h41 := h39.right
      -- Disjunctions on the left can always be decomposed.
      cases h40
      case inl h42 =>
        -- Disjunctions on the left can always be decomposed.
        cases h42
        case inl h43 =>
          -- Disjunctions on the left can always be decomposed.
          cases h43
          case inl h44 =>
            -- False on the left can always be used.
            apply False.elim h44
          case inr h45 =>
            -- Conjunctions on the left can always be decomposed.
            let h46 := h41.left
            let h47 := h41.right
            -- Conjunctions on the left can always be decomposed.
            let h48 := h46.left
            let h49 := h46.right
            -- Disjunctions on the left can always be decomposed.
            cases h47
            case inl h50 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- One of the premise coincides with the conclusion.
              exact h49
            case inr h51 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- One of the premise coincides with the conclusion.
              exact h51
        case inr h52 =>
          -- Conjunctions on the left can always be decomposed.
          let h53 := h41.left
          let h54 := h41.right
          -- Conjunctions on the left can always be decomposed.
          let h55 := h53.left
          let h56 := h53.right
          -- Disjunctions on the left can always be decomposed.
          cases h54
          case inl h57 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h56
          case inr h58 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h58
      case inr h59 =>
        -- Conjunctions on the left can always be decomposed.
        let h60 := h41.left
        let h61 := h41.right
        -- Conjunctions on the left can always be decomposed.
        let h62 := h60.left
        let h63 := h60.right
        -- Disjunctions on the left can always be decomposed.
        cases h61
        case inl h64 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h63
        case inr h65 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h65
    case inr h66 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h66



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246145244544690583953267869324 : ((p4 ∧ p2) ∨ ((((p4 ∨ False) ∨ ((((p1 ∧ ((((p2 ∨ p2) ∧ (p3 ∧ p1)) → p1) ∧ False)) ∨ True) ∨ p2) ∨ p1)) → False) → (p2 → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : ((p4 ∨ False) ∨ ((((p1 ∧ ((((p2 ∨ p2) ∧ (p3 ∧ p1)) → p1) ∧ False)) ∨ True) ∨ p2) ∨ p1)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213186617787321186799769070617 : ((((p3 ∨ p1) ∨ p3) ∧ p5) ∨ ((((p5 ∧ p5) ∧ (True → (p4 ∨ p1))) ∨ p5) ∨ ((p5 ∧ ((p2 ∨ p2) ∨ ((True → p1) ∧ p5))) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_671304579805834675558097702140 : ((((p5 ∨ (p4 ∨ ((False ∧ (p5 ∨ (p2 ∧ ((True ∧ p5) ∨ False)))) ∧ (((p3 ∧ p2) → p3) ∨ (p4 ∨ True))))) ∨ (False → (p1 ∨ p2))) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_784634876492670386670574259858 : (((p3 ∨ (p2 ∨ (p5 ∨ (((p2 → ((((p1 ∧ p5) ∧ True) ∨ p4) ∧ (True ∧ p3))) ∨ p1) ∧ (((True → (p4 ∧ p4)) → p5) ∧ p5))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_634044788318698129965230451456 : ((((((p3 ∨ (((True → p1) ∧ p1) ∧ ((True ∧ (False → (p5 → p5))) ∧ p2))) ∨ (p4 → (p5 ∧ (p5 → p4)))) → (p1 ∧ True)) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59152397887671306841026241187 : (((False ∨ False) ∨ (p5 ∨ (p3 ∨ ((p2 → ((((False → (p4 → True)) → False) → (p3 ∧ ((p1 → p1) ∨ (p1 → p1)))) → p1)) ∧ p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_744227002444632408942043017186 : ((((p1 ∧ p2) → (((False ∧ p4) ∧ ((p1 ∨ p4) ∨ (p3 → False))) ∨ ((p1 ∧ p2) → ((True → (p3 ∧ True)) ∧ ((p5 ∨ p5) ∨ p3))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55140542784346991949521673619 : (((((p1 ∧ (p3 ∧ p4)) ∧ p4) ∨ p2) ∨ ((((((p4 → p5) ∨ (p1 ∧ p1)) ∨ (False ∧ (p2 ∧ p4))) ∨ True) → p1) ∨ (p1 ∧ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53348300482214212197081214499 : ((((False → (p2 ∧ (p3 → ((False ∨ p3) ∧ (True ∧ p4))))) ∧ p5) → (((p1 ∨ (p2 ∧ (p4 ∨ p3))) → p4) → ((True → p3) ∨ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_695349223168611337704173941446 : (((((p3 ∨ ((p3 → (p3 ∧ (p1 ∧ (True → (p2 ∧ p4))))) ∨ p5)) → p3) → ((((p3 ∧ p5) → False) ∧ (p3 ∧ (False ∨ True))) → p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_142184818929766475250800667150 : ((p1 ∧ ((p1 → (p4 ∧ ((p5 ∧ p2) ∨ (((p1 ∨ ((False → p2) ∧ False)) ∧ p3) ∨ (True → (p5 ∧ p5)))))) ∨ p4)) → ((p5 → p2) ∨ True)) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137623571456485185873944901589 : ((False ∨ ((((((True ∨ p3) → p3) ∧ (False ∨ ((p3 → (p5 → False)) ∨ ((False → p3) ∧ False)))) ∧ False) → p1) → p5)) ∨ (p4 ∨ (p4 → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_163041787508769671205044769516 : (((p2 ∨ ((False ∨ (p4 ∧ ((True ∨ (p3 → True)) ∨ False))) ∨ p1)) ∨ (p5 → (True ∨ p4))) ∧ (p2 ∨ ((True ∧ (p5 ∨ p1)) → (True ∨ p3)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_252642012404348272994874672590 : ((p5 → p4) ∨ (((p2 → ((True ∧ p4) ∧ ((p1 ∨ (p1 ∨ (p1 ∨ p1))) ∨ (False ∨ p5)))) ∧ (True ∨ ((False ∧ p2) ∧ p2))) ∨ (p2 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_175363232393447248379361482595 : ((p5 ∨ (p4 ∨ ((True ∨ True) → (p1 → ((p3 → p3) → ((True ∧ True) ∨ p2)))))) → (p2 ∨ (p5 → ((((p2 → True) ∧ p2) ∧ p5) ∨ True)))) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136531395709140547035538219403 : (((p1 → (p1 → p1)) ∧ (((False ∧ (p5 ∨ (p5 ∧ p1))) ∧ (p1 ∨ (p1 ∧ p5))) ∨ (p5 ∧ (p4 ∨ (p1 → p5))))) ∨ ((False → p2) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38874202368315553318658275879 : ((((p3 → (p3 → False)) ∧ ((p4 → (((((True ∧ ((p3 ∧ False) ∧ p2)) ∨ p1) ∧ p4) → p3) → (p2 → (True ∧ p3)))) → p1)) ∧ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_170036724685456873176890455674 : (((p3 ∧ ((False ∧ ((p5 ∨ p5) → (p4 → p3))) ∧ p5)) ∨ (p1 → (p1 ∨ p4))) ∧ (False → ((p5 ∧ ((p4 ∨ p5) → (p3 ∨ p4))) ∧ False))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- False on the left can always be used.
    apply False.elim h2
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338363652734256464777136278158 : (p1 → (((p4 → p4) ∧ (p5 ∨ p3)) ∨ (((((((p4 ∨ ((p3 ∧ p1) ∧ p4)) ∧ ((p1 → p3) → False)) → p4) → p2) ∨ False) ∨ False) ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354621828264308211289927185892 : (p5 → (((((p3 ∨ p1) ∨ p5) → (((True → True) → ((p3 ∨ p1) → (True ∧ p3))) ∧ (((p4 ∧ p1) ∧ (p4 ∧ False)) ∨ p4))) ∨ False) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135143703665824801557594528605 : (((p3 ∨ ((True ∧ p2) → ((p1 ∨ (p1 ∨ p3)) ∧ ((p2 → (False ∨ ((True ∨ p5) → False))) ∨ False)))) ∨ (p4 ∨ p4)) ∨ ((False → p1) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_705086205380982375210266476897 : ((((p4 → (False → (p4 ∨ (p2 → (p1 ∨ (p4 ∧ p5)))))) → (((p5 ∧ ((p2 ∧ p3) → False)) → p4) ∨ ((True ∧ p4) ∨ (False → True)))) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_255691925794609423987457336223 : ((p5 ∧ p5) → ((p2 → (False ∧ ((False ∧ (p4 ∧ p3)) ∨ False))) ∨ ((((True → (False ∧ p5)) → True) ∨ (p3 ∨ (p4 ∨ p1))) ∧ (True ∨ False)))) := by
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
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137071859357671700273994196117 : (((p4 → p2) → (p3 ∨ (p3 ∧ ((p2 ∧ (((p2 ∨ (p3 ∨ (p1 ∧ ((p3 → p5) ∨ p5)))) → p4) ∨ False)) ∨ True)))) ∨ (True → (p4 → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117549357468524367052674038080 : ((p2 ∧ ((((p2 ∨ p3) ∨ (p5 ∧ ((p1 ∨ (p3 ∧ (p4 ∨ False))) ∨ True))) ∨ False) ∧ (p1 ∨ (p4 ∧ ((p3 ∨ p2) ∨ p1))))) ∨ (True ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172294692376694734746537409665 : (((((p4 → p3) ∧ ((False ∧ p1) → p5)) ∨ p5) → ((p2 ∧ p4) ∧ (p5 ∨ True))) ∨ ((p4 → ((False → p1) ∨ (p2 → (p1 ∧ False)))) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47900460430436093171935983187 : ((((p2 → (True ∧ ((((p3 ∧ p3) → p3) ∨ ((False → (((p2 ∧ p5) ∨ True) ∧ p1)) ∧ p5)) ∧ p2))) ∨ (p1 ∧ False)) → (p2 ∧ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149423945381220296648579458299 : ((True ∧ ((p5 ∧ p5) → ((p5 → (((p1 → p4) ∨ p5) → (p5 ∨ ((p4 → p5) ∨ p5)))) → (True ∧ p1)))) ∨ (p3 → (p1 → (p3 ∨ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213232578190912207063117695069 : ((((p1 ∧ p5) → False) ∧ p5) ∨ (((True ∧ True) ∧ (p1 → False)) → (((p1 → True) → p5) → ((((True ∧ p3) ∧ (p1 → p4)) ∧ p4) ∨ p5)))) := by
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
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h7 : (p1 → True) := by
    -- Implications on the right can always be decomposed.
    intro h8
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h9 := h2 h7
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61000986077692419241513039009 : ((False ∧ (((True → ((p5 → p2) ∨ ((((True ∧ p4) ∨ ((p5 ∧ True) ∧ p3)) → p2) ∧ False))) → ((p5 → False) ∧ (p2 ∧ p4))) → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_614251401304008712409603346706 : (((((((((False ∧ False) ∧ (p4 → (p3 → True))) → p2) ∧ (p2 ∧ (p1 ∧ False))) ∨ ((True → True) ∨ False)) → (p1 ∧ (p4 → p3))) ∨ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159478464546708477800297687810 : ((((p2 → (p3 ∨ (p3 ∨ (p5 → p1)))) → (p4 ∨ (True ∨ ((True ∨ p2) ∧ (p3 → True))))) ∧ p2) → (((p5 ∧ True) ∨ (p1 → p5)) ∨ True)) := by
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
theorem thm_5_vars_56145124150725395248221067967 : ((((p4 ∨ p4) → (p3 ∨ p3)) ∨ (p3 ∧ (p3 → ((True ∨ ((((p1 ∨ True) ∨ (p5 → (False ∧ (p3 ∨ True)))) ∨ p5) ∨ p4)) ∨ True)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_89302772592674552885067264355 : (((False ∨ (p4 → p3)) ∧ (((p4 → p2) ∧ p4) ∧ ((p3 → ((False → False) ∧ p4)) ∧ (p2 → (p3 → (p2 → ((p1 → p2) → p1))))))) → p2) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h3.left
    let h7 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h6.left
    let h9 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h7.left
    let h11 := h7.right
    -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
    have h12 : p4 := by
      -- One of the premise coincides with the conclusion.
      exact h9
    -- We have shown the premise of h8, we can now drive its conclusion.
    let h13 := h8 h12
    -- One of the premise coincides with the conclusion.
    exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_124305643152068567689062817833 : ((((p5 ∨ (p5 → (p5 ∨ p3))) → (p4 ∧ False)) ∧ (p3 ∨ (p5 → (((((p2 ∨ p5) ∧ p5) ∧ p1) ∨ True) ∧ (p2 ∨ p2))))) → (p2 ∧ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h5 : (p5 ∨ (p5 → (p5 ∨ p3))) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h6
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h7 := h2 h5
    -- We need to get the right conjuct of h7 based on <expert-advice>.
    let h8 := h7.right
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h10 : (p5 ∨ (p5 → (p5 ∨ p3))) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h11
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h11
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h12 := h2 h10
    -- We need to get the right conjuct of h12 based on <expert-advice>.
    let h13 := h12.right
    -- False on the left can always be used.
    apply False.elim h13
  -- Conjunctions on the left can always be decomposed.
  let h14 := h1.left
  let h15 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h15
  case inl h16 =>
    -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
    have h17 : (p5 ∨ (p5 → (p5 ∨ p3))) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h18
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h18
    -- We have shown the premise of h14, we can now drive its conclusion.
    let h19 := h14 h17
    -- We need to get the left conjuct of h19 based on <expert-advice>.
    let h20 := h19.left
    -- One of the premise coincides with the conclusion.
    exact h20
  case inr h21 =>
    -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
    have h22 : (p5 ∨ (p5 → (p5 ∨ p3))) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h23
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h23
    -- We have shown the premise of h14, we can now drive its conclusion.
    let h24 := h14 h22
    -- We need to get the left conjuct of h24 based on <expert-advice>.
    let h25 := h24.left
    -- One of the premise coincides with the conclusion.
    exact h25



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185532310067764458826982262769 : ((p3 ∨ (((p5 ∨ p1) ∨ p5) → (p2 ∧ (p4 → (p3 ∨ p1))))) ∨ (True ∧ (((p2 → ((((p3 ∨ p2) ∨ p3) ∨ p1) ∨ p3)) → True) ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66216902415051584004656966338 : ((p5 ∨ ((((False ∨ (p1 → (p5 ∨ p3))) ∧ (p1 → p3)) ∧ (True ∨ p3)) → ((p5 → ((p2 → p3) ∨ (p5 → (p2 → p5)))) ∨ False))) ∨ p2) := by
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
  let h4 := h2.left
  let h5 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h8 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h9
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- Implications on the right can always be decomposed.
      intro h11
      -- One of the premise coincides with the conclusion.
      exact h10
    case inr h12 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h13
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h14
      -- One of the premise coincides with the conclusion.
      exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_353763034149441646627944332263 : (p4 → (True → (True → (((p4 ∨ (p3 ∨ p5)) ∧ p1) ∨ (((True ∨ p2) → (((p4 ∧ p2) ∨ (p2 ∨ (p5 ∧ p4))) ∨ p5)) ∨ (True ∨ p4)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113007708108876941840417560235 : (((p4 ∧ (p2 ∧ ((((((False → p3) ∧ p4) → True) → (p3 → (p3 ∧ p1))) ∧ (p3 → p3)) ∧ ((p4 → p4) ∨ p3)))) → False) ∨ (False → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61959953899571054636729223699 : ((p2 ∧ (((False ∧ (False ∧ (p1 ∨ ((False ∧ p4) → False)))) ∨ (p5 → p2)) ∧ (((p4 ∨ ((p2 → False) ∧ p5)) → (p4 ∧ p4)) ∨ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167853692102032854425807605698 : (((False ∨ (p2 ∨ (p2 → (p1 → ((p1 → p4) → p5))))) ∨ (False → ((p3 ∨ False) ∨ p2))) → ((p1 ∨ (p2 ∧ (p4 ∨ (p5 ∨ False)))) ∨ True)) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h5 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h6 =>
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
theorem thm_5_vars_246212666491810941274934975932 : ((p4 ∧ p3) ∨ ((False ∨ (((p5 ∧ p4) → (((False → (p2 → p2)) → (p3 ∨ p2)) ∧ True)) ∨ True)) ∨ ((p5 → (p3 ∨ (True ∧ p2))) ∧ True))) := by
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
theorem thm_5_vars_330611458815783584329989833249 : (True → (True → (((p4 ∨ (p4 ∧ (p3 ∧ ((p2 → p1) → (p1 ∨ p1))))) → (((((p5 ∧ p1) ∧ p1) → p2) ∧ p2) → p1)) ∨ (p3 → p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179863250343008408852886927557 : (((p1 → ((True ∧ ((p1 → (p1 → p2)) ∨ False)) ∨ (p1 → p1))) ∧ p3) → (((False ∨ (((p3 → (False → True)) ∧ p5) → p4)) ∨ p3) ∨ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63932797450080083591392566055 : ((False ∨ ((((((False ∧ p1) ∨ (False ∨ (True → p1))) ∧ p5) → (True → (((p3 → (p2 ∨ p2)) → p4) ∨ p2))) ∨ (p2 ∨ p3)) ∨ True)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_69466997840607153344539285252 : (((((((p3 ∨ ((True ∨ (p2 → False)) ∧ p5)) ∧ ((p2 ∧ (p1 ∨ p2)) ∨ (p2 ∨ (p1 ∨ p5)))) ∨ (False ∨ p4)) → False) ∧ p5) ∧ True) → p3) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h6 : (((p3 ∨ ((True ∨ (p2 → False)) ∧ p5)) ∧ ((p2 ∧ (p1 ∨ p2)) ∨ (p2 ∨ (p1 ∨ p5)))) ∨ (False ∨ p4)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
    -- One of the premise coincides with the conclusion.
    exact h5
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h7 := h4 h6
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_653975926699108506150997374364 : (((((p2 ∧ ((True → p3) ∧ (p5 ∨ (p3 ∧ (((True ∧ p2) ∨ p5) ∨ (((p5 → False) → (p3 ∨ True)) ∨ p4)))))) ∧ p4) ∨ (p3 ∨ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192230851895525958446256311500 : ((((p2 ∨ ((p3 ∧ p2) → p2)) ∧ (p2 ∨ p1)) ∧ p5) → ((p1 ∧ p2) ∨ ((((p1 ∧ ((p5 ∧ False) → p4)) ∨ p5) → p1) ∨ (p5 ∧ p2)))) := by
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
    cases h5
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h3
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h8 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h8
      -- One of the premise coincides with the conclusion.
      exact h6
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h3
      -- One of the premise coincides with the conclusion.
      exact h10
    case inr h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h12
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- Conjunctions on the left can always be decomposed.
        let h14 := h13.left
        let h15 := h13.right
        -- One of the premise coincides with the conclusion.
        exact h14
      case inr h16 =>
        -- One of the premise coincides with the conclusion.
        exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_680611789178971385446790814574 : (((((p3 → ((((p5 → p5) ∨ p4) ∧ True) → True)) → ((True ∧ False) ∨ (p4 ∧ (True ∨ (p1 → p3))))) → ((p4 → (p3 ∧ False)) → p1)) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : (p3 → ((((p5 → p5) ∨ p4) ∧ True) → True)) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h3
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- False on the left can always be used.
    apply False.elim h9
  case inr h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h13 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h14 : p4 := by
        -- One of the premise coincides with the conclusion.
        exact h11
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h15 := h2 h14
      -- We need to get the right conjuct of h15 based on <expert-advice>.
      let h16 := h15.right
      -- False on the left can always be used.
      apply False.elim h16
    case inr h17 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h18 : p4 := by
        -- One of the premise coincides with the conclusion.
        exact h11
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h19 := h2 h18
      -- We need to get the right conjuct of h19 based on <expert-advice>.
      let h20 := h19.right
      -- False on the left can always be used.
      apply False.elim h20
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137822180323770671591280848818 : ((p3 ∨ ((((True ∧ (((p4 ∧ p1) ∨ (True ∧ (p2 → p4))) → p3)) ∧ (((p1 ∨ p3) → False) ∨ False)) → p4) → p4)) ∨ (False → (p1 ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_82197718103937379992709595148 : (((p5 → (((p4 ∧ (p5 → False)) ∨ ((p4 → ((p3 → True) ∧ (p2 → p2))) → ((p5 → p4) ∨ p3))) ∨ p5)) → ((p1 → p1) ∧ False)) → p3) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p5 → (((p4 ∧ (p5 → False)) ∨ ((p4 → ((p3 → True) ∧ (p2 → p2))) → ((p5 → p4) ∨ p3))) ∨ p5)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172539872759913172119333455107 : ((((p5 ∧ p1) ∧ p4) ∨ ((((p5 ∨ p3) ∧ (False → (p4 → p4))) ∧ p1) ∨ p4)) ∨ (((p1 ∧ ((p2 ∧ p1) → p1)) ∨ False) → (True ∨ p1))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_382017573446756283987106603167 : ((((((p4 ∧ ((p4 → False) ∨ ((((p4 ∨ p3) ∧ True) ∧ ((p2 ∨ (p5 ∧ (p5 ∨ p3))) → (p1 ∧ True))) ∧ p5))) → p3) ∨ True) ∨ p1) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_893599947152830152899063313690 : ((((((p5 → True) → False) ∧ (((((((p2 ∧ p5) → p1) ∧ (p3 ∨ p1)) → p3) → True) ∧ (p4 ∧ False)) → p4)) ∧ (p2 → (p1 → p4))) → p1) ∧ True) := by
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
  have h6 : (p5 → True) := by
    -- Implications on the right can always be decomposed.
    intro h7
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h8 := h4 h6
  -- False on the left can always be used.
  apply False.elim h8
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178428822741613425719907153845 : (((((p2 ∧ ((p2 ∨ p5) → False)) ∨ p1) ∧ p3) ∧ (p4 ∧ (p5 ∨ False))) ∨ ((p2 ∨ True) → (((p3 → True) ∨ ((False ∨ p5) ∨ p4)) ∨ True))) := by
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
theorem thm_5_vars_585467568939301913384358182407 : (((((((((p3 ∨ (False ∨ p3)) → (((((True ∧ p2) → p3) ∧ (p5 ∨ p4)) ∧ p1) ∧ (p3 ∨ False))) ∨ p5) ∧ p3) ∨ False) ∧ False) ∧ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300050033764543791278072385047 : (False ∨ (((((p3 ∨ (p3 ∨ p3)) ∧ ((p3 → ((True ∧ ((((p1 ∨ p5) ∨ p4) ∧ p3) → p4)) → p5)) ∧ p3)) ∧ True) ∧ p1) ∨ (True ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135081447621028666611053909387 : ((((p4 ∧ (False ∨ (p3 ∧ ((((True → p2) → (p4 ∧ True)) ∧ True) ∧ p1)))) ∨ ((p2 ∨ p3) ∨ p3)) ∨ (p4 ∧ False)) ∨ ((p5 ∨ p2) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319097481546433318252232334965 : (p4 ∨ (((True → (p2 → True)) ∧ (((((p1 → (False ∧ p2)) ∧ p2) ∧ p4) → p4) → (p5 ∧ (False ∧ p2)))) → (p1 ∧ ((False → p3) → p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : ((((p1 → (False ∧ p2)) ∧ p2) ∧ p4) → p4) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h6.left
    let h9 := h6.right
    -- One of the premise coincides with the conclusion.
    exact h7
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h10 := h3 h4
  -- We need to get the right conjuct of h10 based on <expert-advice>.
  let h11 := h10.right
  -- We need to get the left conjuct of h11 based on <expert-advice>.
  let h12 := h11.left
  -- False on the left can always be used.
  apply False.elim h12
  -- Implications on the right can always be decomposed.
  intro h13
  -- Conjunctions on the left can always be decomposed.
  let h14 := h1.left
  let h15 := h1.right
  -- We want to use the implication h15 based on <expert-advice>. So we show its premise.
  have h16 : ((((p1 → (False ∧ p2)) ∧ p2) ∧ p4) → p4) := by
    -- Implications on the right can always be decomposed.
    intro h17
    -- Conjunctions on the left can always be decomposed.
    let h18 := h17.left
    let h19 := h17.right
    -- Conjunctions on the left can always be decomposed.
    let h20 := h18.left
    let h21 := h18.right
    -- One of the premise coincides with the conclusion.
    exact h19
  -- We have shown the premise of h15, we can now drive its conclusion.
  let h22 := h15 h16
  -- We need to get the right conjuct of h22 based on <expert-advice>.
  let h23 := h22.right
  -- We need to get the left conjuct of h23 based on <expert-advice>.
  let h24 := h23.left
  -- False on the left can always be used.
  apply False.elim h24



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165400545259489011703977435219 : (((p2 → ((((p1 ∨ p4) ∧ False) ∨ (False ∧ (p2 ∨ p2))) ∧ False)) ∨ ((p1 ∨ p1) → p3)) ∨ ((p5 ∨ (True → (p1 → (p3 → True)))) ∨ p4)) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64956809461290679719330202487 : ((p2 ∨ (((p3 ∨ (p3 ∨ ((p4 ∨ False) ∨ p1))) → p1) ∨ (False ∨ (((((p4 ∧ p2) ∨ False) ∨ p5) ∧ True) ∨ ((p1 ∧ p1) → True))))) ∨ p2) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198387172943128163107647663976 : ((p3 ∧ ((True ∨ p5) → (p3 → (p1 ∧ p1)))) ∨ (((p3 ∧ (p3 ∨ (p1 → p3))) ∨ (((False ∧ False) ∧ (p4 ∧ (p1 ∨ p4))) ∧ p3)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_826738219304572415294451204606 : (((((p1 → p1) → ((p1 ∧ ((((p3 ∧ p1) ∧ p4) → ((p5 → p3) ∧ (p4 ∨ ((p3 ∨ True) ∨ True)))) ∧ p5)) ∧ (p2 ∧ False))) ∧ p2) → False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (p1 → p1) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h4
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- False on the left can always be used.
  apply False.elim h8
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_782412255755325094062138089751 : (((p3 ∨ (((((p4 ∨ True) ∧ (p2 → (((p3 ∨ ((p4 ∨ p4) ∨ False)) → p5) → p1))) ∨ ((p3 ∨ p4) → p3)) ∧ (p3 ∧ p1)) ∨ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_645276430789263557694399259928 : ((((p3 ∨ (False → ((p2 ∨ p3) ∨ (p4 ∧ (((p2 → True) ∧ (p3 ∨ (((p5 → ((p4 ∨ p2) ∨ True)) ∨ p5) ∧ False))) ∧ True))))) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50409079732185218656325013580 : (((False ∧ ((p3 ∧ (p1 → ((True ∧ p5) → p3))) ∨ ((p3 → ((p1 ∧ p1) ∧ (p5 ∧ p4))) ∨ p3))) ∨ ((p4 → (p3 ∨ p3)) ∧ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_139595093956213892944313157468 : ((((p3 ∨ (p2 ∨ ((p2 ∨ p2) ∧ ((p1 ∨ p2) ∧ (p1 ∨ (p1 → p5)))))) ∨ (p2 → ((p1 ∧ p4) ∨ p5))) → False) → (p5 → (p5 ∧ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : ((p3 ∨ (p2 ∨ ((p2 ∨ p2) ∧ ((p1 ∨ p2) ∧ (p1 ∨ (p1 → p5)))))) ∨ (p2 → ((p1 ∧ p4) ∨ p5))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h3
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200512264406479082658667397764 : (((False ∨ False) → (((True ∨ True) ∧ p4) ∧ False)) → ((False ∨ (((p3 ∨ False) ∧ ((p5 ∧ p5) → (p1 → p5))) → ((True → False) → p5))) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h7 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h8 := h3 h7
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- False on the left can always be used.
    apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191323668591206546148522756439 : (((p1 ∧ p2) ∨ (((p3 ∧ True) ∨ (p3 ∨ p1)) ∨ True)) ∨ (p5 → (((((((p4 ∧ p1) ∧ p1) ∨ False) ∧ (True ∧ p3)) → p3) ∨ p5) ∨ p3))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232821020916178281549192108049 : ((p2 ∧ (p2 ∨ True)) → (((p1 ∧ p4) ∧ p1) ∨ (True ∨ ((False → (p4 ∧ p5)) ∨ (p3 ∧ (((p5 ∧ ((p4 ∨ p4) → p5)) ∨ p3) ∧ p2)))))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_735567271204597450543098133470 : ((((p5 ∨ True) ∧ ((((p4 ∨ ((p5 ∧ False) ∧ p4)) → p3) ∨ p2) ∨ ((((p3 ∧ p4) → p5) ∧ ((p1 ∨ p1) ∧ p4)) ∨ (False → p2)))) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165683985622755109884562094546 : ((((p5 → (False ∨ p2)) ∧ (p5 → p5)) → (((((p2 → p3) ∧ p2) ∧ p4) → False) → p4)) ∨ ((False → p1) → ((p1 ∨ True) ∨ (p5 ∨ p2)))) := by
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
theorem thm_5_vars_663177862514967268089108064325 : (((((p1 → p4) ∧ (((True ∧ ((p3 ∨ ((True ∧ p5) → p3)) ∧ ((p2 → p2) → (p3 ∧ p5)))) → (True ∧ p2)) ∧ p4)) → (p1 ∨ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197451130545014549139604923668 : ((((False ∨ (p1 → p4)) ∨ p2) ∧ (p4 ∧ p1)) ∨ (p2 → (((True ∧ True) ∨ (True ∧ p4)) → (((False ∨ p5) ∧ p1) ∨ (p5 ∨ (p1 → True)))))) := by
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
    let h4 := h3.left
    let h5 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h10
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218769342651885699899376028934 : ((p1 ∧ ((True ∨ True) ∨ False)) → ((((p3 ∧ p5) ∧ (((True ∧ True) → ((p2 ∧ p3) ∨ p3)) ∧ p5)) ∨ (p1 ∨ (p4 ∨ (p1 → p2)))) ∨ True)) := by
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
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h7 =>
    -- False on the left can always be used.
    apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_352809007341804491377129305233 : (p4 → ((p4 ∨ p1) → (p1 → (False ∨ (False ∨ (((p1 ∨ (False ∧ p4)) → (False ∧ ((p4 ∧ ((p4 ∨ p1) ∧ p4)) ∨ p5))) ∨ (False → p3))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- False on the left can always be used.
    apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337858149503329433337302658803 : (p1 → (((((p4 ∨ (p1 ∧ (p4 ∧ (p3 ∨ p3)))) ∧ p5) → False) ∨ (False ∨ p5)) ∨ (p1 ∧ ((p5 ∨ (p3 ∧ p1)) → (p1 ∨ (p5 ∧ p3)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173139445282898044213580374523 : ((p3 ∨ (((p1 ∨ p1) ∨ ((((p4 → True) ∨ (p1 → p4)) ∧ False) ∧ False)) ∨ p5)) ∨ (((False ∨ p4) → ((p3 → p4) ∨ p4)) ∨ (p1 ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233880626970286731714467607986 : ((p4 ∨ (p1 ∨ p2)) → ((p3 ∧ p3) ∨ (((p3 ∧ ((p4 ∨ p1) ∧ (p2 → p3))) → (((False ∨ True) → p3) ∧ (p5 ∧ (p4 ∧ p4)))) → True))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_668417587592318198565254058196 : (((((((((False ∧ ((p5 ∧ p5) ∨ p3)) ∨ True) ∨ False) ∨ ((p5 ∧ ((p4 → False) ∨ p2)) ∧ p5)) ∨ p2) ∧ p4) ∨ (p5 ∨ (p5 ∨ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_222215015943857651722490134400 : (((p5 ∨ p5) → p5) ∧ (((p1 ∨ p3) ∧ True) ∨ ((p1 ∨ (p5 ∨ ((True ∧ p2) ∧ p5))) ∨ ((False → ((True ∧ p4) ∨ (p5 ∧ p3))) ∨ True)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168622330358939138149237482587 : ((p3 ∧ (p1 ∧ ((p5 → p1) ∧ (((p2 → (False ∧ (p5 ∨ True))) → False) → (False → p3))))) → ((((p1 → p4) ∧ p1) ∨ True) ∨ (p4 → True))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_262209141925550954151456789175 : (True ∧ (((p2 ∨ ((p4 ∨ (((((p1 ∨ (p5 → p4)) ∧ (p1 ∧ p5)) → False) ∨ ((False ∧ False) → (p5 ∧ p4))) → True)) ∨ p4)) → p4) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205211069029531366190626991634 : (((p5 → (p3 ∧ p2)) ∧ (p4 ∨ True)) ∨ (p3 ∨ ((p5 ∧ (((((p1 → p2) → p5) → ((p2 → p1) → p5)) ∧ p3) → p2)) ∨ (p5 → p5)))) := by
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
theorem thm_5_vars_52392954392007896305306100265 : (((((p4 → True) ∨ ((p2 ∧ True) ∨ True)) → (False → ((p3 → p5) ∧ False))) ∧ (p3 ∧ (((p2 ∧ p4) ∧ (p2 → False)) ∧ (p3 ∧ False)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47052301653936624669036403667 : ((((p3 → (((p1 → False) ∧ (p4 → (p5 ∧ p2))) → (((p2 ∧ (p4 ∨ (p5 → p4))) ∨ p3) ∨ p5))) ∧ (p4 ∨ p3)) ∨ (False ∨ True)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181517481570954339463212593288 : ((True → ((p1 ∧ ((p3 → ((False ∨ p4) ∧ (p2 ∧ False))) → False)) ∧ False)) → ((False ∧ (p3 → p1)) ∧ (p2 → ((p2 → False) ∨ (p1 → p2))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Implications on the right can always be decomposed.
  intro h5
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h6 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h7 := h1 h6
  -- We need to get the left conjuct of h7 based on <expert-advice>.
  let h8 := h7.left
  -- We need to get the left conjuct of h8 based on <expert-advice>.
  let h9 := h8.left
  -- One of the premise coincides with the conclusion.
  exact h9
  -- Implications on the right can always be decomposed.
  intro h10
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h11 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h12 := h1 h11
  -- We need to get the right conjuct of h12 based on <expert-advice>.
  let h13 := h12.right
  -- False on the left can always be used.
  apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_139865066272238238714890092726 : (((((p4 → (p4 ∨ (p2 ∧ p3))) ∧ (((p2 → (p5 ∧ p4)) ∨ (p1 ∨ p3)) → (False → True))) ∧ p2) ∧ (p3 ∧ p4)) → ((p3 → p5) → p5)) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h9 := h4.left
  let h10 := h4.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h11 : p3 := by
    -- One of the premise coincides with the conclusion.
    exact h9
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h12 := h2 h11
  -- One of the premise coincides with the conclusion.
  exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137726780605555799903379848590 : ((p1 ∨ (p2 ∧ (False ∧ ((p2 → (((p5 ∨ (p5 → (p3 ∧ ((p4 → (p5 → p3)) ∨ True)))) ∨ p2) → p4)) ∨ p2)))) ∨ (True → (True ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190267452424999167597303168347 : ((((((p5 ∨ False) ∨ p2) ∧ (False ∧ p2)) ∨ p3) ∨ True) ∨ (((False → True) ∨ ((((((p2 → p1) → p2) → p5) ∨ p3) ∨ True) ∧ p5)) ∧ p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219368887719694814059892627548 : ((p3 ∨ ((False → p1) ∨ p4)) → ((p3 → (p3 ∧ ((p1 → (p2 ∧ (p5 ∧ False))) → (p4 ∧ (p5 → (p3 ∨ p5)))))) ∨ ((True ∨ False) ∨ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171691369201061939926174806639 : (((True → (((p3 → (p2 ∧ ((p4 → (p5 ∨ p2)) ∨ p5))) ∧ p1) ∧ p4)) ∨ p3) ∨ ((p1 ∨ p4) → (p4 ∨ (True ∨ (True ∧ (p3 ∨ p2)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112620976721795924308933166013 : ((((p2 ∨ (((p3 ∧ ((p4 → (p4 ∨ False)) ∨ p1)) → p4) ∨ ((((p4 → p3) ∧ p2) → p5) ∧ p4))) ∨ (p3 ∨ p3)) → p5) ∨ (p3 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



