variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42578630943816629074234825802 : (((p2 ∨ (((p3 ∧ (p4 ∧ (((False ∧ (False ∨ (p4 ∨ ((p2 ∧ p3) ∨ p1)))) ∨ p2) ∧ p1))) ∧ p4) ∧ (False ∨ (p2 → False)))) ∨ True) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_399720969238659714914264292737 : ((((p3 → (((p1 ∧ (p5 → p1)) → (((p5 ∧ p2) ∧ p2) ∨ (p5 ∧ p1))) ∨ ((((p3 ∨ True) ∧ p4) ∧ p2) → (p1 → p4)))) ∨ p3) ∧ True) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h8 =>
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h9 =>
    -- One of the premise coincides with the conclusion.
    exact h7
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356157353538888077878184898843 : (p5 → ((((p3 → ((p1 → p1) ∨ p1)) → False) ∨ (p3 ∨ (p3 → (((p1 → p3) → p4) ∧ p1)))) ∨ (p1 → ((False ∧ p1) ∨ (True ∨ False))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172827978398244993671107967743 : ((True ∧ (p4 ∧ (p1 ∨ ((((p2 ∨ (True → (p4 → True))) → p1) → p2) ∨ p5)))) ∨ (p3 → (((p3 ∨ p2) ∨ (p5 ∨ (p2 ∨ False))) ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_745757204720389804235527840956 : ((((False ∨ True) → (((p5 → p2) ∨ ((True ∨ ((p4 ∧ ((p5 → False) ∨ p3)) ∨ (p1 ∨ p1))) ∨ (True ∧ False))) → ((p3 ∨ True) ∧ True))) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h4 =>
      -- False on the left can always be used.
      apply False.elim h4
    case inr h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Disjunctions on the left can always be decomposed.
        cases h1
        case inl h9 =>
          -- False on the left can always be used.
          apply False.elim h9
        case inr h10 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h11 =>
        -- Disjunctions on the left can always be decomposed.
        cases h11
        case inl h12 =>
          -- Conjunctions on the left can always be decomposed.
          let h13 := h12.left
          let h14 := h12.right
          -- Disjunctions on the left can always be decomposed.
          cases h14
          case inl h15 =>
            -- Disjunctions on the left can always be decomposed.
            cases h1
            case inl h16 =>
              -- False on the left can always be used.
              apply False.elim h16
            case inr h17 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- True on the right can always be proven directly.
              apply True.intro
          case inr h18 =>
            -- Disjunctions on the left can always be decomposed.
            cases h1
            case inl h19 =>
              -- False on the left can always be used.
              apply False.elim h19
            case inr h20 =>
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- One of the premise coincides with the conclusion.
              exact h18
        case inr h21 =>
          -- Disjunctions on the left can always be decomposed.
          cases h21
          case inl h22 =>
            -- Disjunctions on the left can always be decomposed.
            cases h1
            case inl h23 =>
              -- False on the left can always be used.
              apply False.elim h23
            case inr h24 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- True on the right can always be proven directly.
              apply True.intro
          case inr h25 =>
            -- Disjunctions on the left can always be decomposed.
            cases h1
            case inl h26 =>
              -- False on the left can always be used.
              apply False.elim h26
            case inr h27 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- True on the right can always be proven directly.
              apply True.intro
    case inr h28 =>
      -- Conjunctions on the left can always be decomposed.
      let h29 := h28.left
      let h30 := h28.right
      -- False on the left can always be used.
      apply False.elim h30
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_33035482391670454609281883858 : ((p3 ∨ ((True ∧ ((p5 ∧ (p3 ∨ True)) ∧ p2)) → (((p4 → p1) ∧ (((((p3 ∨ p3) ∨ True) ∧ False) ∨ True) ∨ p1)) ∨ (p1 → p1)))) ∧ True) := by
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
    -- Implications on the right can always be decomposed.
    intro h9
    -- One of the premise coincides with the conclusion.
    exact h9
  case inr h10 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h11
    -- One of the premise coincides with the conclusion.
    exact h11
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158209795494733405460245970977 : ((((p4 ∧ p4) → p5) ∧ ((p3 ∨ (p1 ∧ ((p5 ∨ p3) ∨ ((p5 ∧ p2) ∨ p4)))) ∨ (p3 ∧ p3))) ∨ ((p2 → (p2 ∨ (False ∧ p5))) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40064185789462014513930899491 : ((((((p4 ∨ p4) ∧ (((True ∧ (False → ((False ∨ p1) → p2))) ∧ (p5 ∧ (p5 ∧ p5))) ∧ ((p5 ∧ p5) ∧ True))) ∨ p5) ∧ True) ∨ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137461409413518915445264502114 : ((p4 ∧ (p1 ∧ (p2 ∧ ((p1 ∧ p3) → ((((p4 ∨ p5) → (p3 → (False → (p1 → True)))) → (p3 ∨ p3)) → False))))) ∨ ((p5 ∧ p1) → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_809639707733758473445979550508 : (((p5 → ((True → ((p2 → ((p3 ∧ (p2 → True)) → (p2 ∨ (p1 ∨ (True ∨ (True ∧ ((p5 → p2) → (p4 ∨ False)))))))) ∧ p1)) → p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_327904263893095501021799724227 : (True → ((p5 → (((False ∨ (p5 ∧ ((((True ∧ False) ∧ True) → ((p1 ∧ (p2 → p1)) ∧ p5)) → p2))) → (False ∧ False)) ∧ False)) ∨ (False → p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_4273471419593962364746867891 : (True → (((False → (((p4 ∧ p5) ∧ ((p3 ∨ p5) ∨ False)) → (p1 ∧ False))) → ((((False ∨ False) ∨ (p3 → p5)) ∧ p1) ∧ p4)) → p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (False → (((p4 ∧ p5) ∧ ((p3 ∨ p5) ∨ False)) → (p1 ∧ False))) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h6.left
    let h9 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- False on the left can always be used.
        apply False.elim h4
      case inr h12 =>
        -- False on the left can always be used.
        apply False.elim h4
    case inr h13 =>
      -- False on the left can always be used.
      apply False.elim h13
    -- Conjunctions on the left can always be decomposed.
    let h14 := h5.left
    let h15 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h16 := h14.left
    let h17 := h14.right
    -- Disjunctions on the left can always be decomposed.
    cases h15
    case inl h18 =>
      -- Disjunctions on the left can always be decomposed.
      cases h18
      case inl h19 =>
        -- False on the left can always be used.
        apply False.elim h4
      case inr h20 =>
        -- False on the left can always be used.
        apply False.elim h4
    case inr h21 =>
      -- False on the left can always be used.
      apply False.elim h21
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h22 := h2 h3
  -- We need to get the right conjuct of h22 based on <expert-advice>.
  let h23 := h22.right
  -- One of the premise coincides with the conclusion.
  exact h23



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167221553719641490563568513003 : (((p4 ∨ ((((p5 → p2) ∨ (p1 → True)) → (False → ((False ∧ True) ∨ p2))) ∨ True)) ∨ True) → ((p1 ∧ p1) ∨ (p1 → (p4 → (p5 ∨ p4))))) := by
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
      -- Implications on the right can always be decomposed.
      intro h4
      -- Implications on the right can always be decomposed.
      intro h5
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
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
        -- Implications on the right can always be decomposed.
        intro h9
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h9
      case inr h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h11
        -- Implications on the right can always be decomposed.
        intro h12
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h12
  case inr h13 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h14
    -- Implications on the right can always be decomposed.
    intro h15
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_243009612322658366651424891553 : ((p4 → True) ∧ ((p4 ∧ p5) → ((((p3 ∨ ((p2 ∧ (False → (p5 ∧ (True ∨ False)))) ∧ False)) → p1) → (((p3 ∨ p1) ∧ True) ∧ True)) ∨ p4))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197618650075649986589094908849 : (((((p4 → p2) ∧ p5) ∧ p4) → (p1 → False)) ∨ (((p5 ∨ (p4 ∧ p1)) ∧ (p4 → (p1 → p5))) ∨ (((p2 → (p1 ∨ p4)) → p4) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160861316709356169339423208586 : (((p1 ∧ ((p5 ∨ p3) ∨ p1)) ∧ (((p3 ∨ (p3 ∧ False)) → p1) → (p2 ∧ ((False ∧ p1) ∨ True)))) → ((False ∨ (False ∨ False)) ∨ (p1 ∨ p3))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h8 =>
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
    exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_694141067423802306646113474209 : (((((False ∨ ((True → p4) ∧ (False ∧ p4))) ∧ (((False ∨ p1) → p5) ∧ p5)) ∨ ((p4 → (p4 → p3)) ∧ (p3 ∧ ((p1 ∧ p2) ∨ p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_254057104968042378077067195940 : ((p2 ∧ True) → (((False ∨ p1) ∧ p5) ∨ (((((p1 ∧ (True → p1)) ∧ p3) ∨ ((p4 → p4) ∨ True)) ∧ (p2 → (True → False))) → (p3 ∧ p1)))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h8.left
    let h11 := h8.right
    -- One of the premise coincides with the conclusion.
    exact h9
  case inr h12 =>
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h13 =>
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h14 : p2 := by
        -- One of the premise coincides with the conclusion.
        exact h2
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h15 := h6 h14
      -- We want to use the implication h15 based on <expert-advice>. So we show its premise.
      have h16 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h15, we can now drive its conclusion.
      let h17 := h15 h16
      -- False on the left can always be used.
      apply False.elim h17
    case inr h18 =>
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h19 : p2 := by
        -- One of the premise coincides with the conclusion.
        exact h2
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h20 := h6 h19
      -- We want to use the implication h20 based on <expert-advice>. So we show its premise.
      have h21 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h20, we can now drive its conclusion.
      let h22 := h20 h21
      -- False on the left can always be used.
      apply False.elim h22
  -- Conjunctions on the left can always be decomposed.
  let h23 := h4.left
  let h24 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h23
  case inl h25 =>
    -- Conjunctions on the left can always be decomposed.
    let h26 := h25.left
    let h27 := h25.right
    -- Conjunctions on the left can always be decomposed.
    let h28 := h26.left
    let h29 := h26.right
    -- One of the premise coincides with the conclusion.
    exact h28
  case inr h30 =>
    -- Disjunctions on the left can always be decomposed.
    cases h30
    case inl h31 =>
      -- We want to use the implication h24 based on <expert-advice>. So we show its premise.
      have h32 : p2 := by
        -- One of the premise coincides with the conclusion.
        exact h2
      -- We have shown the premise of h24, we can now drive its conclusion.
      let h33 := h24 h32
      -- We want to use the implication h33 based on <expert-advice>. So we show its premise.
      have h34 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h33, we can now drive its conclusion.
      let h35 := h33 h34
      -- False on the left can always be used.
      apply False.elim h35
    case inr h36 =>
      -- We want to use the implication h24 based on <expert-advice>. So we show its premise.
      have h37 : p2 := by
        -- One of the premise coincides with the conclusion.
        exact h2
      -- We have shown the premise of h24, we can now drive its conclusion.
      let h38 := h24 h37
      -- We want to use the implication h38 based on <expert-advice>. So we show its premise.
      have h39 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h38, we can now drive its conclusion.
      let h40 := h38 h39
      -- False on the left can always be used.
      apply False.elim h40



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_358017478793773369288744938113 : (p5 → (False ∨ (p1 ∨ (((((p1 ∧ (p1 ∧ ((p5 ∧ False) → ((p3 → False) ∨ False)))) ∨ p4) ∧ False) ∧ ((p5 → p3) ∧ p5)) ∨ (p1 → p5))))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_785662681143336098099865852481 : (((p4 ∨ ((((p5 ∨ (p1 ∧ (((p1 ∨ (p1 ∨ (p3 ∨ p4))) ∧ ((p4 ∧ True) → (p5 ∧ p4))) ∧ p5))) → p2) ∧ (p3 ∨ p1)) → p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147524126667990515122694706015 : (((True → ((p2 ∧ (((p4 → ((p5 → (False → p4)) → (p3 ∨ p5))) → (p3 → False)) → p4)) ∧ p2)) ∨ True) ∨ (((False ∧ p4) ∨ p5) → p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219473775405027606390317776211 : ((p4 ∨ (False → (False → p4))) → ((p4 → ((((p5 ∧ (p5 → (((p1 ∧ p3) → p2) → p4))) → p1) ∨ (True ∨ (True ∧ p2))) → False)) ∨ True)) := by
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
theorem thm_5_vars_690988013432305679844745969642 : ((((((p5 ∧ False) ∧ ((p4 → ((p5 → p2) ∨ (True → p1))) → p4)) → (True ∨ False)) → ((p1 ∧ (p5 ∨ (p1 ∨ True))) → (p1 → p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200235951449085531927065737927 : ((((False → p1) ∨ p1) → (p1 ∨ (False → p1))) → (p5 ∨ (((p4 → (p4 ∧ (((p2 ∨ p2) → ((True ∧ True) ∧ True)) → False))) ∨ p4) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43528481689933318209466025656 : ((((False → (((False → p4) → ((p2 ∧ False) ∨ p1)) → (p5 ∨ (((True ∨ (p4 ∨ (p3 ∨ p4))) → p1) → (p4 ∧ True))))) ∨ True) → p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_151080203606896186689553608372 : ((((True ∧ (((p1 ∨ p1) → p3) → ((True ∧ (p2 → ((p1 ∧ False) ∧ False))) → (p1 ∧ False)))) ∨ p5) → p5) → (p3 ∨ (p2 ∨ (p5 → p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47600420165020502796576912034 : (((p3 → ((p5 ∧ True) ∧ (((p2 ∧ p5) → (((((p3 ∨ True) → p4) → (p1 ∧ p3)) → p1) ∨ (True → p4))) ∨ p4))) ∨ (p3 ∨ True)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185803221223940631671181477593 : ((p5 → ((p5 ∧ p2) ∧ ((True → ((p4 ∨ p2) → True)) ∨ p4))) ∨ ((False ∧ (((((p4 ∨ p2) → p2) → (p5 → False)) → p5) → False)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171298158930558113551220701746 : (((((p1 ∧ (True → (p5 ∧ (p3 ∨ ((p1 ∨ p1) → p5))))) → False) ∧ True) ∧ p2) ∨ (True → ((((p2 ∧ False) ∨ p3) ∨ p3) ∨ (True → True)))) := by
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
theorem thm_5_vars_348158949626232036992207614106 : (p3 → ((True ∨ p3) → (((p4 ∨ (p1 → (False ∨ (p4 ∨ p3)))) ∧ (p5 → ((True ∨ (((True → p3) ∨ p5) → p3)) ∨ p2))) ∨ (p2 ∨ True)))) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258444676710302949572190679709 : ((p5 ∨ p1) → (p2 ∨ ((True ∧ p1) → (p3 ∨ ((((True ∧ p4) → (p2 → (p2 → p1))) → False) → (p4 ∧ (((p5 ∧ False) → p1) ∨ p3))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h7 : ((True ∧ p4) → (p2 → (p2 → p1))) := by
      -- Implications on the right can always be decomposed.
      intro h8
      -- Implications on the right can always be decomposed.
      intro h9
      -- Implications on the right can always be decomposed.
      intro h10
      -- Conjunctions on the left can always be decomposed.
      let h11 := h8.left
      let h12 := h8.right
      -- One of the premise coincides with the conclusion.
      exact h5
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h13 := h6 h7
    -- False on the left can always be used.
    apply False.elim h13
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h14
    -- Conjunctions on the left can always be decomposed.
    let h15 := h14.left
    let h16 := h14.right
    -- False on the left can always be used.
    apply False.elim h16
  case inr h17 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h18
    -- Conjunctions on the left can always be decomposed.
    let h19 := h18.left
    let h20 := h18.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h21
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- We want to use the implication h21 based on <expert-advice>. So we show its premise.
    have h22 : ((True ∧ p4) → (p2 → (p2 → p1))) := by
      -- Implications on the right can always be decomposed.
      intro h23
      -- Implications on the right can always be decomposed.
      intro h24
      -- Implications on the right can always be decomposed.
      intro h25
      -- Conjunctions on the left can always be decomposed.
      let h26 := h23.left
      let h27 := h23.right
      -- One of the premise coincides with the conclusion.
      exact h20
    -- We have shown the premise of h21, we can now drive its conclusion.
    let h28 := h21 h22
    -- False on the left can always be used.
    apply False.elim h28
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h29
    -- Conjunctions on the left can always be decomposed.
    let h30 := h29.left
    let h31 := h29.right
    -- False on the left can always be used.
    apply False.elim h31



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_311912357566181661985880720389 : (p2 ∨ (p2 ∨ (True → ((True ∧ ((((p2 ∨ (((False ∧ p3) → True) → (p4 ∧ p3))) ∨ p5) ∧ p5) ∨ ((p1 → True) ∧ (True ∧ True)))) ∨ True)))) := by
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
theorem thm_5_vars_40631246440160246950887199286 : ((((((False → (((False ∨ ((p3 ∧ p3) ∧ False)) → ((p2 ∨ (p3 ∧ (p3 ∨ (p1 → p2)))) → p1)) ∧ False)) → False) → p2) → p4) ∨ True) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_775421785808845017520408930780 : (((False ∨ (p2 ∧ ((p4 ∨ (p5 ∧ p5)) → (((p1 ∨ (p5 ∨ ((False → (p3 → ((p2 ∨ p3) → p5))) ∨ (p2 ∨ p3)))) ∧ p4) ∨ p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42706732275883373685993777268 : (((p5 ∨ (((p4 ∨ p1) ∨ False) ∨ (((p1 ∨ (p1 ∨ ((p5 ∧ p2) ∨ (False ∧ (False ∧ p1))))) ∧ False) ∧ (p1 ∨ (p3 → p4))))) ∨ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58604916809085892836968942656 : (((False → p1) ∧ ((p2 ∧ (p3 → (p4 ∨ (False → False)))) ∧ ((((p4 ∧ p4) ∧ True) ∧ p5) ∧ ((((True ∧ p2) ∨ p3) ∨ False) ∨ p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56586565436921581922718130303 : (((p1 → (p5 → (p2 → p2))) → ((p2 ∨ (False ∨ (p5 ∧ (p3 → p1)))) ∨ ((True ∧ False) → (p5 → ((True ∧ (True ∨ p2)) → p2))))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h2.left
    let h9 := h2.right
    -- False on the left can always be used.
    apply False.elim h9
  case inr h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h2.left
    let h12 := h2.right
    -- False on the left can always be used.
    apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_327840750958502454752241483797 : (True → ((((p5 ∨ (((p5 → (p2 ∨ (p4 ∨ False))) ∨ True) ∧ p1)) ∨ (p3 → True)) ∨ (p5 → ((p3 ∨ False) → (True ∨ p5)))) ∨ (False ∧ True))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_255609450325921949935621252868 : ((p5 ∧ p4) → ((True → (True → (False ∧ ((False → (False ∧ ((((False ∨ p5) ∧ (p4 → (True ∧ False))) ∨ (p3 ∨ p1)) → p4))) → p3)))) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_730513227880785630670727713354 : ((((p1 ∧ (p2 ∧ p5)) → ((((((p2 ∨ ((True → False) ∧ (True ∨ p5))) ∧ p5) ∧ ((p1 ∨ p2) ∨ p3)) → (p4 ∨ True)) ∨ p1) ∨ p3)) ∨ p2) ∧ True) := by
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
  let h4 := h3.left
  let h5 := h3.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179475095181005159933889547644 : ((True → ((((p2 → p2) ∨ p3) ∧ (False → ((p4 ∨ True) ∧ p1))) → p3)) ∨ (((((True ∧ True) ∨ p1) → False) → (True → (p1 → p2))) ∨ False)) := by
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
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h4 : ((True ∧ True) ∨ p1) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h4
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50317291907911448810359337734 : (((((True ∧ ((p3 ∧ p4) ∧ (p4 ∨ (False ∨ True)))) ∧ p2) ∧ ((p2 → (False → (p5 ∨ p1))) → p5)) ∨ ((True ∧ (True ∧ p1)) → p1)) ∨ p1) := by
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
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150309145537843534466092178968 : ((p4 → ((False ∨ False) ∧ ((p5 ∨ p2) ∨ ((((((True ∨ p2) ∧ p5) → p3) ∨ False) ∧ (p1 ∧ p4)) ∨ p1)))) ∨ ((p4 ∧ (False ∨ False)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227905522781328523010845138398 : ((p2 ∧ (p2 → p5)) ∨ ((((p5 ∨ p5) ∧ True) → (p4 ∨ ((p5 → p2) ∧ True))) ∨ (p3 → (False → ((p3 ∧ (True ∧ (False ∨ p4))) → False))))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- False on the left can always be used.
    apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174814531445111596526787498905 : (((p3 → p5) ∧ (((True ∨ p2) ∧ p4) ∧ (p5 ∧ (((p4 → p4) ∨ True) ∨ p1)))) → ((p2 ∧ p5) ∨ ((((p1 → p5) ∧ True) → p5) ∨ p5))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h5.left
    let h10 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h9
      case inr h13 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h9
    case inr h14 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h9
  case inr h15 =>
    -- Conjunctions on the left can always be decomposed.
    let h16 := h5.left
    let h17 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h17
    case inl h18 =>
      -- Disjunctions on the left can always be decomposed.
      cases h18
      case inl h19 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h16
      case inr h20 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h16
    case inr h21 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_139887175250091612546758078086 : (((((((p1 ∨ (p5 ∧ p4)) → (p5 ∨ (False ∨ ((p1 → p1) → False)))) ∨ True) ∨ (p2 ∨ p4)) → p2) ∧ (p1 → p3)) → ((p2 ∧ p2) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : ((((p1 ∨ (p5 ∧ p4)) → (p5 ∨ (False ∨ ((p1 → p1) → False)))) ∨ True) ∨ (p2 ∨ p4)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257855960000682472535555047340 : ((p4 ∨ True) → ((False ∨ ((((p4 ∨ (True ∧ (((p2 ∨ p1) ∧ p2) ∧ (p2 → p3)))) ∧ (p2 ∧ True)) → p3) → ((False ∧ p2) ∧ True))) ∨ True)) := by
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
theorem thm_5_vars_166562483264402390029875907848 : ((p5 ∨ (False ∨ ((False → p4) → ((p1 ∧ p5) ∧ (p5 → ((False → p1) → (False ∨ p4))))))) ∨ ((True ∨ (p1 ∨ True)) ∨ ((p4 ∨ p4) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_70974068353228981922935381677 : ((((p2 ∧ (((p5 → p3) ∧ (p5 ∨ False)) ∧ p5)) ∧ (((True → (((p2 → p4) ∧ (p2 → True)) ∨ False)) ∨ p5) → (p4 ∨ p4))) ∧ p4) → p3) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h8 := h7.left
  let h9 := h7.right
  -- Conjunctions on the left can always be decomposed.
  let h10 := h8.left
  let h11 := h8.right
  -- Disjunctions on the left can always be decomposed.
  cases h11
  case inl h12 =>
    -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
    have h13 : p5 := by
      -- One of the premise coincides with the conclusion.
      exact h9
    -- We have shown the premise of h10, we can now drive its conclusion.
    let h14 := h10 h13
    -- One of the premise coincides with the conclusion.
    exact h14
  case inr h15 =>
    -- False on the left can always be used.
    apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192230912883022198204619170279 : ((((p2 ∨ (p1 ∨ (False ∨ p3))) ∧ (p5 → p4)) ∧ p4) → (p5 ∨ ((p1 ∨ ((p1 ∧ (True ∨ ((True ∨ False) ∨ True))) ∨ p1)) ∨ (True ∨ p1)))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- False on the left can always be used.
        apply False.elim h10
      case inr h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300066435153403075234691187051 : (False ∨ ((((p2 ∨ (p1 → ((p5 ∧ p5) ∨ p3))) ∨ (True ∧ (((p4 → (p1 ∧ True)) ∧ ((p1 → p5) ∧ p2)) → p2))) ∨ p4) ∨ (p1 ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61585258378750737389938969979 : ((p1 ∧ ((p3 → ((True → p4) → p5)) → ((True → ((True ∨ (p3 ∨ ((p5 ∧ p2) → True))) ∧ (p3 ∨ (True ∧ (p4 → p5))))) → p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43543775813727681081243537863 : ((((p4 → ((p4 → False) → (((p2 → ((((p4 → (p2 ∨ p3)) ∧ p2) → ((p5 ∧ False) ∧ False)) ∨ p4)) ∨ p4) ∨ p2))) ∨ p3) → p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1502855101371959535040367551 : (((((((p1 → ((p1 → p4) ∧ p3)) → ((p4 → p2) ∨ False)) → p4) → p5) ∨ p2) ∧ ((False → True) → (p5 → True))) ∨ (False → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_705923173522469006381743859435 : (((((True → (True → True)) ∨ (p2 → (p2 ∧ p4))) ∧ ((False ∨ p4) ∧ ((p3 ∧ p1) ∧ ((p2 ∧ (True ∧ (False ∨ (p2 ∧ False)))) ∨ p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_344710905531130528616024256216 : (p2 → (p3 → (((p4 ∨ (p5 ∨ (True → ((((((p5 → p4) ∨ ((p3 ∨ p5) ∨ False)) ∧ False) ∨ (p2 ∨ True)) → p4) ∨ False)))) ∨ p3) ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_628446715654956904638489303005 : (((((p3 ∧ ((p5 ∧ (p4 ∨ ((p4 ∨ ((p2 → False) ∧ (False ∧ p5))) → (p5 → (p5 ∧ p3))))) ∧ (p3 → (p5 ∨ False)))) ∧ p4) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227117386276343096730797658432 : (((p4 ∨ p2) → p4) ∨ (((((p5 → True) → (True ∨ (True → p3))) → ((p5 → p2) ∨ p1)) ∨ (p3 ∨ (True ∨ False))) ∨ ((p2 ∧ p3) ∨ p3))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_790886439043522431375825448088 : (((p5 ∨ (p3 → (((p2 ∧ ((p5 ∧ True) → (p4 → p1))) → p1) ∨ ((p1 → p4) ∨ (p3 ∨ ((p4 → p1) → ((False → p2) ∧ p1))))))) ∨ p1) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208917444397991818679005736472 : ((p5 ∧ ((p2 ∧ p2) ∨ (p5 → False))) → ((((p1 → True) → (False ∧ p1)) → p4) ∧ (False ∨ (((((p1 ∨ p2) ∧ p2) ∨ p1) ∨ p2) ∧ p5)))) := by
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
  cases h4
  case inl h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h8 : (p1 → True) := by
      -- Implications on the right can always be decomposed.
      intro h9
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h10 := h2 h8
    -- We need to get the left conjuct of h10 based on <expert-advice>.
    let h11 := h10.left
    -- False on the left can always be used.
    apply False.elim h11
  case inr h12 =>
    -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
    have h13 : p5 := by
      -- One of the premise coincides with the conclusion.
      exact h3
    -- We have shown the premise of h12, we can now drive its conclusion.
    let h14 := h12 h13
    -- False on the left can always be used.
    apply False.elim h14
  -- Conjunctions on the left can always be decomposed.
  let h15 := h1.left
  let h16 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h16
  case inl h17 =>
    -- Conjunctions on the left can always be decomposed.
    let h18 := h17.left
    let h19 := h17.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h19
    -- One of the premise coincides with the conclusion.
    exact h15
  case inr h20 =>
    -- We want to use the implication h20 based on <expert-advice>. So we show its premise.
    have h21 : p5 := by
      -- One of the premise coincides with the conclusion.
      exact h15
    -- We have shown the premise of h20, we can now drive its conclusion.
    let h22 := h20 h21
    -- False on the left can always be used.
    apply False.elim h22



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166259470544069720771101898939 : ((p3 ∧ ((p1 → (True ∧ (p5 ∧ (False ∨ p3)))) ∧ (((p3 ∨ p5) ∨ p1) ∧ (p5 → p2)))) ∨ ((False ∨ (p5 ∧ (True ∧ p2))) → (p1 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147320461917595539089641083219 : ((((p3 → (p1 → ((p2 → (False → (p5 ∧ False))) → (p1 ∨ (((p1 ∨ p2) → p3) ∧ True))))) → p2) ∨ p3) ∨ (((False ∧ True) ∨ True) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165118527590283543504954906955 : (((p4 → (p2 ∨ ((p1 → ((((p3 ∨ p4) ∨ p1) ∨ p2) ∨ p2)) ∨ (p5 → True)))) → p2) ∨ (False → (p3 ∨ (p3 ∨ ((p5 ∨ p2) ∨ p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68110403669677605535097471877 : ((p2 → (p2 → ((p1 ∨ (((((True ∨ p4) → (((False ∧ (False ∧ p5)) ∨ (p1 → True)) ∧ p5)) ∧ p1) ∧ p3) ∨ (p4 ∧ p4))) ∨ True))) ∨ False) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40943154793118370540764563785 : ((((((p3 ∨ (((p5 ∨ p5) → (p2 → (p1 ∧ False))) ∨ (p3 ∧ p3))) ∨ ((True ∨ (True ∨ p3)) ∨ p5)) → p4) ∨ (True ∧ p4)) ∨ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115494855915781528316373811981 : ((((p2 ∧ (p4 → (p2 ∧ (p4 ∨ True)))) ∨ p3) → (((True → True) → p4) ∨ (((True ∨ p1) ∨ p1) → (False → (p5 → p2))))) ∨ (p5 ∧ True)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Implications on the right can always be decomposed.
    intro h6
    -- Implications on the right can always be decomposed.
    intro h7
    -- False on the left can always be used.
    apply False.elim h6
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- Implications on the right can always be decomposed.
    intro h10
    -- Implications on the right can always be decomposed.
    intro h11
    -- False on the left can always be used.
    apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_678867846918673339438067681565 : ((((p1 ∧ (False ∨ ((p4 ∧ p3) → (p1 → ((p3 ∧ (p5 → (((p4 ∧ p1) → False) → p2))) ∨ p5))))) ∨ (False ∧ ((True → p2) → p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_670045204660138780528842138233 : (((((p4 ∧ (((p1 ∨ p2) → False) ∨ (p5 ∨ p3))) ∨ (((p5 ∧ p1) → (((p4 ∨ p3) → False) ∨ p5)) ∨ p3)) ∨ (p4 → (False ∨ False))) ∨ p3) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_801312964047747879590528235584 : (((p2 → ((p3 → ((p3 ∨ (((True → ((p5 → p2) ∧ p2)) → False) → True)) → p5)) ∨ (p4 ∨ ((((p5 ∨ False) ∧ False) ∧ p4) ∨ True)))) ∨ p1) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_693569668763454735853169445415 : (((((p3 ∧ ((p4 ∨ ((p3 ∨ (p3 ∨ (p5 ∨ True))) ∧ p3)) ∧ True)) ∧ True) ∨ ((((p3 ∧ p2) ∧ False) → (p4 ∧ (False ∧ p5))) ∧ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47166640201768275361060681462 : ((((p2 ∧ ((p3 → (p1 → p2)) ∧ (p2 ∨ (False ∨ (p4 ∨ (p4 ∨ p4)))))) ∧ (((p1 ∧ (p2 ∨ p2)) ∨ True) → p3)) ∨ (False → p4)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147066578986577830837900713934 : ((((((p3 → p1) ∧ ((False ∧ p4) ∨ p2)) ∨ p4) → (((p3 → False) ∧ p2) ∧ ((p4 ∨ p4) ∧ p2))) ∧ p1) ∨ ((p3 → False) → (p3 → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : p3 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_357897676712221433794046161830 : (p5 → (p5 ∧ (p3 ∨ (((((False → (False ∧ (p5 ∧ False))) ∧ p1) ∨ (((p2 ∨ p2) ∧ False) ∧ False)) ∨ (True ∧ p5)) ∨ ((p2 ∨ p4) ∧ p1))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_710229787795653646141177798332 : ((((((p4 → p5) → (p1 ∧ p2)) ∨ True) ∧ ((((p3 → p3) → (p4 ∨ (p4 → False))) → (p2 ∧ False)) ∨ (True ∧ (p2 → (False → p4))))) ∨ p5) ∧ True) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208789669787847032532603074763 : ((p2 ∧ (True ∨ (True ∧ (p4 ∨ p4)))) → (((((((p5 ∨ p1) ∨ False) ∧ True) ∧ ((p2 ∧ p4) → ((p5 ∨ False) → p2))) ∨ p2) ∨ p2) ∧ True)) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345629355651029988560028853238 : (p3 → ((False ∧ (True → ((p3 → (((p2 ∨ p1) ∨ ((((True ∧ p3) → p1) ∧ (p5 → p4)) ∧ p2)) ∧ (p1 ∧ p2))) ∨ (p5 ∨ True)))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111897036417676074020715045484 : ((((p5 ∧ ((p2 → (((p4 ∧ p3) ∨ p4) ∨ p5)) → ((p2 → False) ∨ p5))) ∨ (p3 ∧ ((False ∨ (False ∧ True)) ∨ p5))) ∨ False) ∨ (p4 → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259433050367030023932593025279 : ((False → p4) → (((((True ∨ False) ∧ ((p5 ∧ p2) ∧ (True → p5))) ∨ p1) ∨ ((False → ((((True → p2) → True) ∨ p1) → p1)) ∨ p1)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115230260966929233879395054697 : (((((((p4 ∧ p4) → True) → (p4 ∧ p4)) ∨ False) ∨ p4) ∨ ((True ∨ ((p2 ∨ (p5 ∧ (p5 ∧ True))) ∧ (False ∨ p3))) → True)) ∨ (p3 ∧ p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52042199721051540488630384618 : (((True → (p1 ∧ ((p3 ∧ ((p2 → p5) ∨ p2)) → (((p3 ∨ p5) ∨ p1) → p5)))) ∨ ((p1 ∨ p1) → ((p5 ∨ (p4 → p3)) → True))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337319574917708696863223441439 : (p1 → ((p1 ∧ ((p2 ∨ ((True ∧ ((p4 ∧ p3) ∧ (p5 ∧ p5))) ∧ (p4 ∨ p2))) ∨ ((p4 ∨ p2) → (False ∨ p1)))) ∧ ((p4 ∨ p4) → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  -- Implications on the right can always be decomposed.
  intro h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58304087545807233519132575062 : (((True ∨ p4) ∧ (((((p5 ∨ p4) ∧ (p4 ∨ False)) ∧ (((p3 ∧ True) → p2) ∧ p4)) → (False ∨ (p1 ∨ (p3 → (p3 → p1))))) ∧ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206050541700657813563779022935 : ((p2 ∧ (p1 → (p1 ∧ (False → True)))) ∨ (((((False ∨ p5) ∨ p5) ∨ (p3 → p1)) → (((p5 ∨ p1) → (p4 ∨ p3)) ∨ p1)) ∨ (True ∧ True))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230785345208281091724970446161 : (((True ∧ p4) ∨ True) → ((p3 ∧ (p4 → ((p2 ∨ (p4 ∨ p4)) → (False ∨ (p2 ∨ True))))) ∨ (p2 → ((True ∧ p3) ∨ (p2 → (p1 → True)))))) := by
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
    -- Implications on the right can always be decomposed.
    intro h6
    -- Implications on the right can always be decomposed.
    intro h7
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h10
    -- Implications on the right can always be decomposed.
    intro h11
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49094015372952176068574751366 : (((((p4 ∨ (((True ∨ False) → True) ∧ ((p5 ∧ p2) → (True ∨ False)))) → (p3 ∨ p1)) ∨ ((p1 ∨ p3) ∧ p1)) ∨ (False ∨ (False → p1))) ∨ p5) := by
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
theorem thm_5_vars_60251417616115355988992535531 : (((False → False) → (((p4 → False) → ((p2 ∧ True) ∧ (True → (p3 ∧ (((p5 ∨ (p3 ∨ p5)) ∨ (p5 → False)) → p5))))) → (p1 ∨ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_619882199493934941519522778834 : (((((p5 ∨ p1) ∧ (((p3 ∨ ((p1 ∧ ((p5 ∨ p4) → p5)) ∧ True)) → (False ∧ ((p5 ∨ p2) ∧ p2))) ∧ ((True → p1) ∧ p1))) ∨ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_724375281356842575472360036514 : ((((p5 ∧ (p5 ∨ True)) ∧ (p3 ∨ ((((p4 → (False ∨ (p3 → p4))) ∧ p5) → ((p4 ∨ ((p5 ∨ (True ∧ True)) ∧ p3)) ∧ p3)) → p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_139725620670197762542259995402 : ((((p2 → p5) → (False ∧ (True ∧ ((p5 → ((True → (p4 ∧ ((True ∨ p2) → (p5 → True)))) → True)) → False)))) → p4) → ((True → False) → p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66230109457421450994518163959 : ((p5 ∨ ((True ∧ (p4 ∨ ((p2 ∨ (p1 ∨ p5)) ∧ p3))) ∧ (p3 ∨ (p5 ∨ (p5 ∨ (((False → p3) ∧ (p3 ∧ (p1 → p2))) ∧ p5)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52323141388125255547665390156 : (((((p1 ∨ p2) ∧ (p2 ∧ (((True ∧ (p4 ∧ True)) ∧ p2) ∨ p2))) ∨ p3) ∧ (p1 ∨ ((p5 ∨ ((p1 ∨ p2) ∨ (p3 → p2))) → p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342409709862397092837972654128 : (p2 → ((((((p3 ∨ p2) → p2) ∨ ((False → (p4 → True)) → p3)) ∨ (False → p4)) ∧ p4) → ((p3 ∨ (p1 ∨ True)) ∧ (p2 ∨ (p4 → True))))) := by
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
  cases h3
  case inl h5 =>
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
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h9 := h2.left
  let h10 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h9
  case inl h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h13 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h1
  case inr h14 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_727189871893826898379664831178 : ((((False ∧ (p1 ∧ False)) ∨ (p4 ∧ ((p1 ∧ ((p2 ∧ ((p1 → True) ∨ (((p2 → (p5 ∧ (p1 ∨ p2))) → p4) → p2))) ∧ False)) ∨ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231296135830818800390517435490 : (((p5 ∨ p3) ∨ p5) → ((((False → p4) ∧ (p2 ∧ ((p4 ∧ ((p3 ∧ True) → (True → (p4 ∨ False)))) ∨ False))) ∨ (p5 → p5)) → (p4 ∨ True))) := by
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
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h11 =>
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
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h15 =>
      -- False on the left can always be used.
      apply False.elim h15
  case inr h16 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_196751324631645770536782171866 : (((((p4 ∧ True) ∧ p2) ∨ (False ∨ p3)) ∧ p3) ∨ (((((((True ∧ ((False ∨ p1) ∨ p4)) ∨ False) ∧ True) ∧ False) ∨ p3) ∨ False) ∨ (True ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231002437228606387736676250925 : (((p5 ∧ False) ∨ p3) → (True ∧ (((p4 ∧ True) ∧ (False → True)) ∨ ((((False ∨ (p3 ∨ True)) ∧ ((p4 ∨ p5) ∨ p2)) ∨ True) ∧ (True ∨ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
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
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_612308613688924701135313639486 : (((((p1 ∧ (True ∧ (((True ∨ p2) → False) ∧ ((p1 ∨ p4) → (p2 ∨ (((p4 ∧ (True ∧ p2)) → True) ∧ False)))))) ∧ (p2 ∨ True)) ∨ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_196758709490938954593973547123 : ((((p4 ∧ (p4 ∨ False)) ∨ (p5 → p3)) ∧ p1) ∨ ((p4 ∨ ((True ∨ p5) ∧ ((((p5 ∨ (p5 → p5)) ∧ p1) → p1) ∨ p1))) ∧ (p5 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309410190529916277102785771637 : (p2 ∨ ((p3 → (False ∨ (True → (p5 → (p4 ∧ (((True ∨ p3) ∨ p2) ∨ (False ∧ ((False → (p5 ∨ (p4 ∨ p5))) → p1)))))))) ∨ (p3 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_142582564874642340956394182491 : ((False ∨ ((((((((p5 ∨ p1) ∨ p4) → p5) → True) ∨ (((p5 → (p4 → False)) → p5) ∨ p2)) ∧ p5) ∨ True) → p5)) → ((p4 ∨ p5) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- False on the left can always be used.
    apply False.elim h2
  case inr h3 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h4 : (((((((p5 ∨ p1) ∨ p4) → p5) → True) ∨ (((p5 → (p4 → False)) → p5) ∨ p2)) ∧ p5) ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h5 := h3 h4
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5



