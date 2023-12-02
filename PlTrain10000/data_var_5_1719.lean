variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134090404046428800442669362368 : (((((p5 ∧ p4) → ((((p3 ∨ p3) ∨ (True → (p5 ∧ (p5 ∧ p1)))) → (True → p1)) ∧ (p2 ∧ False))) → p2) ∨ True) ∨ ((p4 ∧ p4) → True)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_252421363660275462925085692368 : ((p5 → False) ∨ ((False ∨ p5) ∨ ((((((p1 ∧ p5) ∧ (False ∧ (p1 → True))) ∧ ((p1 ∧ p4) ∨ (p4 ∨ p2))) → (False ∧ p2)) → False) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_680736331528309819449553657518 : (((((p5 ∨ ((p1 ∨ False) ∨ p4)) ∨ ((False → (p2 ∨ False)) ∨ (p3 ∧ (((p4 → p3) ∨ p2) ∨ True)))) → (((p2 → False) → p4) ∨ True)) ∨ p2) ∧ True) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h5 =>
        -- Disjunctions on the left can always be decomposed.
        cases h5
        case inl h6 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h7 =>
          -- False on the left can always be used.
          apply False.elim h7
      case inr h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h14 =>
        -- Disjunctions on the left can always be decomposed.
        cases h14
        case inl h15 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h16 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h17 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_656873791457955552533711432186 : (((((p5 ∨ (p2 → (p1 → p3))) ∧ (p5 ∨ (p5 ∨ ((p1 ∧ (p1 ∨ p1)) ∧ ((p1 ∨ (p1 → (p3 → True))) ∧ p2))))) ∨ (p4 ∧ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215293200307037055849301501216 : ((p1 ∧ ((p4 → p3) ∧ True)) ∨ ((p3 ∨ True) ∧ (((((True → p5) ∧ p2) ∨ ((True → False) ∨ ((p5 ∧ (p4 → False)) ∧ p2))) ∨ p3) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_44223785884829621151550263732 : ((((((((p3 ∨ (((p1 ∨ False) ∧ True) ∧ (True ∧ (p2 ∨ p2)))) → p2) ∨ p4) ∨ p5) → True) ∨ ((True ∧ p3) ∨ (p4 ∨ p2))) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310246519349029160057021336007 : (p2 ∨ (((p4 → p1) ∧ (((True → (False ∧ True)) ∨ p2) ∨ (p5 ∨ p1))) → (p1 → (((p5 ∧ p2) ∨ (p3 → (p4 → (p3 ∨ p1)))) ∨ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h7 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h8 := h6 h7
      -- We need to get the left conjuct of h8 based on <expert-advice>.
      let h9 := h8.left
      -- False on the left can always be used.
      apply False.elim h9
    case inr h10 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h11
      -- Implications on the right can always be decomposed.
      intro h12
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h11
  case inr h13 =>
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h14 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h15
      -- Implications on the right can always be decomposed.
      intro h16
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h15
    case inr h17 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h18
      -- Implications on the right can always be decomposed.
      intro h19
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_139103260808131262742649249579 : (((((((False → p3) ∧ (((True → p5) ∨ p3) ∧ p1)) ∧ (p2 ∨ p1)) → (p1 ∧ p1)) ∧ ((p5 ∧ p2) → p2)) ∨ p2) → ((p5 ∨ True) ∨ p4)) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149805832483128870875679584644 : ((False ∨ (p3 ∨ (((((p5 ∧ p3) ∨ p4) ∨ (p2 ∨ True)) ∨ (p5 ∧ (True ∨ p3))) → ((p5 ∧ p4) → p3)))) ∨ (False ∨ (p2 → (p1 ∨ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258065267367246606324399708446 : ((p4 ∨ p2) → (((False ∨ p5) ∧ True) ∨ ((p3 ∨ p1) ∨ (True ∨ (p1 ∧ ((p5 ∧ ((p3 → True) ∧ (True → (p1 → (p4 ∧ p1))))) ∨ p2)))))) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259201726932882926164694344640 : ((False → False) → ((p5 → (p2 ∨ ((((p3 ∨ True) → p3) ∧ (p1 ∨ p2)) ∨ (False → ((False ∨ (p4 → p4)) ∨ (True ∧ p3)))))) ∨ (p5 ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259328410170725118592811717120 : ((False → p2) → ((((p4 ∨ (p1 ∧ p2)) ∧ False) ∧ ((((p2 ∧ (True → (True ∨ p4))) ∧ p4) ∧ p1) ∧ False)) ∨ (True ∨ ((p1 → True) ∨ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200046694852607324923450379798 : (((p2 ∨ (p3 ∨ (p1 → False))) → (p3 ∨ p2)) → ((p2 ∧ p2) ∨ ((p2 ∧ p1) ∨ ((p3 ∧ p2) → (p5 → ((True ∧ (p4 ∨ p3)) ∨ p2)))))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147695721981120169322852776905 : (((((p3 → ((p1 ∨ ((True ∨ (True ∨ p3)) → p3)) → False)) ∧ p2) ∨ (p4 → (p1 ∧ (True → True)))) → False) ∨ (p3 → (p1 ∨ (True ∨ p3)))) := by
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
theorem thm_5_vars_183885357831046480432454635508 : (((((p1 ∧ p2) → p1) → ((p2 ∧ p1) → (p5 ∧ p4))) ∧ p1) ∨ ((False ∨ (True ∨ ((False → p2) ∨ (True ∧ (p5 ∨ p3))))) → (p2 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- False on the left can always be used.
    apply False.elim h2
  case inr h3 =>
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
        -- Conjunctions on the left can always be decomposed.
        let h8 := h7.left
        let h9 := h7.right
        -- Disjunctions on the left can always be decomposed.
        cases h9
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
theorem thm_5_vars_178349414563089746784282270886 : (((p3 ∧ (p4 ∧ ((((True ∧ p5) ∨ True) ∧ True) ∧ p3))) ∨ (True ∧ p5)) ∨ ((False ∨ ((False → True) → ((p1 ∧ p5) ∧ (p2 → False)))) → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- False on the left can always be used.
    apply False.elim h2
  case inr h3 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h4 : (False → True) := by
      -- Implications on the right can always be decomposed.
      intro h5
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h6 := h3 h4
    -- We need to get the left conjuct of h6 based on <expert-advice>.
    let h7 := h6.left
    -- We need to get the right conjuct of h7 based on <expert-advice>.
    let h8 := h7.right
    -- One of the premise coincides with the conclusion.
    exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_255482971756800768714846882833 : ((p5 ∧ p2) → ((((p5 → (((True ∨ (p2 ∨ ((p4 ∨ p5) → p1))) ∨ ((False ∨ ((p4 ∨ p3) ∧ p3)) ∨ False)) ∨ p2)) → p4) ∧ p4) ∨ True)) := by
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
theorem thm_5_vars_597298320091562741311269867586 : (((((p5 ∧ (True → (p1 ∨ p5))) ∧ (p2 ∧ ((p2 ∧ p4) → (((((p2 ∧ (p2 → p5)) → p4) ∨ (False → p3)) ∨ True) → p3)))) ∧ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113386010767956376016920812396 : (((True → ((((((False → True) → True) ∨ ((p3 ∧ False) → p2)) ∨ p4) ∨ (True → ((p5 ∧ p5) ∧ p3))) → False)) ∧ (True ∧ p1)) ∨ (False ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64462794634219719713732381520 : ((p1 ∨ ((True → (((False ∧ True) ∧ p2) ∨ ((p5 ∧ (((False → p2) ∨ (p4 ∨ p4)) ∧ (p2 ∨ p5))) → False))) ∧ (p1 ∨ (p3 ∨ True)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225384912346819964086926052363 : (((p2 ∨ p2) ∧ p3) ∨ ((p4 → False) ∨ (p4 ∨ ((p3 ∨ ((p2 → (p3 → p2)) ∧ (True → (p1 ∧ ((p5 ∨ p5) ∧ True))))) → (False → True))))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_82289647730513553450095285117 : ((((p4 ∧ ((p3 ∨ (p5 → (((p5 ∧ (p4 ∨ p3)) → ((p4 → p4) ∧ p3)) ∨ p3))) ∨ p4)) → False) ∧ ((True ∧ p4) ∨ (p1 ∧ p4))) → p2) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h7 : (p4 ∧ ((p3 ∨ (p5 → (((p5 ∧ (p4 ∨ p3)) → ((p4 → p4) ∧ p3)) ∨ p3))) ∨ p4)) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h6
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h6
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h8 := h2 h7
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h12 : (p4 ∧ ((p3 ∨ (p5 → (((p5 ∧ (p4 ∨ p3)) → ((p4 → p4) ∧ p3)) ∨ p3))) ∨ p4)) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h11
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h11
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h13 := h2 h12
    -- False on the left can always be used.
    apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_33717124400861884882135356078 : ((p5 ∨ ((False ∨ ((((p2 ∧ ((((p4 → (p5 → (p5 ∨ p4))) → p5) ∨ (p3 ∧ True)) ∨ p2)) ∨ p2) ∨ True) ∨ (p3 ∨ p2))) ∨ p5)) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54551276094030408004675320034 : (((p1 ∧ ((True ∧ (p5 ∨ False)) ∨ (p5 ∧ True))) ∨ ((((True ∨ ((False → p3) ∧ p3)) → (p3 → True)) ∨ p2) → ((p3 ∧ p4) ∨ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158596975053140667128725342931 : ((False ∧ (((p3 ∧ p1) ∧ (((((p5 ∨ False) → (False ∨ True)) ∧ (p5 ∨ p2)) → p3) ∨ p2)) ∨ True)) ∨ (False → ((True → p5) ∨ (p5 ∧ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58689137050316699602692220877 : (((p2 → p2) ∧ (((((p3 ∧ p4) ∧ (True ∧ p1)) ∧ p2) ∧ False) ∨ (p2 → (False ∨ ((p2 → (False → p1)) ∨ (p5 ∨ (p3 → p5))))))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231591105812867686038845843316 : (((True ∧ False) → p1) → (((p1 → (False ∨ (p4 → p4))) ∨ p5) ∧ ((False ∧ (((p5 ∧ p1) ∧ p3) ∨ p1)) ∨ (p5 → (False ∨ (True ∨ p3)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234948055442216204312883919254 : ((True ∧ True) ∧ (p2 → (p3 ∨ ((p1 ∨ (((True ∧ (False ∧ (p2 → False))) ∨ p5) ∧ (p4 → p3))) ∨ (p4 ∨ (False → ((p4 ∨ False) ∧ False))))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_702445180149973025088552698588 : (((((p5 ∧ ((p1 ∨ ((False ∧ p1) ∨ True)) ∨ p4)) ∨ p4) ∨ ((False → (p5 → (((p5 → p4) ∨ (p3 → p3)) ∨ p1))) → (True → p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51128685339758597558732130113 : ((((p2 ∧ (((((((p3 ∨ p4) → p5) → p3) ∨ p5) ∨ p5) → p4) ∨ (p4 ∨ p4))) ∨ p4) ∨ ((p1 ∧ p4) ∨ (p4 ∨ (False ∧ True)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_348141815331537957074036392325 : (p3 → ((p3 ∧ p2) → (p5 → ((p3 → ((((p1 → False) ∨ (p5 ∧ (((True ∧ p1) ∧ p1) → p4))) ∧ (False → p1)) ∧ (p3 → p1))) → p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h2.left
  let h6 := h2.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h7 : p3 := by
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h8 := h4 h7
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
  have h10 : p3 := by
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h9, we can now drive its conclusion.
  let h11 := h9 h10
  -- One of the premise coincides with the conclusion.
  exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114733019892185949807650462043 : (((((True → (False → p5)) ∧ (p1 ∨ p2)) → (((True ∨ p3) ∨ p3) ∨ (p1 → p5))) → ((p2 ∧ (False ∨ (p3 ∨ p5))) ∧ p1)) ∨ (True → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157362488962395377651769192372 : (((p2 → (((((p3 ∧ p4) ∧ p2) ∧ False) ∨ (((False ∨ p1) ∨ p1) ∧ (True ∨ p4))) ∨ p2)) → False) ∨ ((p1 → True) ∨ (p4 ∧ (p2 → True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118158265707923149825313634623 : ((False ∨ ((p3 → ((p5 ∨ True) ∧ p5)) → ((((p5 → p5) ∨ ((p2 ∧ False) ∧ ((p4 ∧ (p4 ∨ True)) → p2))) ∨ p4) → p2))) ∨ (False → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_123506839687083702185912079485 : ((((((p3 ∧ True) ∨ p1) → (False ∧ False)) ∧ ((False ∨ (False → True)) → (p1 → p1))) ∧ ((False ∨ p3) ∧ (p1 ∨ (p4 ∨ p2)))) → (p4 ∧ p1)) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h3.left
  let h7 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h8 =>
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h10 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h11 : ((p3 ∧ True) ∨ p1) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h10
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h12 := h4 h11
      -- We need to get the left conjuct of h12 based on <expert-advice>.
      let h13 := h12.left
      -- False on the left can always be used.
      apply False.elim h13
    case inr h14 =>
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h15 =>
        -- One of the premise coincides with the conclusion.
        exact h15
      case inr h16 =>
        -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
        have h17 : ((p3 ∧ True) ∨ p1) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- One of the premise coincides with the conclusion.
          exact h9
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h4, we can now drive its conclusion.
        let h18 := h4 h17
        -- We need to get the left conjuct of h18 based on <expert-advice>.
        let h19 := h18.left
        -- False on the left can always be used.
        apply False.elim h19
  -- Conjunctions on the left can always be decomposed.
  let h20 := h1.left
  let h21 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h22 := h20.left
  let h23 := h20.right
  -- Conjunctions on the left can always be decomposed.
  let h24 := h21.left
  let h25 := h21.right
  -- Disjunctions on the left can always be decomposed.
  cases h24
  case inl h26 =>
    -- False on the left can always be used.
    apply False.elim h26
  case inr h27 =>
    -- Disjunctions on the left can always be decomposed.
    cases h25
    case inl h28 =>
      -- One of the premise coincides with the conclusion.
      exact h28
    case inr h29 =>
      -- Disjunctions on the left can always be decomposed.
      cases h29
      case inl h30 =>
        -- We want to use the implication h22 based on <expert-advice>. So we show its premise.
        have h31 : ((p3 ∧ True) ∨ p1) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- One of the premise coincides with the conclusion.
          exact h27
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h22, we can now drive its conclusion.
        let h32 := h22 h31
        -- We need to get the left conjuct of h32 based on <expert-advice>.
        let h33 := h32.left
        -- False on the left can always be used.
        apply False.elim h33
      case inr h34 =>
        -- We want to use the implication h22 based on <expert-advice>. So we show its premise.
        have h35 : ((p3 ∧ True) ∨ p1) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- One of the premise coincides with the conclusion.
          exact h27
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h22, we can now drive its conclusion.
        let h36 := h22 h35
        -- We need to get the left conjuct of h36 based on <expert-advice>.
        let h37 := h36.left
        -- False on the left can always be used.
        apply False.elim h37



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_707640552377358175245949856766 : (((((False ∧ p5) ∨ ((p4 → (p1 ∧ True)) ∨ p1)) ∨ ((p5 → p3) → ((True ∧ (p4 ∨ (p5 → (p4 ∨ p2)))) ∨ (True ∨ (p1 → p5))))) ∨ p3) ∧ True) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160605459774459667989426372984 : (((p1 ∧ (True ∧ (True ∧ (p5 ∨ ((p1 → p1) → p4))))) ∧ (p5 ∨ ((p4 ∨ (True → p3)) ∨ False))) → ((True ∧ ((True ∧ p4) → False)) ∨ p1)) := by
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
  let h8 := h7.left
  let h9 := h7.right
  -- Disjunctions on the left can always be decomposed.
  cases h9
  case inl h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h12 =>
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- Disjunctions on the left can always be decomposed.
        cases h13
        case inl h14 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h4
        case inr h15 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h4
      case inr h16 =>
        -- False on the left can always be used.
        apply False.elim h16
  case inr h17 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h18 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h19 =>
      -- Disjunctions on the left can always be decomposed.
      cases h19
      case inl h20 =>
        -- Disjunctions on the left can always be decomposed.
        cases h20
        case inl h21 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h4
        case inr h22 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h4
      case inr h23 =>
        -- False on the left can always be used.
        apply False.elim h23



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_679393705761527029613035511669 : ((((p4 → (True ∧ (((((p5 ∨ (p3 ∧ p2)) ∧ ((False ∧ (False ∧ p2)) ∨ p1)) → p2) ∧ p5) → False))) ∨ (((False ∨ p5) → p1) → True)) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_148777235297288978990958715178 : ((((p5 ∧ (False → p4)) ∨ (True ∧ p5)) ∨ (((p4 → p3) ∧ (p4 → (p1 ∧ (p5 ∨ (p2 ∨ p3))))) ∧ p1)) ∨ (p2 ∨ (p2 → (p1 → True)))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_18259288162478314112465531913 : ((((False ∨ ((p5 → p2) → ((p2 ∧ p3) ∧ ((p5 → p2) ∧ (p1 ∧ True))))) ∧ ((p2 ∧ p4) ∨ False)) → (p1 ∨ (p1 → (p1 ∨ p4)))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h9
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h10 =>
      -- False on the left can always be used.
      apply False.elim h10
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_153463194048523656344213392968 : ((p4 ∨ (p1 ∨ ((True ∧ (p3 ∧ (p5 ∧ (False ∨ (p1 ∨ p3))))) ∧ (((True ∨ (p1 ∧ False)) ∧ False) ∧ p2)))) → ((p1 ∧ (p5 ∨ False)) ∨ True)) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h8 := h6.left
      let h9 := h6.right
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h14 =>
        -- False on the left can always be used.
        apply False.elim h14
      case inr h15 =>
        -- Disjunctions on the left can always be decomposed.
        cases h15
        case inl h16 =>
          -- Conjunctions on the left can always be decomposed.
          let h17 := h7.left
          let h18 := h7.right
          -- Conjunctions on the left can always be decomposed.
          let h19 := h17.left
          let h20 := h17.right
          -- Disjunctions on the left can always be decomposed.
          cases h19
          case inl h21 =>
            -- False on the left can always be used.
            apply False.elim h20
          case inr h22 =>
            -- Conjunctions on the left can always be decomposed.
            let h23 := h22.left
            let h24 := h22.right
            -- False on the left can always be used.
            apply False.elim h24
        case inr h25 =>
          -- Conjunctions on the left can always be decomposed.
          let h26 := h7.left
          let h27 := h7.right
          -- Conjunctions on the left can always be decomposed.
          let h28 := h26.left
          let h29 := h26.right
          -- Disjunctions on the left can always be decomposed.
          cases h28
          case inl h30 =>
            -- False on the left can always be used.
            apply False.elim h29
          case inr h31 =>
            -- Conjunctions on the left can always be decomposed.
            let h32 := h31.left
            let h33 := h31.right
            -- False on the left can always be used.
            apply False.elim h33



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56568846556243727821214650301 : (((True → ((p4 → True) ∧ p4)) → ((p3 → ((((p5 → (p4 → p2)) → True) ∧ ((p5 ∧ (p5 ∨ p5)) ∧ False)) ∧ False)) ∨ (p4 ∨ p4))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258594016403824244386944164271 : ((p5 ∨ p4) → ((False ∧ ((False ∧ (p3 ∨ ((p4 ∨ (p3 → p3)) → (p4 → (((p3 → p4) → False) ∧ p5))))) ∨ (p2 ∨ True))) ∨ (p2 → p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_355563923569688254591999253802 : (p5 → (((((p5 → p2) → (p3 ∨ p1)) ∨ ((True ∧ p5) → (p3 ∧ ((p4 ∧ ((True ∧ p5) ∧ p1)) ∧ True)))) ∨ (p4 ∧ p4)) ∨ (False ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205219498557444791622116675587 : ((((p4 ∧ p4) ∧ p1) ∨ (False ∨ p3)) ∨ (((p5 ∧ (p4 ∨ (((p2 ∨ p3) ∧ (p2 ∧ True)) ∧ p1))) ∨ p5) → (((p4 → False) ∨ p5) ∨ False))) := by
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Conjunctions on the left can always be decomposed.
      let h9 := h7.left
      let h10 := h7.right
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h11 =>
        -- Conjunctions on the left can always be decomposed.
        let h12 := h10.left
        let h13 := h10.right
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h3
      case inr h14 =>
        -- Conjunctions on the left can always be decomposed.
        let h15 := h10.left
        let h16 := h10.right
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h3
  case inr h17 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44696381735598640189208424834 : ((((((p4 → p5) ∨ p2) ∨ p4) ∧ (p1 ∧ ((p2 ∨ (((p3 ∧ ((True ∧ ((p1 → p5) ∧ False)) → p1)) ∨ False) ∧ True)) ∨ p4))) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_662379559873299115302584978387 : ((((((False ∨ (True ∧ True)) ∨ ((p4 → p4) ∧ p2)) ∨ ((False ∨ p5) ∨ (((p5 ∨ False) ∧ p2) ∨ (p1 ∧ (p3 ∨ p5))))) → (False ∨ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52686819522736154250701318499 : (((p5 ∨ (((True ∨ (p3 → True)) ∨ p1) ∧ (p3 ∨ ((p4 → p1) ∧ p2)))) ∨ (p3 ∨ (False → (((p3 ∨ (True → p1)) → p4) ∧ True)))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- False on the left can always be used.
    apply False.elim h1
  case inr h4 =>
    -- False on the left can always be used.
    apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_988831896218094705027948065446 : (((p3 ∧ (((p5 ∨ ((p5 → p4) ∨ (p2 ∨ (((p2 ∨ False) ∨ (p5 → p1)) ∧ p2)))) → (False ∧ (True ∨ p3))) ∧ (p2 ∧ (p5 → p3)))) → p5) ∧ True) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h8 : (p5 ∨ ((p5 → p4) ∨ (p2 ∨ (((p2 ∨ False) ∨ (p5 → p1)) ∧ p2)))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h6
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h9 := h4 h8
  -- We need to get the left conjuct of h9 based on <expert-advice>.
  let h10 := h9.left
  -- False on the left can always be used.
  apply False.elim h10
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173137860551673299904250513625 : ((p3 ∨ ((((p5 → (((p1 ∧ (True ∧ p2)) ∨ True) ∨ p1)) ∧ p5) ∨ False) ∨ True)) ∨ (((((True → p1) ∧ (True ∨ p1)) ∧ p2) ∧ False) ∧ p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_606547560236936353140117289543 : ((((((((p2 ∧ (((p3 ∧ p3) ∨ (p2 → p2)) → p1)) ∨ (((p1 → p2) ∧ False) ∧ p2)) → ((False → p2) → p5)) → p3) ∧ p3) ∨ True) ∨ False) ∧ True) := by
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
theorem thm_5_vars_640967044839556606611652489039 : (((((p1 ∧ False) ∨ ((p5 → p2) ∧ ((p1 → p5) → (((p5 ∧ p5) → p1) ∨ (((((p5 → p2) ∧ p1) ∨ False) → False) ∧ p5))))) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214693411860378616420509185714 : (((True ∧ p2) ∨ (p4 ∨ False)) ∨ ((p3 ∧ p1) ∨ ((p5 ∧ ((p5 ∧ (False → p4)) → ((((p2 ∨ (p3 → True)) ∨ p2) ∨ p2) → False))) → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263845897314753893003726985592 : (True ∧ ((p5 ∨ ((p1 ∨ (False ∧ p2)) → (False ∧ ((True ∧ ((p2 ∨ p3) ∨ True)) ∨ p3)))) → ((p5 → (False ∨ (p2 ∨ True))) ∧ (p4 ∨ True)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
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
  -- Disjunctions on the left can always be decomposed.
  cases h1
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_773145492306175526080320804740 : (((False ∨ (((((p3 ∧ True) ∨ p3) → (p2 → (((((p5 ∧ (False → p4)) → (False ∨ p3)) → True) → (p5 ∧ p5)) → False))) ∧ False) ∧ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47278707715551277951056481087 : (((((p5 ∨ p1) ∨ (p2 → p1)) ∨ ((((p2 ∨ (((p4 ∧ (p5 ∧ False)) ∧ p1) ∧ p4)) → (p4 ∨ True)) → p2) ∨ True)) ∨ (p4 ∨ True)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_622146997200233847965174124601 : ((((p2 ∧ ((p5 → (False ∧ (False ∧ False))) ∨ (False ∧ (((p2 ∨ p3) ∨ (p3 ∧ ((True ∨ (True ∧ p4)) ∨ p3))) ∨ (p2 ∨ True))))) ∨ True) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_172310255451478678327758727814 : (((True ∧ ((p1 ∧ p1) → ((p2 ∨ p5) → p5))) → ((p5 → True) → (p4 ∧ p2))) ∨ ((p1 → True) ∨ ((p1 ∨ ((True → True) ∧ p2)) ∧ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200765298213260386875195850005 : ((p4 ∧ ((((p2 ∨ True) ∧ True) ∧ p2) → False)) → (p5 ∨ ((p2 ∨ p3) → (((p3 ∨ ((False → True) → False)) → p2) → ((p5 ∧ p2) ∧ p4))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h7 : (((p2 ∨ True) ∧ True) ∧ p2) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h6
      -- True on the right can always be proven directly.
      apply True.intro
      -- One of the premise coincides with the conclusion.
      exact h6
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h8 := h3 h7
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h10 : (p3 ∨ ((False → True) → False)) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h9
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h11 := h5 h10
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h12 : (((p2 ∨ True) ∧ True) ∧ p2) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h11
      -- True on the right can always be proven directly.
      apply True.intro
      -- One of the premise coincides with the conclusion.
      exact h11
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h13 := h3 h12
    -- False on the left can always be used.
    apply False.elim h13
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h14 =>
    -- One of the premise coincides with the conclusion.
    exact h14
  case inr h15 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h16 : (p3 ∨ ((False → True) → False)) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h15
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h17 := h5 h16
    -- One of the premise coincides with the conclusion.
    exact h17
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h18 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h19 =>
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42906445392225531428062576592 : (((p3 → ((p1 → p5) ∨ ((p4 → ((p3 → (True ∨ ((p4 → False) ∨ (p5 ∨ (p4 → p3))))) ∨ (p2 ∧ p4))) → (p3 → p2)))) ∨ True) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61884091046915284295321631122 : ((p2 ∧ ((p3 → (p4 ∧ ((p5 ∨ (p3 ∧ ((p4 → (p1 ∨ p1)) ∨ False))) → ((p1 ∧ (True ∧ (p1 ∨ True))) ∨ False)))) ∧ (p3 → p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_653903407537991521738355410078 : ((((((p1 ∨ (p1 ∧ p3)) → ((False ∨ (False ∨ ((((False → p3) ∧ False) ∨ True) → ((p2 → p4) ∧ p3)))) ∧ p5)) ∧ p2) ∨ (p4 ∨ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_212741222035168808526261451021 : ((p1 → ((False ∨ True) ∧ p1)) ∧ ((True → (((p3 ∧ ((True ∧ (True ∧ p1)) ∧ p3)) → (p2 → p5)) → ((p3 ∧ p3) ∧ True))) ∨ (p3 → True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310220795941739461674781459325 : (p2 ∨ ((p2 ∧ ((p2 → p4) ∧ (False ∧ (p5 ∧ ((False ∧ p3) ∨ True))))) ∨ (False → (p5 ∨ (p3 ∧ (True ∧ (((p2 ∨ p4) ∧ p3) ∨ p2))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165217586686243369243662877413 : ((((False ∨ (((p3 → (True ∧ p2)) → p4) ∨ False)) ∨ ((p3 → p3) ∧ True)) ∨ (p2 ∧ True)) ∨ (((p4 ∧ p3) ∨ True) → (p4 → (True ∧ p1)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_145015898988280811483835896074 : ((((p5 → (((p4 ∨ (p5 ∧ p2)) → p4) → (True → p5))) → p4) ∨ ((True ∨ (True ∨ True)) ∨ (True ∨ p2))) ∧ (True ∧ (False ∨ (p3 → True)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167735252701579854087560330952 : ((((p3 ∧ ((p1 ∧ (p3 → p2)) ∧ p4)) ∨ (p4 ∧ (p3 ∨ p2))) ∨ ((p5 ∧ p1) ∨ p1)) → ((((True ∨ (p4 ∨ p2)) ∨ p3) ∧ False) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h3 =>
      -- Conjunctions on the left can always be decomposed.
      let h4 := h3.left
      let h5 := h3.right
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Conjunctions on the left can always be decomposed.
      let h8 := h6.left
      let h9 := h6.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
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
    -- Disjunctions on the left can always be decomposed.
    cases h15
    case inl h16 =>
      -- Conjunctions on the left can always be decomposed.
      let h17 := h16.left
      let h18 := h16.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h19 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112378774740928841159977594916 : ((((((True ∧ (((p3 ∨ p2) ∧ True) → ((p5 ∧ p5) ∨ True))) ∨ ((p3 ∨ False) → True)) ∨ ((True ∨ p4) ∧ True)) ∧ p2) → p4) ∨ (p3 → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_755474422608561095543874907185 : (((p1 ∧ ((True ∧ ((p4 ∨ (((p5 ∧ (p1 → True)) ∨ (False ∧ (p5 ∧ ((False ∧ True) ∧ p5)))) ∧ (p3 → p4))) ∧ (p4 ∧ False))) ∧ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64522321891018454266282598594 : ((p1 ∨ ((((p4 ∨ (True → False)) → (False ∧ (p1 → p4))) → p4) ∨ ((False → (p3 → p5)) ∨ ((((p4 ∨ p4) → False) ∨ p1) → p4)))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47121703977631322228293698078 : (((((((((True ∨ True) → ((p5 ∨ False) ∨ (True ∨ p3))) ∨ (p4 → p1)) → p3) ∨ False) ∧ True) → ((True ∨ p3) ∧ False)) ∨ (True ∨ p4)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58965578377114614960452588146 : (((p2 ∧ p2) ∨ ((p3 ∨ False) ∨ (p5 → ((True ∧ p3) ∨ (((p3 → p3) ∨ ((((p4 ∧ p1) → p5) ∨ p1) ∨ (True → False))) ∨ p1))))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337896010602504523815698959944 : (p1 → (((p2 ∧ (False ∨ False)) → (p4 ∨ ((p1 → ((p2 ∨ p4) ∨ p5)) ∨ p5))) → (((p2 ∨ p4) → (p5 ∧ (p4 → (p2 ∧ p5)))) ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38018274932014229342304760526 : ((((p4 ∨ (p3 ∧ ((p1 ∧ (((False → True) ∨ ((p1 ∨ (p5 ∨ p3)) ∨ (p1 ∧ p5))) → (p1 ∨ False))) ∨ p5))) ∨ (p4 → p3)) ∧ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178679750102434642489166193421 : (((p2 → (p5 ∧ (False ∨ False))) ∧ ((p4 → p2) ∧ ((p3 → p1) ∨ False))) ∨ (((p5 ∧ p4) → ((p3 ∧ p2) ∨ (False → (p4 ∧ True)))) ∨ False)) := by
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
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_108173768522747075081642202576 : (((p2 → False) → (((((p1 → (False ∧ p5)) ∨ p2) ∨ p5) → (((True ∨ (p4 ∧ p3)) → p2) → ((p3 → p3) → p2))) ∨ p5)) ∧ (False → p4)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h7 : (True ∨ (p4 ∧ p3)) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h8 := h3 h7
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h9 =>
      -- One of the premise coincides with the conclusion.
      exact h9
  case inr h10 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h11 : (True ∨ (p4 ∧ p3)) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h12 := h3 h11
    -- One of the premise coincides with the conclusion.
    exact h12
  -- Implications on the right can always be decomposed.
  intro h13
  -- False on the left can always be used.
  apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205529648293605842967622658631 : (((False ∨ p4) ∧ ((p1 ∨ True) ∨ False)) ∨ ((p4 → p1) → ((p3 ∧ p4) → ((True ∧ False) ∨ ((((False ∧ (p5 ∧ p4)) ∨ True) ∧ False) ∨ p1))))) := by
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
  have h5 : p4 := by
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h5
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52356070240534230449861877967 : (((((p5 → (p1 ∨ p5)) → (True ∨ ((False → p5) ∧ p1))) ∧ (False ∧ p5)) ∧ (p3 ∨ (p2 → ((p4 → ((True ∨ p3) ∨ p5)) → p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_986582258103307344343033482803 : (((p2 ∧ (((p1 ∧ p2) → False) ∧ ((((((False ∧ (p4 ∧ (True ∧ p5))) → p3) ∧ ((False → False) ∧ p5)) ∧ p1) ∧ p2) ∧ (False ∨ p2)))) → p4) ∧ True) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- Conjunctions on the left can always be decomposed.
  let h10 := h8.left
  let h11 := h8.right
  -- Conjunctions on the left can always be decomposed.
  let h12 := h10.left
  let h13 := h10.right
  -- Conjunctions on the left can always be decomposed.
  let h14 := h13.left
  let h15 := h13.right
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h16 =>
    -- False on the left can always be used.
    apply False.elim h16
  case inr h17 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h18 : (p1 ∧ p2) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h11
      -- One of the premise coincides with the conclusion.
      exact h17
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h19 := h4 h18
    -- False on the left can always be used.
    apply False.elim h19
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167698650675094073994396939551 : (((((p3 ∧ p5) ∧ p1) ∧ (((False ∧ (True ∨ True)) → True) → p5)) ∧ ((False ∧ p4) → p1)) → ((((p2 ∨ p2) ∨ p1) → p4) ∨ (False → p3))) := by
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
  let h8 := h6.left
  let h9 := h6.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h10
  -- False on the left can always be used.
  apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354660779580424731348293525242 : (p5 → ((((p1 ∧ (False → p3)) ∨ ((((False ∧ ((p4 ∧ True) ∧ p5)) → ((p4 ∧ p2) ∧ p1)) ∧ True) → ((p3 → p2) ∨ p4))) → False) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136964688202671479430668485310 : (((p1 ∧ p1) → ((((p5 → True) → ((p3 ∧ p4) → p4)) ∧ (p1 → (p1 ∧ True))) → ((p4 → (p3 → True)) ∧ p3))) ∨ ((p2 ∨ True) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_212270130712510762041663317238 : ((False ∨ (p3 → (p2 ∨ True))) ∧ (((p4 ∨ (((p3 ∨ (True → (p1 ∨ (p1 → p5)))) ∨ ((False ∨ False) → True)) ∨ (p5 ∨ True))) ∧ False) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1721708557529454368794147347 : (((p4 ∨ (((p2 ∨ ((p4 ∨ p1) ∨ p1)) → False) → (False ∧ p4))) ∨ ((p2 ∧ p3) → ((True → p2) → p2))) ∧ (True → (False ∨ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  exact h3
  -- Implications on the right can always be decomposed.
  intro h5
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158385326289849814783863037534 : (((p1 → p1) ∧ (((p5 ∧ (((p2 → p5) → ((True → (p1 ∧ p2)) → True)) → p4)) ∨ True) ∨ p5)) ∨ (p4 ∨ ((p2 → p4) → (p4 ∧ p3)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_76674808964860684258177906432 : ((((((p1 ∧ (((True ∨ p3) ∧ p4) → p4)) ∨ ((True ∨ p2) ∧ p3)) ∨ (False ∧ p3)) ∨ ((((p4 ∨ p2) → True) → p4) ∨ True)) → p1) → p1) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((((p1 ∧ (((True ∨ p3) ∧ p4) → p4)) ∨ ((True ∨ p2) ∧ p3)) ∨ (False ∧ p3)) ∨ ((((p4 ∨ p2) → True) → p4) ∨ True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_613164260899642102729571668917 : (((((((p3 ∧ (((p2 ∧ p1) ∧ ((p3 ∧ ((p3 ∨ p4) ∧ p5)) ∨ (p3 ∧ p1))) → True)) ∧ p3) → (p3 ∧ p3)) → (p5 ∧ True)) ∨ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_765734938685853448569143264763 : (((p4 ∧ (((((False → p4) → (p4 ∨ (p1 ∧ p5))) → p2) ∨ p3) → ((((p5 → ((p5 ∨ True) ∧ p4)) ∧ (False ∧ p3)) ∧ False) ∧ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1163572243738075221013457357 : ((((True ∨ (p4 ∧ p1)) ∨ False) → ((((p2 → (p1 → p1)) → (((p4 ∨ p2) ∧ (p1 ∨ p2)) → p3)) ∧ p2) ∧ (p2 ∨ p2))) → p2) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((True ∨ (p4 ∧ p1)) ∨ False) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the left conjuct of h3 based on <expert-advice>.
  let h4 := h3.left
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50296488840740611461992418177 : (((((((p5 ∨ (p4 → (p5 ∧ p3))) → False) → (p3 ∨ p1)) → (p5 ∨ p2)) ∨ (False → (True ∨ p4))) ∨ ((p1 → p1) ∨ (p2 ∨ False))) ∨ p2) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112057429817879797643796310985 : ((((p4 ∧ True) ∧ ((((False ∧ p2) ∨ (p2 → (p3 ∧ ((p1 → ((p3 ∧ p1) ∧ p2)) ∧ p4)))) → p3) → (p2 ∧ p3))) ∨ p5) ∨ (False → False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_610573957643253693080285398055 : (((((((((((p1 ∧ (p3 ∨ (p4 ∧ p5))) ∨ p4) ∨ True) ∧ (((p5 → p1) ∧ p2) → True)) ∨ p1) → p1) ∨ (False → p3)) → p2) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192468509331933161114944440435 : ((((p3 → (False ∨ (True ∨ p3))) ∨ (p5 ∧ p1)) ∨ p2) → ((False ∨ False) ∨ (True ∨ (p1 ∧ (p2 ∨ ((p2 ∨ ((p2 ∨ p5) → True)) ∧ p3)))))) := by
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
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h4 =>
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
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
theorem thm_5_vars_48171144413312199565479535881 : ((((True → p2) ∧ ((False ∨ ((False → (((False → False) → p2) ∧ (p2 → p4))) → ((p4 → (p2 ∧ p3)) ∧ True))) → p4)) → (p5 ∧ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_226371724102137407053224992923 : (((True → p3) ∨ False) ∨ (((p2 ∨ ((False ∧ p2) → ((((p3 ∨ p5) → True) ∧ (p5 ∧ p1)) ∧ p5))) → (p3 ∧ (p5 ∧ (p4 → p1)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190663521909980338385534644259 : (((True → (((p1 → p2) ∧ p2) ∨ (p1 ∨ False))) → False) ∨ ((True → (False → (p2 ∧ (p3 ∧ False)))) ∧ ((p1 → p1) ∨ (p4 ∨ (p3 → p3))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h2
  -- False on the left can always be used.
  apply False.elim h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113610239390376907734979496479 : (((p3 ∨ (True → (False ∧ (p1 ∨ (True ∧ ((p1 ∨ (((p1 → (p4 ∧ p3)) → p3) ∨ (p4 ∧ p4))) → p4)))))) ∨ (False ∧ p3)) ∨ (False → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113604594614144659533424370889 : (((p2 ∨ (((p4 ∧ (p5 ∨ ((p4 ∨ p1) ∨ ((p5 ∨ p5) ∨ (p3 ∧ (False → (True ∨ p2))))))) ∧ p5) ∨ False)) ∨ (True ∧ True)) ∨ (p3 ∧ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_619348635188998570607672873547 : ((((((p4 ∧ p1) → p2) → ((((p4 ∨ p2) → ((True ∨ (p1 ∧ False)) → ((p2 → True) → ((p5 ∧ True) → p1)))) ∧ p5) ∧ p1)) ∨ True) ∨ False) ∧ True) := by
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
theorem thm_5_vars_114072614290162984369803824291 : (((((False ∧ (False → p1)) ∨ False) ∧ (p4 ∨ ((p2 ∧ (p3 ∨ (p1 ∧ p1))) ∧ (False ∨ (p2 ∧ p3))))) ∨ (p3 → (p2 → p1))) ∨ (p5 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



