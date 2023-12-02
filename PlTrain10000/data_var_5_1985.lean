variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_339746573527424826756255254518 : (p1 → (p4 ∨ (((p2 → (p1 → ((p4 → p2) ∨ True))) → ((False → True) ∧ p4)) ∨ (False → ((p1 ∨ ((p1 → (p4 → p2)) ∧ False)) → False))))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- False on the left can always be used.
    apply False.elim h2
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- False on the left can always be used.
    apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257549980400962972829777949960 : ((p3 ∨ p1) → ((((((True → (p1 ∨ (((p2 ∧ False) ∧ p3) ∧ (p2 ∨ p1)))) ∧ p3) ∧ True) → p2) ∨ (p1 → ((p4 ∨ p1) ∨ p2))) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52109076321510532650384380411 : ((((((p1 ∧ ((p2 ∨ p5) ∧ (((p2 ∨ p4) ∧ False) ∧ p4))) ∧ p5) ∨ True) → p4) → (p4 ∧ (p5 → (((True → p3) ∨ p5) ∨ p1)))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p1 ∧ ((p2 ∨ p5) ∧ (((p2 ∨ p4) ∧ False) ∧ p4))) ∧ p5) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299334823799586559407823490808 : (False ∨ (((p1 ∧ (p2 ∧ (p4 ∨ p5))) → (((p4 → p1) → p4) ∨ ((p5 → (p1 → ((False ∧ True) ∧ ((p5 ∧ p5) ∨ p1)))) ∨ p1))) ∨ p3)) := by
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
  let h4 := h3.left
  let h5 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259249910813052869514190078707 : ((False → p1) → (((False ∨ (False ∧ (((p3 → p2) → False) ∨ (p4 ∨ (True ∧ ((p2 → p1) ∧ ((p3 → p1) ∨ True))))))) ∨ (p2 → p2)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337076648023317981792600661445 : (p1 → ((((((p2 ∧ p1) ∧ p5) → (((((p2 → p5) ∨ p2) ∨ p3) → (p5 ∨ p2)) → p4)) → p5) ∧ (False → (p4 → False))) ∨ (True ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137618411370892241154081620446 : ((False ∨ (((p3 → (((((p2 ∧ (False ∨ p1)) ∧ (False ∨ p3)) ∧ p4) ∨ True) ∧ (p2 → True))) → (p5 ∨ p2)) ∨ True)) ∨ (p4 → (False ∨ p3))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40424816137967538170165871802 : (((((True → (((True ∧ (False ∨ True)) ∨ ((p3 → p3) → (False ∨ True))) ∧ p2)) → (p2 ∧ (p1 ∧ (False ∧ (p1 → p1))))) ∨ p1) ∨ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187067327817371319344511026946 : (((p2 ∨ p4) ∧ (True → (p4 ∧ (p4 ∨ (True → (p1 → p1)))))) → ((p3 ∨ ((True → (p4 ∨ ((p5 ∨ p2) → p5))) ∨ p1)) ∧ (p4 ∨ p4))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h6 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h7 := h3 h6
    -- We need to get the left conjuct of h7 based on <expert-advice>.
    let h8 := h7.left
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h10
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h9
  -- Conjunctions on the left can always be decomposed.
  let h11 := h1.left
  let h12 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h11
  case inl h13 =>
    -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
    have h14 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h12, we can now drive its conclusion.
    let h15 := h12 h14
    -- We need to get the left conjuct of h15 based on <expert-advice>.
    let h16 := h15.left
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h16
  case inr h17 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_697940786160021093933642584276 : (((((p2 ∧ ((False ∨ ((True ∨ p2) → True)) → (p3 ∨ p3))) ∧ p3) ∨ (p5 → ((p2 → (True ∧ ((p1 → p4) → p1))) → (p4 ∨ True)))) ∨ p3) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_327812126076298148121076601978 : (True → ((((((p5 ∨ (p5 → ((((p2 → p5) ∧ p1) → p1) ∧ p3))) ∧ (p3 → (False ∧ p3))) ∧ (False → False)) → p1) → p2) ∨ (False → False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_241508650795731056523211510412 : ((False → p2) ∧ (p5 → (((p5 ∧ ((False ∧ p1) ∧ (((p4 ∧ p1) → p1) ∧ (((False ∨ p4) → (p3 → (p1 → p3))) → p3)))) ∧ False) ∨ p5))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_327397127327690639799063072705 : (True → ((((((((p4 ∨ p2) ∨ p3) ∨ p2) → (False ∨ True)) ∨ (((p2 ∨ (p4 ∨ True)) → p3) ∧ False)) → False) ∧ ((p1 ∨ p1) ∨ p4)) → p3)) := by
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
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h7 : (((((p4 ∨ p2) ∨ p3) ∨ p2) → (False ∨ True)) ∨ (((p2 ∨ (p4 ∨ True)) → p3) ∧ False)) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h8
        -- Disjunctions on the left can always be decomposed.
        cases h8
        case inl h9 =>
          -- Disjunctions on the left can always be decomposed.
          cases h9
          case inl h10 =>
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
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h15 := h3 h7
      -- False on the left can always be used.
      apply False.elim h15
    case inr h16 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h17 : (((((p4 ∨ p2) ∨ p3) ∨ p2) → (False ∨ True)) ∨ (((p2 ∨ (p4 ∨ True)) → p3) ∧ False)) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h18
        -- Disjunctions on the left can always be decomposed.
        cases h18
        case inl h19 =>
          -- Disjunctions on the left can always be decomposed.
          cases h19
          case inl h20 =>
            -- Disjunctions on the left can always be decomposed.
            cases h20
            case inl h21 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- True on the right can always be proven directly.
              apply True.intro
            case inr h22 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- True on the right can always be proven directly.
              apply True.intro
          case inr h23 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
        case inr h24 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h25 := h3 h17
      -- False on the left can always be used.
      apply False.elim h25
  case inr h26 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h27 : (((((p4 ∨ p2) ∨ p3) ∨ p2) → (False ∨ True)) ∨ (((p2 ∨ (p4 ∨ True)) → p3) ∧ False)) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h28
      -- Disjunctions on the left can always be decomposed.
      cases h28
      case inl h29 =>
        -- Disjunctions on the left can always be decomposed.
        cases h29
        case inl h30 =>
          -- Disjunctions on the left can always be decomposed.
          cases h30
          case inl h31 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h32 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
        case inr h33 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h34 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h35 := h3 h27
    -- False on the left can always be used.
    apply False.elim h35



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256835822230727662004167400498 : ((p1 ∨ p3) → (((((((((False ∧ ((True ∧ p2) ∧ False)) → p5) ∧ p3) ∧ (p1 ∧ p4)) ∧ p1) ∨ True) ∧ True) ∨ p5) ∨ (p5 ∨ (False → False)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
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
  case inr h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
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
theorem thm_5_vars_134875202668526712957684812359 : (((p2 → ((((p3 → ((p2 ∧ (True ∧ True)) ∨ p2)) ∧ True) ∨ (((False ∧ p1) ∨ (True → p3)) ∨ False)) → p4)) → p4) ∨ (p4 ∨ (p1 → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38115782278741695654855322713 : (((((p1 ∨ (p1 ∧ ((False ∧ p2) → (p3 ∨ (True → (((False ∨ (True → True)) ∧ False) → p3)))))) → p4) ∧ (p1 ∧ (False → p3))) ∧ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114960691319600710016507394250 : (((p2 ∨ (p4 ∧ (((p2 → p5) → p4) ∧ ((p2 ∨ p4) ∧ (True ∨ p4))))) → ((True → ((p5 → True) ∨ (False → True))) → p1)) ∨ (p1 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171899538476284295760470051263 : (((p5 ∨ (((p2 ∨ False) ∧ (True → (p1 ∨ (True ∨ False)))) → (p4 ∨ p1))) → p5) ∨ (p4 ∨ (False → (p5 ∨ (False ∧ (p5 ∨ (p1 ∧ p3))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205111154036246352855381278862 : ((((p5 ∧ p1) ∨ p5) ∧ (False ∧ p1)) ∨ (((p4 ∨ (p2 → p4)) → ((((p2 ∨ p1) ∨ p2) ∨ True) ∧ ((False → (False ∧ True)) ∨ True))) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Disjunctions on the left can always be decomposed.
  cases h1
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
theorem thm_5_vars_115350352167646379385983510966 : ((((((False ∨ (p2 ∧ p2)) ∧ True) → p2) ∧ p3) ∧ (True ∧ ((((p5 → (p1 → True)) → (p5 ∨ p1)) ∧ p4) ∧ (False ∧ p3)))) ∨ (p3 → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_609284907471434632022280238452 : ((((((p1 ∧ True) ∧ (((((p2 → p3) ∧ p2) → p5) ∨ (((p3 ∧ ((p3 → p1) ∧ p2)) → p5) ∨ (False ∨ True))) ∨ p5)) ∨ p5) ∨ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_680639286433445237616859040165 : ((((((True → (p2 ∧ (False ∧ p4))) ∧ p4) ∨ (p4 → ((p2 ∧ ((p4 ∨ (p4 ∨ p5)) → p1)) ∨ True))) → ((p4 ∨ p5) ∨ (False ∨ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61465443671368955028886721394 : ((p1 ∧ ((((p2 ∧ (p5 ∨ False)) ∧ p2) ∧ (((p3 → (((True ∧ False) ∨ p5) ∧ p4)) → (True → p3)) ∧ (p2 ∨ True))) ∨ (p4 → False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_676202127096436964540354982389 : ((((((True ∧ p1) → p1) ∧ (((False → (p5 → ((p2 ∧ True) ∨ (p5 ∧ False)))) → (p1 ∧ False)) ∨ True)) ∧ (p5 ∨ ((True → p3) → p3))) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h5 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h6 := h4 h5
  -- One of the premise coincides with the conclusion.
  exact h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_9346712685993932516176422933 : ((((p3 ∧ ((p4 ∨ p1) ∨ (True → p2))) → ((((False ∧ (p1 → True)) ∧ ((p3 ∧ False) ∨ ((p1 → p5) ∧ p4))) → p1) → p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_224997280822657548519929030520 : (((True ∧ p3) ∧ p4) ∨ (((True → ((False ∧ p4) ∧ (False ∨ p4))) ∨ ((((p3 ∨ p4) ∧ (p2 ∨ p3)) ∧ p3) → (False ∨ (p2 → True)))) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h13
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h14 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h15
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187156200768256377359217158811 : (((p2 → p4) ∨ (((p2 → p5) → (p3 ∨ False)) ∨ (p2 ∧ p1))) → ((((True ∧ (True → (p2 → False))) ∧ p5) → ((p2 ∨ p3) ∧ p5)) ∨ True)) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112477162184340106807702705901 : (((((p3 → p4) ∧ (((p1 ∧ (p1 ∨ (p5 ∧ p5))) → (p4 ∨ (False ∨ (p2 ∧ ((p3 → p4) ∨ p5))))) ∨ p1)) ∨ False) → p1) ∨ (True ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43102434465485522400629704474 : ((((((((True ∧ (p3 ∨ (p4 → True))) → p3) → (p4 → p3)) → ((p2 ∨ (p3 ∨ p2)) → p4)) ∨ ((p2 ∧ p4) ∨ p5)) ∧ True) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_69005123758361253576655349913 : ((p5 → (((p1 → ((p2 ∨ p3) → False)) ∨ (((False ∨ (p2 → ((True → p2) → (False → (False ∧ p1))))) ∧ (p1 ∧ p5)) → p2)) ∧ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68188166100151746025053738167 : ((p3 → (((((p4 → ((((True ∧ (p5 ∨ p4)) → p3) → p5) → p1)) → (p1 → p1)) → p1) → ((p5 ∨ (False → p1)) ∧ p1)) ∨ p1)) ∨ False) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : ((p4 → ((((True ∧ (p5 ∨ p4)) → p3) → p5) → p1)) → (p1 → p1)) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- Implications on the right can always be decomposed.
    intro h6
    -- One of the premise coincides with the conclusion.
    exact h6
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h7 := h2 h4
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53950050298966054891140925211 : (((p4 → (p1 ∨ (p1 ∧ ((p2 ∨ p3) ∨ (p4 ∨ False))))) ∨ (((((True ∧ p2) ∧ p5) → (((p2 ∨ True) → False) → p2)) ∧ False) ∨ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354795608003420119689696043080 : (p5 → (((True → (p2 ∧ (p1 → (p4 ∨ p3)))) ∨ (((True ∧ p5) ∧ (True ∧ ((p3 → ((p2 ∧ (p1 ∧ p3)) ∧ False)) → False))) ∨ p5)) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51341889253911143846198059982 : (((p4 → (p1 ∨ (((p1 ∨ (p4 ∨ p2)) → False) ∨ ((p1 ∨ (False ∧ p1)) ∧ (False ∧ p5))))) ∨ (((p3 ∧ p4) → (p4 ∨ p5)) → True)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_757418407768951557238212308706 : (((p1 ∧ ((p4 → p2) → (((((True ∧ p5) ∧ p1) ∨ ((True ∨ (((p1 ∨ p1) → p5) ∨ p2)) ∨ ((p2 ∨ p5) → p4))) → True) → p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328292487865622340275963547723 : (True → (((p2 ∨ (((p2 ∧ (True → p5)) ∨ p1) ∨ p1)) ∨ (p1 ∨ (p1 ∨ ((p4 ∨ (True ∨ p3)) → p2)))) ∨ ((True → (p1 ∧ True)) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256772708007219450615138354211 : ((p1 ∨ p2) → ((((((p3 → (p3 ∨ ((p3 → ((p4 ∧ True) → p3)) → (p2 → (p2 ∧ True))))) ∨ p4) → p3) ∨ p2) ∨ True) → (p4 ∨ True))) := by
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
    case inr h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
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
    -- Disjunctions on the left can always be decomposed.
    cases h1
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260956747805216033139267493126 : ((p4 → p1) → (((((p5 → (p2 ∧ False)) ∧ (p4 → False)) ∨ ((p3 → p2) ∧ p4)) ∧ ((p2 ∧ (p2 → ((p3 ∨ p2) → p2))) ∨ False)) → p2)) := by
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
    cases h4
    case inl h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- One of the premise coincides with the conclusion.
      exact h9
    case inr h11 =>
      -- False on the left can always be used.
      apply False.elim h11
  case inr h12 =>
    -- Conjunctions on the left can always be decomposed.
    let h13 := h12.left
    let h14 := h12.right
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h15 =>
      -- Conjunctions on the left can always be decomposed.
      let h16 := h15.left
      let h17 := h15.right
      -- One of the premise coincides with the conclusion.
      exact h16
    case inr h18 =>
      -- False on the left can always be used.
      apply False.elim h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111650539164253818963658406126 : (((((p3 → p2) ∧ (((p1 ∧ ((((p5 → p2) ∧ p3) ∨ p3) ∨ (p3 → p2))) → p5) → ((p1 → p3) ∧ True))) ∨ p4) ∨ p2) ∨ (p3 → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_877423883470759142377452943 : ((True → (p5 ∨ (((((False → (p2 ∧ True)) → (True ∨ (p3 ∨ (p3 ∧ p2)))) → p5) ∧ ((p4 ∨ (p4 ∨ p2)) → p1)) ∧ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111259094477070853805975557640 : ((((p3 ∨ False) ∨ (p5 ∨ (p4 ∨ (p1 ∨ ((True ∧ ((False → (((p1 ∧ p3) ∨ p2) ∧ (p4 ∨ p3))) ∨ p3)) → p1))))) ∧ False) ∨ (True ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52620281732430996809272488651 : (((((p3 ∧ True) → p4) ∨ ((p1 → ((p5 → (p2 → p1)) ∨ p5)) → p5)) ∨ ((True ∨ ((p1 → (p1 ∨ (False ∧ True))) ∨ p1)) ∧ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67590125458051651638025606428 : ((p1 → (True ∧ (((False ∨ p4) ∧ (p2 ∧ (((p3 → p4) ∨ p4) ∨ ((p4 ∨ (((p5 ∨ p3) ∧ p1) ∧ p3)) ∨ (False ∧ p5))))) → False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323838213490390407092076919465 : (p5 ∨ (((True → False) ∧ ((p4 ∧ ((True ∧ (p5 ∨ (False → True))) ∧ (p4 ∧ p4))) ∧ (False → p3))) → ((False ∨ ((p3 ∧ p1) ∧ p2)) ∨ p2))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h8 := h7.left
  let h9 := h7.right
  -- Conjunctions on the left can always be decomposed.
  let h10 := h8.left
  let h11 := h8.right
  -- Disjunctions on the left can always be decomposed.
  cases h11
  case inl h12 =>
    -- Conjunctions on the left can always be decomposed.
    let h13 := h9.left
    let h14 := h9.right
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h15 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h16 := h2 h15
    -- False on the left can always be used.
    apply False.elim h16
  case inr h17 =>
    -- Conjunctions on the left can always be decomposed.
    let h18 := h9.left
    let h19 := h9.right
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h20 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h21 := h2 h20
    -- False on the left can always be used.
    apply False.elim h21



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118457822471316364188939921023 : ((p3 ∨ (((((((p2 ∨ p2) ∧ True) ∨ (p2 ∧ (p1 ∧ (p5 ∨ p4)))) ∧ p4) → p5) ∧ (((False → False) → p1) ∨ p4)) ∨ True)) ∨ (p2 ∧ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54476695155187839544966167598 : (((((p2 ∨ (p1 ∨ p5)) ∧ p3) ∨ (p3 ∧ True)) ∨ (True ∨ ((p5 ∨ p1) ∨ ((p2 ∧ (((p2 ∧ p2) ∧ p1) ∧ p4)) ∧ (p3 → p1))))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_687219306597369664777804275235 : (((((((((((p5 ∨ True) ∨ True) ∨ True) → (p1 ∧ p1)) ∨ p1) ∨ p3) ∧ p1) ∧ p3) ∧ (((True ∨ p4) ∧ p4) → (False ∨ (True ∧ p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336204579745420394853240929117 : (p1 → (((p5 ∨ (p4 → (p4 ∧ (((p4 → (((p5 ∨ (p3 → (True ∨ (False → False)))) → p2) ∨ p5)) → p5) → p3)))) ∨ (False → p2)) ∨ p3)) := by
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
theorem thm_5_vars_200961673189523992080750900952 : ((p2 ∨ ((False → (p1 ∧ True)) → (p4 ∧ p5))) → ((((p2 ∨ p5) → p3) ∨ p2) ∨ ((((p2 ∨ (p3 ∨ p5)) ∧ (True → False)) ∧ False) ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h4 : (False → (p1 ∧ True)) := by
      -- Implications on the right can always be decomposed.
      intro h5
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- False on the left can always be used.
      apply False.elim h5
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h6 := h3 h4
    -- We need to get the left conjuct of h6 based on <expert-advice>.
    let h7 := h6.left
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_780661983850560269319912266118 : (((p2 ∨ ((((p4 ∨ p3) ∨ (p1 ∧ p3)) ∧ (False ∨ True)) ∨ (p2 ∨ ((p4 ∨ p1) ∨ ((((p4 → p2) → True) ∨ (p1 → p4)) ∨ True))))) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_49152449421099712894878589777 : ((((((p4 ∨ ((True → False) ∧ True)) ∨ False) → p2) ∨ (((p1 → (((p3 ∨ p3) → p4) ∧ p4)) → p3) ∨ p1)) ∨ (False → (p5 ∧ p2))) ∨ p5) := by
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
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136026754653513506410280891837 : ((((((p3 ∧ False) → p4) ∨ p1) ∨ ((p5 ∧ p4) → True)) → (p3 ∧ ((False ∨ False) ∧ ((True → p2) ∧ (p1 → p4))))) ∨ ((p4 → p4) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64381110755509080829919809424 : ((p1 ∨ ((True → ((((p5 → True) ∧ ((p4 ∨ (False ∧ p5)) ∧ (p1 ∧ ((False ∧ (p1 ∧ (True ∧ p3))) ∨ True)))) ∧ p2) → p3)) ∨ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178291437378850936685135233077 : (((p2 ∨ (((((p4 ∨ p2) → True) ∨ p4) ∨ p4) ∧ p2)) ∧ (p2 ∧ p1)) ∨ ((p2 → ((False ∧ p3) ∧ True)) ∨ ((False ∨ (True ∨ p5)) ∨ False))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_194025080499138198068443806723 : ((p4 ∨ (p2 ∨ ((False ∧ (p2 ∨ p3)) ∨ (p4 ∨ p5)))) → (((p1 → (p1 ∧ (p2 ∨ False))) → (p2 → (p4 ∧ p1))) ∨ (p2 → (True → True)))) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h7
      -- Implications on the right can always be decomposed.
      intro h8
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Conjunctions on the left can always be decomposed.
        let h11 := h10.left
        let h12 := h10.right
        -- False on the left can always be used.
        apply False.elim h11
      case inr h13 =>
        -- Disjunctions on the left can always be decomposed.
        cases h13
        case inl h14 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h15
          -- Implications on the right can always be decomposed.
          intro h16
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h17 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h18
          -- Implications on the right can always be decomposed.
          intro h19
          -- True on the right can always be proven directly.
          apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_948332911883565444186900691175 : ((((p2 ∨ (p1 → (p1 → p1))) → (p5 ∧ (((True → ((((p5 → (p5 ∨ p2)) ∨ (p5 ∨ p3)) → p4) ∨ False)) ∨ p5) ∧ (p2 ∨ p2)))) → p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p2 ∨ (p1 → (p1 → p1))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h2
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- One of the premise coincides with the conclusion.
    exact h9
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50817200566743554282676501822 : (((p4 → (p1 ∧ (((((p3 ∨ False) ∧ (((p3 ∧ p5) ∧ (p2 → p4)) ∨ p2)) → p3) ∨ p3) → p1))) → (p3 → ((p5 ∧ p5) ∧ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56888524353305059823847380655 : (((p3 ∧ (p1 ∧ p4)) ∧ (p4 ∧ (((((False ∨ (p1 → (False ∨ (False ∧ (p1 ∧ p1))))) ∨ False) ∨ p3) ∧ (p1 → False)) ∧ (p2 ∨ p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_655926057372062101959784314998 : ((((((((p2 → p1) → (((False ∧ p3) ∨ p3) → False)) → False) ∧ ((p1 → p1) → False)) ∧ (((False ∨ False) → p1) ∧ p5)) ∨ (False → p1)) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_114030748512192378463371858333 : (((((True ∧ ((((p5 → p4) ∧ p2) ∧ False) ∨ (p2 → (p3 ∧ p4)))) ∨ (p4 → (p4 → True))) → False) ∨ (p4 ∨ (False ∨ p3))) ∨ (False → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166513052416732072115688460425 : ((p4 ∨ ((((p3 ∧ p3) → (p4 → ((p4 ∨ p3) ∧ p5))) ∨ (p3 ∨ True)) ∧ (p1 ∨ p1))) ∨ (p1 ∨ ((p4 ∨ p4) ∨ ((False ∧ True) → False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_86676688571424519107302460842 : (((True ∧ (((p3 → (p5 ∧ p5)) ∧ p5) ∧ p5)) ∧ ((((p5 ∨ (p5 ∨ p1)) ∨ (p2 ∨ p1)) ∧ p2) ∧ ((False → (p1 → True)) → p3))) → p3) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h10 := h3.left
  let h11 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h12 := h10.left
  let h13 := h10.right
  -- Disjunctions on the left can always be decomposed.
  cases h12
  case inl h14 =>
    -- Disjunctions on the left can always be decomposed.
    cases h14
    case inl h15 =>
      -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
      have h16 : (False → (p1 → True)) := by
        -- Implications on the right can always be decomposed.
        intro h17
        -- Implications on the right can always be decomposed.
        intro h18
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h11, we can now drive its conclusion.
      let h19 := h11 h16
      -- One of the premise coincides with the conclusion.
      exact h19
    case inr h20 =>
      -- Disjunctions on the left can always be decomposed.
      cases h20
      case inl h21 =>
        -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
        have h22 : (False → (p1 → True)) := by
          -- Implications on the right can always be decomposed.
          intro h23
          -- Implications on the right can always be decomposed.
          intro h24
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h11, we can now drive its conclusion.
        let h25 := h11 h22
        -- One of the premise coincides with the conclusion.
        exact h25
      case inr h26 =>
        -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
        have h27 : (False → (p1 → True)) := by
          -- Implications on the right can always be decomposed.
          intro h28
          -- Implications on the right can always be decomposed.
          intro h29
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h11, we can now drive its conclusion.
        let h30 := h11 h27
        -- One of the premise coincides with the conclusion.
        exact h30
  case inr h31 =>
    -- Disjunctions on the left can always be decomposed.
    cases h31
    case inl h32 =>
      -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
      have h33 : (False → (p1 → True)) := by
        -- Implications on the right can always be decomposed.
        intro h34
        -- Implications on the right can always be decomposed.
        intro h35
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h11, we can now drive its conclusion.
      let h36 := h11 h33
      -- One of the premise coincides with the conclusion.
      exact h36
    case inr h37 =>
      -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
      have h38 : (False → (p1 → True)) := by
        -- Implications on the right can always be decomposed.
        intro h39
        -- Implications on the right can always be decomposed.
        intro h40
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h11, we can now drive its conclusion.
      let h41 := h11 h38
      -- One of the premise coincides with the conclusion.
      exact h41



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40125060558171131576297054983 : (((((((True → False) → (p2 ∨ (p5 ∨ (((((p2 → False) ∨ p3) → p2) ∧ p4) ∨ p4)))) ∧ p5) ∨ ((p2 ∧ True) ∨ p2)) ∧ p2) ∨ True) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_85992002077384320506704948664 : (((((p1 ∧ p1) ∨ (p1 ∨ p1)) ∨ ((False → p5) ∨ False)) ∧ (((p3 → (p4 ∧ (p4 ∧ p2))) ∨ (p1 → (p4 ∨ (p1 ∨ p5)))) → False)) → p5) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h8 : ((p3 → (p4 ∧ (p4 ∧ p2))) ∨ (p1 → (p4 ∨ (p1 ∨ p5)))) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h9
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h9
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h10 := h3 h8
      -- False on the left can always be used.
      apply False.elim h10
    case inr h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
        have h13 : ((p3 → (p4 ∧ (p4 ∧ p2))) ∨ (p1 → (p4 ∨ (p1 ∨ p5)))) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h14
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h14
        -- We have shown the premise of h3, we can now drive its conclusion.
        let h15 := h3 h13
        -- False on the left can always be used.
        apply False.elim h15
      case inr h16 =>
        -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
        have h17 : ((p3 → (p4 ∧ (p4 ∧ p2))) ∨ (p1 → (p4 ∨ (p1 ∨ p5)))) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h18
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h18
        -- We have shown the premise of h3, we can now drive its conclusion.
        let h19 := h3 h17
        -- False on the left can always be used.
        apply False.elim h19
  case inr h20 =>
    -- Disjunctions on the left can always be decomposed.
    cases h20
    case inl h21 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h22 : ((p3 → (p4 ∧ (p4 ∧ p2))) ∨ (p1 → (p4 ∨ (p1 ∨ p5)))) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h23
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h23
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h24 := h3 h22
      -- False on the left can always be used.
      apply False.elim h24
    case inr h25 =>
      -- False on the left can always be used.
      apply False.elim h25



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_633655417547616859724440105960 : ((((((False → p3) → ((((True ∧ (p3 ∧ (((p5 → ((p2 ∧ p2) → True)) → p3) → True))) ∧ True) ∧ p2) → True)) ∨ (p4 ∨ p2)) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_606085414590587708377617821091 : ((((p5 → (p4 ∨ (p4 ∨ ((p5 → False) ∧ (((p1 ∨ p5) ∧ True) ∧ ((p5 ∧ (p1 ∧ (p5 → (False ∨ (p4 ∨ p2))))) → p5)))))) ∧ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_202694295224085284336302092059 : (((p2 ∨ (p2 ∧ p5)) → (False → p5)) ∧ (((False → p2) ∨ (p2 ∨ (True → p2))) ∧ (p3 ∨ ((p1 ∧ (p1 ∧ (p3 ∧ p1))) ∨ (p4 → True))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_261530508655889380906809395347 : ((p5 → p3) → ((p3 ∧ p4) ∨ ((((p2 → False) ∧ p5) ∨ ((p1 ∨ p5) → ((p2 ∧ False) → (p3 ∧ (p1 → p5))))) ∨ (p4 ∨ (p3 → True))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228269483247007308139105519959 : ((p5 ∧ (p4 → p3)) ∨ ((True ∧ (p4 ∧ (p2 ∧ False))) ∨ (p5 → (((p3 ∧ ((p1 ∨ (p1 → p3)) ∨ p2)) ∨ (p5 ∨ p3)) ∨ (p2 ∨ False))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115070754819145887428439761528 : ((((p1 → (p1 ∧ True)) → ((p4 ∨ ((p2 ∧ p3) ∨ False)) ∧ p1)) ∨ ((False → p3) ∧ ((p4 ∧ False) → (p4 ∨ (p1 ∨ p5))))) ∨ (p4 ∨ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2289961495842466288649998845 : (((False → p5) → (p5 ∨ (p4 ∨ (p1 → (((p5 ∨ p5) ∧ p4) ∨ p5))))) ∨ (False → ((((True ∧ p5) ∨ p5) → p3) ∨ (p5 → p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_807625097138060324694953340693 : (((p4 → (((p2 ∧ (p3 → p2)) ∨ p1) → (((p2 ∧ (p3 ∧ p1)) ∨ p5) ∨ (((p3 ∨ p2) ∨ p4) ∨ ((p2 → False) → (p1 ∨ p3)))))) ∨ False) ∧ True) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115313144050443089084337414957 : (((((p5 ∨ p5) → (p2 ∨ False)) ∧ ((False ∧ p3) → p2)) → (p2 ∧ (False ∧ ((p3 ∨ p5) ∧ ((p5 ∨ True) ∧ (False → p5)))))) ∨ (False ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310383984190139858595081771491 : (p2 ∨ ((((p2 → (False ∨ (p2 ∨ True))) ∧ p4) ∨ p5) ∨ (p3 ∨ (((True ∨ (True ∧ True)) ∧ ((p4 → (p1 → True)) ∨ (p5 ∨ p3))) ∨ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119118840342723638688093365986 : ((p1 → (True ∧ (True ∧ (((p2 ∧ p4) ∧ (p5 ∧ (((False → p1) ∧ (True ∨ True)) → (p3 ∧ (p2 ∧ p2))))) ∧ (False ∨ False))))) ∨ (p1 → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178025982422803749502011974288 : (((p3 → (((p4 ∨ p5) → (p3 ∧ (p5 ∧ (False ∨ p1)))) → p5)) ∨ True) ∨ (p2 ∨ ((False ∨ False) ∨ (p1 ∧ (False ∨ ((p2 → True) ∨ p1)))))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198271426836480804384399492524 : ((False ∧ ((True ∨ p1) ∧ ((p3 ∨ p5) ∨ True))) ∨ (p4 ∨ ((False ∨ (True ∨ (p2 ∨ (p3 ∧ ((p3 → p5) ∨ (False ∧ True)))))) ∨ (True ∨ True)))) := by
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
theorem thm_5_vars_167067859950791034023552280608 : ((((((p1 ∧ ((p1 ∧ (False ∨ p5)) → (p5 ∧ p1))) ∨ (p1 ∧ p5)) ∧ p4) → False) ∨ p1) → (((p5 ∨ p1) ∧ p1) → ((False ∧ p2) ∨ True))) := by
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
    cases h1
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
  case inr h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_140883473238163100276628038818 : (((True ∨ (p4 ∨ ((True ∧ ((p4 ∨ (p1 ∨ True)) ∨ p3)) ∧ False))) → ((True ∨ (False ∧ ((p5 → False) ∧ False))) ∧ p1)) → ((p4 ∧ p1) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (True ∨ (p4 ∨ ((True ∧ ((p4 ∨ (p1 ∨ True)) ∨ p3)) ∧ False))) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160007494851187585194299128795 : ((((False ∧ (True ∨ (False ∨ p2))) ∨ (p5 ∨ ((p4 ∨ ((p1 ∧ (p5 → p1)) → p2)) ∨ p5))) → p4) → ((True → (False ∧ p3)) → (p3 ∧ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- One of the premise coincides with the conclusion.
  exact h5
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h6 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h7 := h2 h6
  -- We need to get the left conjuct of h7 based on <expert-advice>.
  let h8 := h7.left
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113996213851148695524628732355 : (((p3 → ((p3 ∧ ((((p4 → (True ∧ p5)) → p1) → p1) ∨ (p5 ∧ p3))) → (p1 ∨ (p3 ∧ False)))) ∧ ((False ∧ p2) ∨ p1)) ∨ (True ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337072219761793084846872620101 : (p1 → (((True ∧ (((p4 ∧ p5) ∧ (p4 → p4)) ∧ ((p1 → ((p5 ∨ (p1 → (p2 ∨ p2))) ∧ p2)) ∧ p4))) ∨ (False ∨ False)) ∨ (p1 ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136256237528233844192422600411 : (((p4 → ((False → p2) → (False ∧ p1))) ∨ ((p3 ∨ ((p4 ∧ p2) ∧ (((p3 ∧ (False ∧ p2)) ∧ p1) ∧ p5))) ∧ p5)) ∨ (False → (p1 ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_265862595474504497814338547750 : (True ∧ (p5 ∨ (p4 ∨ ((((((p1 ∧ p1) → True) → False) ∧ p2) ∧ (False ∨ (False ∨ (((p5 ∧ p1) → (p5 → p1)) ∧ p5)))) ∨ (True → True))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_632960909876987796352704401869 : ((((((((p2 ∧ (True ∧ (True ∨ True))) → (((True → p4) → p4) ∧ p5)) → False) ∨ (False ∧ (False ∧ (True ∨ p2)))) ∧ (p5 ∧ p4)) → False) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h3.left
    let h6 := h3.right
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h7 : ((p2 ∧ (True ∧ (True ∨ True))) → (((True → p4) → p4) ∧ p5)) := by
      -- Implications on the right can always be decomposed.
      intro h8
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h9
      -- Conjunctions on the left can always be decomposed.
      let h10 := h8.left
      let h11 := h8.right
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h14 =>
        -- One of the premise coincides with the conclusion.
        exact h6
      case inr h15 =>
        -- One of the premise coincides with the conclusion.
        exact h6
      -- Conjunctions on the left can always be decomposed.
      let h16 := h8.left
      let h17 := h8.right
      -- Conjunctions on the left can always be decomposed.
      let h18 := h17.left
      let h19 := h17.right
      -- Disjunctions on the left can always be decomposed.
      cases h19
      case inl h20 =>
        -- One of the premise coincides with the conclusion.
        exact h5
      case inr h21 =>
        -- One of the premise coincides with the conclusion.
        exact h5
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h22 := h4 h7
    -- False on the left can always be used.
    apply False.elim h22
  case inr h23 =>
    -- Conjunctions on the left can always be decomposed.
    let h24 := h23.left
    let h25 := h23.right
    -- False on the left can always be used.
    apply False.elim h24
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184115669616698323993863649085 : ((((p4 ∧ p3) → (False ∧ ((p1 ∨ (p1 → True)) ∨ p5))) ∨ p5) ∨ (True → (p4 → (((p3 ∧ False) ∨ (((p1 → True) ∧ True) ∧ True)) ∨ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65706967054740040741809752032 : ((p4 ∨ (((p5 → False) ∨ ((p2 → p5) → ((p2 ∧ False) ∨ (((p4 ∨ p5) → (p2 ∧ p4)) → ((p2 ∧ p5) ∧ True))))) ∧ (p1 → p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323980289539062572736833752267 : (p5 ∨ ((((p4 → (False ∧ (p1 ∧ (True ∨ p3)))) → ((False ∨ True) ∧ False)) ∧ False) ∨ ((((p4 ∨ ((p2 → p4) ∧ p5)) → False) → p3) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340904667237493772513652074945 : (p2 → ((((False ∨ ((False ∨ p5) ∧ ((p1 ∨ p2) ∧ True))) ∨ p4) ∨ (p2 ∧ (False ∨ (p3 → ((p5 ∨ True) ∨ (p5 → (p4 ∧ p5))))))) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323916267231056894767917774542 : (p5 ∨ ((p5 → ((p1 ∧ p3) → ((p4 ∨ ((False ∧ (p2 ∨ p2)) ∨ p4)) ∨ (p4 ∨ False)))) ∨ (False → (p3 ∨ ((p5 ∧ (p2 → False)) ∧ p3))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_669826275620074887702089878281 : ((((((p1 ∨ ((p2 ∧ p4) ∧ ((p2 → p4) → p4))) ∨ (p4 → p4)) ∧ ((False → p2) ∨ (p2 ∧ (p3 ∨ True)))) ∨ ((p2 ∧ p5) → p2)) ∨ p4) ∧ True) := by
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
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160768804886545088815899381389 : ((((True → p2) ∧ (p5 → (p4 ∨ p4))) ∧ (((p4 ∨ (p1 → ((False → False) ∧ False))) → p4) → p1)) → ((p3 ∨ (p2 → False)) ∨ (p4 → p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h6
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h7 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h8 := h4 h7
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_684932954849350750774896700672 : ((((p2 ∧ ((((True → True) ∧ p3) ∧ (p3 ∨ (((p5 ∧ p4) → p5) ∧ (p2 → p1)))) ∧ p3)) ∨ (p2 ∧ ((p4 ∧ (True ∧ p3)) ∨ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_656480807412336953691470147994 : (((((((p4 ∨ p4) → (p2 ∧ (p1 ∧ (p1 ∨ p3)))) ∧ p2) → (p1 → (((p4 ∨ p5) ∧ True) → ((p4 ∧ False) ∨ p1)))) ∨ (p2 ∧ False)) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h1.left
    let h8 := h1.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h1.left
    let h11 := h1.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171417343302973324846476194003 : (((((p4 ∧ True) → p3) → (((True ∧ p2) ∨ (p3 ∧ p3)) ∧ (p3 ∧ p4))) ∧ p1) ∨ ((p2 ∨ p2) → (((p3 ∨ p4) ∨ (p1 → True)) ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44656943545148686057963546323 : ((((True ∧ (False ∨ ((p1 ∧ True) → p5))) ∨ ((p2 → ((p3 ∧ (p1 → True)) ∧ (((p1 → p3) ∨ False) ∨ p4))) ∧ (p4 → p4))) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117449251254723860801382863098 : ((p1 ∧ (((p5 ∧ p5) → (p4 → False)) → ((((True ∧ ((p5 ∧ (p5 ∧ p2)) ∨ False)) ∧ p3) → p1) → ((False → p4) → p4)))) ∨ (p1 → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198663068025753219766138788819 : ((p3 ∨ (p5 → (p4 ∧ ((p2 ∨ False) ∧ p3)))) ∨ ((p5 → (((((p3 ∨ False) ∨ (p1 → True)) → ((p4 ∧ False) ∨ p1)) ∧ p3) ∨ True)) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41334689197586781519815195811 : ((((((((p4 → False) ∨ (((p2 → p5) ∨ True) ∨ (p4 ∧ p3))) ∧ p2) → p2) → p5) ∨ (p5 → ((p3 ∨ p2) ∨ (p4 ∨ p5)))) ∨ p5) ∨ p4) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_694769822271635251847741456239 : ((((p5 ∨ (((((p2 → True) → p1) ∨ p3) ∨ p4) ∧ ((p3 → p4) ∧ p5))) ∨ ((p1 ∨ ((p1 ∧ ((False ∨ p5) → p4)) ∧ p2)) → p1)) ∨ p5) ∧ True) := by
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
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- One of the premise coincides with the conclusion.
    exact h6
  -- True on the right can always be proven directly.
  apply True.intro



