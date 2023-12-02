variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_629867723773185100075068618485 : ((((((((p3 → (True ∧ p4)) ∧ p5) → (True ∧ True)) ∧ (((((p3 ∨ (p4 ∨ p4)) → p5) ∧ (False ∧ False)) → p1) ∨ p3)) ∨ p1) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149342012045174448188334891686 : (((p1 ∨ p5) → ((((p3 ∨ (p4 ∨ True)) → p5) ∨ ((p4 → ((False → p3) ∨ True)) ∨ (p4 ∨ False))) → p5)) ∨ (True ∨ ((p1 → p2) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_562595413226950723816766293486 : (((p5 ∨ (((p5 → (p1 → (((p5 ∧ (p5 ∧ True)) ∨ ((p4 → p4) ∧ (p5 ∨ p4))) → p4))) ∨ (p3 ∨ p3)) ∨ ((p3 → True) ∨ p2))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191135524866812041507408125436 : ((((p2 ∨ p4) ∧ p3) ∨ (((True → p4) → p1) → p2)) ∨ (((p2 ∧ p1) ∨ ((p5 → p1) ∨ True)) ∨ ((True → True) → (False → (p4 ∨ True))))) := by
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
theorem thm_5_vars_48109628959917260951948696134 : ((((p5 → ((False ∨ p5) → p4)) ∨ ((((((p5 ∧ p2) ∧ p3) ∨ ((p5 ∧ p1) ∨ p4)) ∨ (p3 ∨ p1)) ∨ p5) ∧ p2)) → (p1 ∨ True)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Disjunctions on the left can always be decomposed.
        cases h7
        case inl h8 =>
          -- Conjunctions on the left can always be decomposed.
          let h9 := h8.left
          let h10 := h8.right
          -- Conjunctions on the left can always be decomposed.
          let h11 := h9.left
          let h12 := h9.right
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
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h16
          case inr h17 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
      case inr h18 =>
        -- Disjunctions on the left can always be decomposed.
        cases h18
        case inl h19 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h20 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h20
    case inr h21 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_430004304586509305538286330111 : ((((((((True ∨ p5) ∨ (p5 ∨ p3)) ∧ p3) → p4) ∧ (((True → ((p3 ∨ p5) ∧ (p2 ∧ True))) ∨ p3) ∧ (p5 ∨ p3))) ∨ (p4 → p4)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323800211522700431055314869483 : (p5 ∨ (((False ∧ p4) ∧ ((p1 → False) ∨ ((False → (False ∧ p4)) → (((p4 ∨ p1) ∧ p4) → p4)))) ∨ (True ∧ (((p2 ∨ True) ∧ p4) ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134787478694656747826983679294 : (((p2 ∧ ((((False ∨ p1) → False) → (p5 ∨ ((p1 → ((True ∨ p1) ∨ False)) ∨ ((True ∨ p1) ∧ p5)))) ∨ p4)) → p4) ∨ ((True ∨ p1) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56994870504332591047070417312 : (((p5 ∨ (p1 → p2)) ∧ ((((p4 → (p2 → p5)) ∧ (((((p3 → p5) ∧ True) → p1) ∧ p2) → ((p4 ∧ False) ∨ p2))) → True) → p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111971025790777764950037353451 : ((((p5 ∧ ((False ∧ (True ∧ p2)) ∧ p1)) ∧ ((p3 ∨ ((((p5 ∧ (p5 ∨ p4)) → (p2 ∨ p1)) ∨ p1) ∧ False)) → p4)) ∨ p5) ∨ (p5 → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184594336668083042021671768537 : (((p2 → (((p1 ∨ (p3 ∧ True)) ∨ p1) ∨ p4)) → (False ∧ p3)) ∨ (((p3 ∧ ((p2 → False) → (p1 → (False ∧ (False ∨ False))))) ∨ True) ∧ True)) := by
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
theorem thm_5_vars_254349940622953221121380004928 : ((p2 ∧ p4) → ((p1 ∨ (p4 ∧ ((p5 ∨ (((False ∨ False) ∨ p3) ∨ (False ∧ True))) ∨ (True ∨ p1)))) ∧ ((p3 ∨ ((p1 → p1) ∧ True)) ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h6
  -- One of the premise coincides with the conclusion.
  exact h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166132401808145751402233718800 : ((True ∧ ((p3 ∨ (p2 → False)) ∧ (((p4 ∧ ((True → p2) ∨ p2)) ∧ (p3 ∧ p3)) ∧ True))) ∨ (((((p2 ∧ p2) ∧ p4) ∧ p3) ∨ False) → p2)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h3.left
    let h6 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- False on the left can always be used.
    apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204373122614527475547445398317 : (((p4 ∨ ((p3 ∨ p4) ∧ p1)) ∧ p5) ∨ (((((p2 ∧ True) ∧ (((p2 ∨ p2) ∧ True) → p2)) ∨ (True → (False → p4))) ∧ (p4 → True)) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_950337673465702482755100392212 : (((((p3 → p4) → p4) ∧ ((True → False) ∧ (p4 → ((True → ((((p4 ∧ (p1 → p1)) ∧ False) ∨ True) ∧ (p1 ∨ (p1 → p5)))) → True)))) → p4) ∧ True) := by
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
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h6 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h7 := h4 h6
  -- False on the left can always be used.
  apply False.elim h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_918656821524362376306003477982 : (((((p2 → ((p2 → (p4 ∧ (p4 ∨ ((p4 → p2) → p3)))) ∧ p5)) ∧ p3) ∧ (((p4 ∨ (((True ∨ p2) ∧ p3) ∨ p5)) ∧ p5) ∨ p5)) → p3) ∧ True) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h9 =>
      -- One of the premise coincides with the conclusion.
      exact h5
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
          -- One of the premise coincides with the conclusion.
          exact h13
        case inr h15 =>
          -- One of the premise coincides with the conclusion.
          exact h13
      case inr h16 =>
        -- One of the premise coincides with the conclusion.
        exact h5
  case inr h17 =>
    -- One of the premise coincides with the conclusion.
    exact h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54423260995373750373074664876 : (((((((False ∨ p5) → p1) → p4) → p3) ∨ p1) ∨ (((((p5 ∨ True) → p3) ∧ ((p3 ∨ p3) → (p2 → p1))) → (p4 → p2)) ∨ True)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_243814137786918133189011655828 : ((p5 → p5) ∧ (p2 → ((((p4 ∨ p3) → (((False ∧ False) → (((p2 → p1) ∨ False) ∨ False)) → ((p4 → p1) → p3))) ∨ p5) ∨ (p1 ∨ p2)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184639555016938459878040655635 : (((p1 → ((p4 ∧ p5) ∨ (p4 ∨ p4))) ∧ (False ∧ (True ∧ p5))) ∨ (((True ∨ p3) ∨ (True ∨ ((p2 → p5) ∧ (p2 ∨ (True ∧ True))))) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167972056586843026094133221306 : (((p4 → ((p1 → p4) → (p4 ∨ (p1 → p2)))) → ((((p3 ∨ p5) ∨ p2) → True) ∧ False)) → ((((True → (False ∨ p3)) ∨ p4) ∨ True) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_634494887593772802086232454838 : (((((((p2 ∨ (p4 ∧ (p3 ∧ p1))) ∧ ((p1 → False) ∨ p5)) ∨ ((p3 → False) → ((True ∧ False) ∧ p4))) ∧ ((False → p3) → p2)) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_125046511944698156738686452971 : ((((p3 → p1) → p5) ∧ ((True ∨ (True → p1)) ∧ (True ∧ (((p3 ∧ p1) → (((p1 ∨ (p5 ∨ p5)) ∧ False) → True)) ∨ p5)))) → (p1 → p5)) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h6.left
    let h9 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h11 : (p3 → p1) := by
        -- Implications on the right can always be decomposed.
        intro h12
        -- One of the premise coincides with the conclusion.
        exact h2
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h13 := h3 h11
      -- One of the premise coincides with the conclusion.
      exact h13
    case inr h14 =>
      -- One of the premise coincides with the conclusion.
      exact h14
  case inr h15 =>
    -- Conjunctions on the left can always be decomposed.
    let h16 := h6.left
    let h17 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h17
    case inl h18 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h19 : (p3 → p1) := by
        -- Implications on the right can always be decomposed.
        intro h20
        -- One of the premise coincides with the conclusion.
        exact h2
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h21 := h3 h19
      -- One of the premise coincides with the conclusion.
      exact h21
    case inr h22 =>
      -- One of the premise coincides with the conclusion.
      exact h22



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_608352030133491108965991047662 : (((((((p1 → p1) → ((((p2 ∨ False) → (p3 ∨ (p4 → (False ∨ True)))) → p1) → (p2 → (p1 ∨ (p1 ∧ True))))) ∨ p3) ∨ False) ∨ True) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_91036429321287687366303505913 : (((p2 → False) ∧ ((((True → p3) ∧ ((p5 ∨ ((False ∨ ((p2 → p2) → p1)) ∧ p1)) ∧ (p4 → (p1 → (p1 ∨ p5))))) → True) ∧ p2)) → False) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h6 : p2 := by
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h7 := h2 h6
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314034269654428289651119452703 : (p3 ∨ ((p4 → (((True ∨ (((False ∨ p4) ∨ (False ∧ p4)) → p2)) ∨ False) → (((p1 ∧ p4) → p4) → (p3 ∧ (p2 ∨ True))))) ∨ (p4 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299155326742422355639105226716 : (False ∨ (((p4 ∨ (((True → (p3 → False)) → ((p4 ∨ (p1 ∧ (((p1 ∧ p1) ∧ False) → p4))) → p4)) → ((p1 ∨ True) ∧ p1))) ∨ False) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232869607650527688784984285150 : ((p2 ∧ (p3 → p4)) → ((((True ∧ (p1 ∧ ((p4 → (p2 ∨ (False ∨ p4))) → (p5 ∨ (p1 ∨ ((p4 ∧ p5) → p3)))))) ∨ p5) ∧ p5) ∨ p2)) := by
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
theorem thm_5_vars_14875772616683500203921920261 : (((((((p1 ∧ p3) ∨ (p3 → p3)) → p1) ∨ p2) → ((p1 ∨ (p1 ∨ ((p5 → p5) ∧ p2))) → (p5 → (p2 ∧ p4)))) ∨ (p5 ∨ True)) ∧ True) := by
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
theorem thm_5_vars_818568059500936199018839991331 : (((((p4 ∧ ((p2 → (((p1 ∧ p1) ∨ p4) → p1)) ∧ (((p3 ∨ (True ∧ (p1 ∨ p2))) ∨ True) ∧ (p1 ∨ p2)))) ∨ (False ∨ False)) ∧ p2) → p1) ∧ True) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
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
        cases h10
        case inl h13 =>
          -- One of the premise coincides with the conclusion.
          exact h13
        case inr h14 =>
          -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
          have h15 : p2 := by
            -- One of the premise coincides with the conclusion.
            exact h3
          -- We have shown the premise of h7, we can now drive its conclusion.
          let h16 := h7 h15
          -- We want to use the implication h16 based on <expert-advice>. So we show its premise.
          have h17 : ((p1 ∧ p1) ∨ p4) := by
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h5
          -- We have shown the premise of h16, we can now drive its conclusion.
          let h18 := h16 h17
          -- One of the premise coincides with the conclusion.
          exact h18
      case inr h19 =>
        -- Conjunctions on the left can always be decomposed.
        let h20 := h19.left
        let h21 := h19.right
        -- Disjunctions on the left can always be decomposed.
        cases h21
        case inl h22 =>
          -- Disjunctions on the left can always be decomposed.
          cases h10
          case inl h23 =>
            -- One of the premise coincides with the conclusion.
            exact h23
          case inr h24 =>
            -- One of the premise coincides with the conclusion.
            exact h22
        case inr h25 =>
          -- Disjunctions on the left can always be decomposed.
          cases h10
          case inl h26 =>
            -- One of the premise coincides with the conclusion.
            exact h26
          case inr h27 =>
            -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
            have h28 : p2 := by
              -- One of the premise coincides with the conclusion.
              exact h3
            -- We have shown the premise of h7, we can now drive its conclusion.
            let h29 := h7 h28
            -- We want to use the implication h29 based on <expert-advice>. So we show its premise.
            have h30 : ((p1 ∧ p1) ∨ p4) := by
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- One of the premise coincides with the conclusion.
              exact h5
            -- We have shown the premise of h29, we can now drive its conclusion.
            let h31 := h29 h30
            -- One of the premise coincides with the conclusion.
            exact h31
    case inr h32 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h33 =>
        -- One of the premise coincides with the conclusion.
        exact h33
      case inr h34 =>
        -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
        have h35 : p2 := by
          -- One of the premise coincides with the conclusion.
          exact h3
        -- We have shown the premise of h7, we can now drive its conclusion.
        let h36 := h7 h35
        -- We want to use the implication h36 based on <expert-advice>. So we show its premise.
        have h37 : ((p1 ∧ p1) ∨ p4) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h5
        -- We have shown the premise of h36, we can now drive its conclusion.
        let h38 := h36 h37
        -- One of the premise coincides with the conclusion.
        exact h38
  case inr h39 =>
    -- Disjunctions on the left can always be decomposed.
    cases h39
    case inl h40 =>
      -- False on the left can always be used.
      apply False.elim h40
    case inr h41 =>
      -- False on the left can always be used.
      apply False.elim h41
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160493820370259481731439061175 : ((((p2 ∧ (p2 → (p3 ∧ ((p1 ∧ p5) → (p2 ∧ p1))))) → p5) ∧ (p2 ∨ (p3 ∧ (False → p2)))) → ((p1 → p2) ∨ ((p4 ∨ p5) → p3))) := by
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
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h11 =>
      -- One of the premise coincides with the conclusion.
      exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_781744588798273141765374750211 : (((p2 ∨ (p5 ∨ ((p1 ∧ (p5 ∨ ((p3 → (p1 → p3)) ∧ (p2 ∧ (((False ∨ p5) → p3) ∨ (p3 ∧ (p2 → (p5 → p1)))))))) ∧ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_22929346664879468558176631794 : (((p2 ∧ ((p3 → True) ∧ (p2 ∨ False))) ∨ ((p3 ∨ (True → ((True → ((p1 → ((False → p5) → (p1 → p5))) → True)) ∧ False))) → p3)) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h4 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h5 := h3 h4
    -- We need to get the right conjuct of h5 based on <expert-advice>.
    let h6 := h5.right
    -- False on the left can always be used.
    apply False.elim h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199579093432949918163333825709 : ((((p2 ∨ (True ∨ (p1 ∨ p2))) ∨ p4) → p4) → (((p4 ∧ (p3 → (True ∨ p2))) ∨ p5) ∨ (((True ∧ True) → ((p4 ∧ p5) → False)) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192118385404016105232774666164 : ((p5 → ((p1 ∨ (p2 ∨ ((p4 → p5) → p4))) ∧ p5)) ∨ (p5 → (((p5 ∨ False) ∨ True) ∨ (False ∧ (((False ∨ (p4 → p4)) ∨ True) → p3))))) := by
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
theorem thm_5_vars_311788502105236565452924694630 : (p2 ∨ (False ∨ (p3 ∨ ((True → (((((((((p1 ∨ (p1 ∧ True)) ∧ p3) ∨ p1) ∧ p3) ∧ p4) ∨ True) ∧ p1) ∧ (p5 ∧ p1)) ∨ True)) ∨ p4)))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115236307506880007006859166151 : ((((((False ∨ False) → ((True ∧ p5) ∧ p1)) ∧ True) → p3) ∨ (True → ((((True ∧ p5) ∧ True) ∧ (False ∧ (True ∧ p3))) → p2))) ∨ (False ∨ p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- Conjunctions on the left can always be decomposed.
  let h9 := h4.left
  let h10 := h4.right
  -- False on the left can always be used.
  apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184749587953863527432321610796 : ((((p4 ∨ p3) ∧ (p5 ∨ p3)) ∧ (((p3 ∧ p3) ∧ False) ∨ p5)) ∨ (((True ∨ p4) ∨ (True ∨ ((((p1 → p2) ∧ p2) ∧ p1) ∧ False))) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_668543130829021644612305196853 : (((((((p4 → p5) ∧ (False ∧ p5)) ∧ ((p5 ∧ ((p5 ∨ True) ∧ True)) ∨ (((p5 ∨ p4) → p5) → p5))) ∧ p2) ∨ ((p1 ∧ False) ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136856320522110512591240217379 : (((p4 ∧ p5) ∨ ((p3 ∨ p1) ∨ (((p1 ∨ True) ∨ p2) ∨ (False ∨ ((p2 ∧ ((p3 ∨ p2) → (False ∨ False))) ∧ True))))) ∨ ((p2 ∨ p3) → False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337372317662667415241869308693 : (p1 → ((((p2 ∧ ((p4 ∧ p2) → False)) ∨ p1) → (p5 → (((p4 ∧ ((p5 ∨ True) ∧ p4)) ∧ (p3 ∨ p5)) ∨ p4))) ∨ ((p3 ∧ False) → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167043817389874090868143073864 : ((((p2 → (p5 → (((p3 → (p4 → True)) → (p5 → p4)) ∨ (p1 ∧ p3)))) ∧ p3) ∨ p3) → (((True → p5) → (True ∧ False)) ∨ (p3 → p3))) := by
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
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249628052301904007439624702590 : ((p5 ∨ p3) ∨ ((p4 ∨ False) ∨ (p1 ∨ ((p1 → ((p2 ∧ False) → (True → (p2 ∧ ((p5 ∨ ((False → (p1 → p5)) ∧ False)) ∨ p4))))) → True)))) := by
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
theorem thm_5_vars_342751733390215404988938008165 : (p2 → (((True → (True ∧ ((p2 ∧ p3) → p1))) → p3) ∨ (((((p5 ∧ ((p5 → (False ∨ (True ∨ p4))) ∧ p4)) ∨ p3) → p4) ∨ p2) ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179438154194432909765535716105 : ((p4 ∨ (p5 → ((p3 ∧ p5) ∨ ((p5 → ((p3 ∧ p1) ∧ p1)) ∧ False)))) ∨ ((p4 ∧ p5) → ((((False ∧ p1) ∧ p2) ∧ p4) ∨ (p3 ∨ p4)))) := by
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
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_21447529725541845010393863065 : ((((p1 → (((p4 ∨ p5) → (p5 ∨ p3)) ∧ p3)) → p4) ∨ ((((True ∧ (True ∨ (p2 ∨ (p2 ∧ True)))) ∨ True) ∧ p1) → (p2 ∨ True))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h9
      case inr h10 =>
        -- Conjunctions on the left can always be decomposed.
        let h11 := h10.left
        let h12 := h10.right
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h11
  case inr h13 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351212308756806250254993445436 : (p4 → (((((p2 → ((p3 ∧ p5) ∧ ((p4 ∧ ((p2 ∧ False) ∧ False)) ∧ True))) → ((False ∧ p1) ∧ p5)) ∨ p2) ∨ p3) ∨ ((p2 ∨ p2) → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_104600272296586740934351872617 : (((((False ∧ ((p3 → p3) → (True ∨ p4))) → p1) → ((((p4 ∨ p5) → p2) ∧ (p5 ∧ (p3 ∧ p2))) ∨ p2)) ∨ (True ∨ False)) ∧ (False → p3)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49323630871457631201577632619 : (((p4 ∨ (((p2 ∨ ((p5 → p4) → p4)) ∨ ((True → False) → ((p4 ∨ (p1 ∧ (p3 ∨ p1))) ∧ True))) ∨ p4)) ∨ (False ∧ (p2 ∨ p2))) ∨ p1) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60775141418875426587367687672 : ((True ∧ ((p4 → p1) ∨ ((p1 → p3) ∨ (p1 → (p2 → ((((p4 ∧ p2) → ((p2 ∨ (p1 → (p2 ∧ False))) ∧ p4)) → p5) ∧ p5)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65414110462406669400329004735 : ((p3 ∨ (((p3 ∨ p5) → p2) ∧ (((((p5 ∧ (((p2 ∧ False) → p2) ∧ (p5 ∨ True))) ∨ p4) ∧ (p4 ∧ (p5 → True))) ∨ p5) → p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310016546779409252810731454894 : (p2 ∨ ((((p4 ∧ ((False ∨ p4) ∨ p2)) → (p3 ∧ (((p3 ∧ p3) ∧ False) ∨ p5))) ∧ p5) ∨ ((True → ((p3 → p3) ∨ (p2 → p1))) ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_788683785824303755588560776502 : (((p5 ∨ ((((p5 ∧ p2) ∨ (p2 → (p2 ∧ (p2 ∨ ((p4 → (p5 ∨ False)) ∧ p1))))) ∨ ((((p5 → p2) ∨ p1) → p1) ∨ p2)) → p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112014075350506045990238483350 : ((((p1 → (p1 ∨ (p4 ∧ True))) → (p5 ∧ (((p2 ∧ p3) ∨ ((((p3 ∨ p5) ∨ True) ∧ (p3 → p1)) ∧ p1)) ∧ True))) ∨ p5) ∨ (True ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55872262404698019898026118696 : (((True ∨ ((p5 → p3) ∨ p1)) ∧ (((p5 → (((p4 ∨ ((p5 → p1) ∧ False)) ∨ (p3 → False)) ∨ False)) → (p3 ∨ p1)) ∨ (p2 → False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_36328725580584239801995138394 : ((p4 → ((((p4 ∧ p3) → ((False ∨ ((((True → False) → p5) ∧ (True → p3)) → p5)) → (p2 ∨ True))) → (p4 → p5)) ∨ (p4 ∧ p4))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137067051913027511414477701745 : (((p3 → p4) → ((p5 ∧ (p1 → (p3 ∧ (p5 ∨ ((p5 → p3) ∧ True))))) ∨ (((p2 ∨ (True ∨ p1)) → p4) → p5))) ∨ ((p4 → p4) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37085937460543690139849574027 : ((((((((True ∧ p1) → p1) ∧ True) ∧ (((p5 → (((p1 ∨ p2) → p3) ∨ (p2 ∨ p4))) ∨ p4) ∨ (p3 ∧ p5))) ∨ p5) ∧ p2) ∧ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303188438713662739239676617402 : (False ∨ (p4 → ((((((False ∧ p1) ∧ (p5 ∧ False)) ∧ p3) ∨ p4) ∨ p4) ∨ ((p2 → False) → (((p2 ∨ (False → (p2 → p1))) ∧ p5) ∧ p3))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48557337847169978852830505575 : ((((((False ∧ ((p4 → p1) ∨ False)) ∨ ((p5 ∧ True) ∨ (p5 → (False ∨ p4)))) ∨ ((p1 ∧ p5) → True)) → p2) ∧ (p1 ∨ (p3 ∨ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137939081103878682076996675475 : ((p4 ∨ (p4 → ((((((False ∨ p3) ∨ (False ∧ ((p3 ∧ p3) ∧ False))) ∨ p4) → p4) ∧ p3) ∧ ((p3 ∧ p3) ∨ p2)))) ∨ ((p4 ∨ True) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38902249734511323256038518249 : ((((p2 ∧ (p3 → p2)) ∨ (((True ∨ (((p3 ∨ p2) ∧ p4) → p2)) → (p3 ∧ ((True → p2) ∨ p2))) ∨ ((p1 ∨ p1) → True))) ∧ True) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308530613608628949606392108667 : (p2 ∨ (((p2 → (p2 ∧ ((True → ((False → p5) → p3)) → (p2 → (p1 ∧ p5))))) → (((p1 ∨ p2) ∧ (p3 ∧ False)) ∨ (p3 → p3))) ∨ False)) := by
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
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_648061944012821230731049154440 : (((((((p3 ∨ (p3 ∨ (False → True))) → p2) ∧ (p1 → ((p2 → ((p5 ∨ ((p3 ∧ p2) → p3)) ∧ False)) ∨ p4))) ∧ p2) ∧ (p5 → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114777991537066693713483457413 : (((((p2 → ((p1 ∧ (p4 ∨ False)) ∧ (True ∨ (False ∧ p5)))) ∨ p4) ∨ True) ∧ (((False ∧ (p2 ∨ (False ∧ False))) ∨ p4) ∨ p3)) ∨ (False → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147917730195654155490361769603 : (((((((False ∨ p4) ∨ p3) ∨ (p2 → p5)) → ((True ∨ p3) ∧ p3)) ∧ (p4 ∧ (p4 ∧ p3))) ∧ (p4 ∧ p4)) ∨ ((p1 → p1) ∨ (p5 ∧ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56335380148099502544117016133 : (((((True ∧ True) ∨ p5) ∨ False) → ((p1 ∨ (p5 → p1)) → (p2 → ((((p3 ∨ (p3 ∧ (False → p4))) → p4) ∨ p2) ∧ (False → False))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345665877166020237325217498889 : (p3 → ((False ∨ ((((p5 → (p3 ∨ p2)) ∧ ((((p5 ∧ p1) ∨ (p2 ∧ p2)) → True) → False)) ∨ p5) ∧ ((p5 → p5) ∧ (p3 ∨ p4)))) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60444360688040744352207647356 : (((p5 → True) → ((p3 → p1) ∧ (p5 ∨ ((p5 ∧ ((((False → (p1 ∨ False)) → True) ∧ (p1 → p5)) ∨ p5)) ∧ ((False ∨ p5) ∨ p3))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119476247826511413262357131213 : ((p4 → (p1 ∧ (True ∧ ((True → ((p4 ∧ ((True ∨ p1) → p1)) ∨ (((p2 → p5) ∧ False) ∨ p5))) ∨ (p2 ∧ (False ∧ p2)))))) ∨ (p3 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_625884996622974577251355750857 : ((((p2 → (((True → (p2 → False)) ∨ (((((p1 ∨ p1) ∧ False) ∧ p4) ∧ p4) ∨ (((p1 ∧ p2) ∨ (False ∧ p3)) ∨ p2))) ∨ p1)) ∨ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_262606811836903107087178518746 : (True ∧ (((((True ∨ True) → (True ∧ (p4 ∨ ((p5 → p3) → (((p1 ∧ ((p4 → (False ∧ p5)) ∨ p3)) ∧ p4) ∧ p3))))) ∨ True) → p3) → p3)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((True ∨ True) → (True ∧ (p4 ∨ ((p5 → p3) → (((p1 ∧ ((p4 → (False ∧ p5)) ∨ p3)) ∧ p4) ∧ p3))))) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231077704762226876961851699671 : (((False ∨ False) ∨ True) → ((True → (p1 ∨ ((p2 → (p4 ∨ (True → (p1 → ((p1 → p5) → p4))))) ∨ p3))) ∨ (p2 → ((p4 ∧ False) → p2)))) := by
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
      -- False on the left can always be used.
      apply False.elim h4
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- Implications on the right can always be decomposed.
    intro h7
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- False on the left can always be used.
    apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_139310601535952886864592744872 : (((True ∨ ((True ∧ ((p1 ∧ (p2 → p3)) ∧ (p2 → (p3 ∨ (True ∧ (False → False)))))) ∨ (p2 → (p1 ∧ p2)))) ∨ p3) → ((p4 ∨ p4) ∨ True)) := by
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
        -- Conjunctions on the left can always be decomposed.
        let h6 := h5.left
        let h7 := h5.right
        -- Conjunctions on the left can always be decomposed.
        let h8 := h7.left
        let h9 := h7.right
        -- Conjunctions on the left can always be decomposed.
        let h10 := h8.left
        let h11 := h8.right
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354929567390913807537546269030 : (p5 → ((p3 ∨ ((True → (p3 → ((True ∧ (p4 → p4)) ∨ p1))) → (((((True ∧ False) → p5) ∨ (p4 ∨ True)) → (p1 → p4)) → False))) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136080580477306401527320686127 : (((p1 ∨ ((p1 ∧ ((True → p5) ∨ p5)) → False)) ∧ ((p2 ∧ ((p3 ∨ (p1 ∧ p4)) ∧ (p5 → (p1 ∨ p4)))) ∨ p3)) ∨ (p1 → (False → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_688835849554349849164834579670 : ((((((p5 ∧ ((True ∨ True) → ((((p1 ∨ True) ∧ p1) ∨ p1) ∧ p2))) ∨ p3) ∧ p3) ∨ (True ∨ ((p3 → (True → p5)) ∨ (True ∨ True)))) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_430294104944983495926920012978 : ((((((True ∧ (p1 ∧ p5)) ∧ False) ∧ (p5 → (((True → ((p2 ∧ (True → p2)) ∧ p5)) ∧ (p1 ∨ False)) ∨ (False ∨ p2)))) ∨ (True ∨ p5)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_809954474640739616650062385386 : (((p5 → (((((p4 ∧ (False ∧ True)) → p1) → ((p2 ∧ ((True ∧ (False → p4)) ∨ p4)) ∧ False)) ∨ (True ∧ p1)) ∨ ((False ∧ p1) → p2))) ∨ p4) ∧ True) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_618211199031081607550303559841 : ((((((p5 ∨ (False ∨ p1)) ∧ p4) ∨ (p3 ∨ (((p3 → True) ∧ (p4 → p1)) → ((((p2 ∧ p1) ∧ (p2 ∨ p4)) ∨ p1) → p1)))) ∨ p3) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h1.left
      let h10 := h1.right
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h1.left
      let h13 := h1.right
      -- One of the premise coincides with the conclusion.
      exact h7
  case inr h14 =>
    -- Conjunctions on the left can always be decomposed.
    let h15 := h1.left
    let h16 := h1.right
    -- One of the premise coincides with the conclusion.
    exact h14
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136251400410752847941420960254 : (((p5 ∨ (((p4 → False) → p4) ∨ p2)) ∨ ((True → (((p2 ∧ p3) → (p4 ∨ p2)) ∧ True)) ∧ ((p3 → p4) ∨ True))) ∨ (p2 → (p4 ∧ False))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257976741970689068260785720414 : ((p4 ∨ p1) → (((True → False) → ((False ∨ p4) ∨ (False ∨ ((((p1 ∧ p5) ∨ ((p4 ∨ (p2 ∧ p3)) ∧ (p4 ∧ p3))) ∧ False) ∨ p3)))) ∨ True)) := by
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
theorem thm_5_vars_234405415868492952003917840386 : ((p1 → (p3 → p4)) → (p3 → (((p4 ∧ True) → (p4 → (((False → (p2 → p1)) ∨ ((p3 ∨ (p3 ∨ p1)) → (True → p5))) → p2))) ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178930803249207965352479371584 : (((p5 → p3) ∧ ((p5 ∨ (True → ((p3 ∧ (p1 ∨ p1)) ∧ p2))) ∨ p3)) ∨ (((p2 ∨ ((p4 ∨ p1) ∨ (p1 ∨ True))) ∨ (p3 ∨ p1)) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166403858666700461676386553561 : ((False ∨ (p1 → (p3 ∧ ((p2 ∨ (((p3 ∨ p2) → (p5 ∧ p2)) ∧ True)) ∨ (True → p2))))) ∨ (p4 ∨ (p3 → ((p4 ∨ (p2 ∨ False)) ∨ True)))) := by
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
theorem thm_5_vars_64056914249931709814220444363 : ((False ∨ ((((((p1 ∧ True) ∨ p2) → (p4 ∧ True)) ∨ ((True ∧ p1) ∧ False)) ∨ (p1 → (p3 ∧ False))) ∨ (p5 ∨ (True ∨ (p2 → False))))) ∨ p4) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_797022607650601797936025615298 : (((p1 → (((((((((p3 → p2) → p5) ∨ p5) → (False ∨ p1)) ∨ p3) ∧ (False ∧ p2)) ∧ ((p3 ∨ p4) ∨ p5)) ∨ (p1 ∨ p2)) ∧ p1)) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257978149886919274573850458957 : ((p4 ∨ p1) → ((p3 → (((p5 ∧ ((p3 → False) ∨ (False → (False ∧ True)))) ∨ ((p5 ∨ ((True ∧ p4) ∧ (p4 ∧ p3))) ∨ p4)) ∨ False)) ∨ True)) := by
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
theorem thm_5_vars_692306011242572062988776442458 : ((((((((True ∨ p4) ∨ p1) ∨ (p2 ∧ (True ∨ (p1 ∨ True)))) ∨ p3) → p1) ∧ (((p1 ∨ (p1 → False)) ∧ ((False ∧ p4) ∨ p2)) → p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207420230736991907745023392216 : (((True ∨ (p2 ∨ (False ∧ p3))) ∨ p4) → (((True → p3) ∨ ((p3 ∧ ((((p5 ∨ (p3 → False)) ∧ p1) ∧ p1) ∨ p5)) ∧ p2)) ∨ (False → p2))) := by
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
      -- False on the left can always be used.
      apply False.elim h4
    case inr h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h7
        -- False on the left can always be used.
        apply False.elim h7
      case inr h8 =>
        -- Conjunctions on the left can always be decomposed.
        let h9 := h8.left
        let h10 := h8.right
        -- False on the left can always be used.
        apply False.elim h9
  case inr h11 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h12
    -- False on the left can always be used.
    apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48218900044362972191500141195 : ((((p3 → p2) → (((p2 ∨ (p3 → p4)) ∧ ((p3 ∨ (((p1 ∨ True) → p5) ∧ p3)) → (p2 ∨ (True → p4)))) → False)) → (p4 ∧ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_729817193810831284446457420629 : (((((True ∧ p2) → p1) → (p4 ∨ (((p3 → (p1 ∨ p2)) → ((((False ∨ (p4 → (p3 ∧ True))) ∨ False) ∨ p1) → False)) → (p3 → p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47182920975573288331592436573 : ((((p2 → ((((p3 → p5) ∨ (p5 ∨ (p5 ∧ p2))) ∧ (p5 ∧ p4)) ∧ True)) → ((p5 → (p1 → p4)) ∨ (p3 ∨ True))) ∨ (p5 ∨ p1)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_149900380017572382185578457915 : ((p2 ∨ (p5 ∨ (((p3 → (True ∨ p3)) → (p4 ∧ ((p5 → p3) ∧ (False ∧ ((p1 ∨ p1) → True))))) ∨ p5))) ∨ ((p1 ∧ False) → (p3 ∧ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186485841544204186293185815712 : ((((True ∨ True) ∨ ((p4 ∨ (p4 → p2)) → p4)) ∧ (p2 ∧ p3)) → (((True → ((True → (((p2 ∧ p2) ∨ True) → p3)) ∧ False)) ∨ p3) ∨ p3)) := by
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
      let h6 := h3.left
      let h7 := h3.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h3.left
      let h10 := h3.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h10
  case inr h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h3.left
    let h13 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305005363718955508082448251979 : (p1 ∨ (((True → ((((p5 → (False → False)) ∧ p5) ∨ (p4 → p1)) → p5)) ∨ ((p1 ∨ p5) ∧ (False ∨ (p3 ∧ p3)))) ∨ (False → (p4 ∨ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232523801804334130281782606423 : ((True ∧ (p5 → False)) → (((p3 ∨ p4) ∨ p5) ∨ (((p2 → p5) ∨ ((p5 ∨ False) → (((True → (True ∧ (p2 → p5))) → True) → True))) ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134601215056577656803593538779 : ((((p4 ∧ ((p3 ∧ ((p2 ∧ ((p2 ∨ p4) ∨ p3)) → ((False ∨ p5) → (p3 ∨ p5)))) ∧ False)) → (p1 ∨ p2)) → p1) ∨ (True ∨ (False ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345363869230179105989640424599 : (p3 → ((((False ∨ ((((True ∧ p2) ∨ ((True ∨ p3) → p4)) ∧ (p2 ∧ p2)) → ((True ∧ False) ∨ (p5 → False)))) ∨ (False ∨ p2)) ∨ True) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65415190328009256967533134267 : ((p3 ∨ ((p3 ∧ (p4 ∧ p1)) ∧ (((p5 ∧ (False ∨ (p2 ∨ p3))) → (p1 ∨ (True → p3))) ∧ ((False ∨ ((p1 ∧ p1) ∨ True)) ∧ p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165170115943308443861622704241 : (((False ∧ ((p1 → (False ∨ ((p3 ∨ p2) ∧ ((p3 ∨ p1) → p3)))) ∨ True)) ∧ (p1 ∧ p2)) ∨ ((p2 ∨ ((True ∨ p2) ∨ p3)) ∨ (False ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



