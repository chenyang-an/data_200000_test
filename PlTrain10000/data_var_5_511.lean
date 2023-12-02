variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_807309213890215508515292552681 : (((p4 → (((((False ∧ p5) → ((p4 ∧ (p5 → p3)) ∧ p3)) → p5) ∧ False) ∨ ((p2 ∧ ((False ∨ (p2 ∧ p3)) ∧ True)) → (p5 → p3)))) ∨ p3) ∧ True) := by
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
  let h6 := h5.left
  let h7 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h8 =>
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- One of the premise coincides with the conclusion.
    exact h11
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_596506454949232390698820256334 : (((((((p4 ∨ (p1 → p4)) ∨ p5) ∧ (p1 → p4)) → (False ∨ ((True ∨ p4) → (p3 ∧ (((p2 ∨ (p1 ∨ p1)) ∨ p4) ∨ p3))))) ∧ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230928077764192506000337012447 : (((p3 ∧ p1) ∨ p2) → ((True ∧ ((((p4 ∧ (p4 ∨ (((False ∧ p3) ∧ p3) ∨ p4))) ∨ ((p1 → p1) ∨ p1)) ∧ (p1 ∧ p3)) ∨ p2)) ∨ True)) := by
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
theorem thm_5_vars_50242626223694607323607862265 : (((((p2 → ((p5 ∨ (((p4 → (p2 → True)) ∧ p3) ∨ (p2 → p2))) ∨ p2)) → (p5 → p1)) → False) ∨ (((p5 → True) ∧ p5) ∨ True)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54580027873498870911451105228 : (((p2 ∨ ((p3 → (False ∧ p4)) ∧ (p4 ∨ False))) ∨ ((((p3 ∨ (p2 → p1)) ∧ (((p2 ∧ p1) ∧ (False → p4)) ∨ p2)) ∧ False) ∨ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233902477913761254980259748115 : ((p4 ∨ (p5 ∨ p1)) → (p3 ∨ (((True ∨ (True ∧ p1)) ∨ False) → ((((p2 → p4) → (p1 ∧ p5)) → (((p4 ∧ False) → p4) ∧ p4)) ∨ True)))) := by
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
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h9 =>
      -- False on the left can always be used.
      apply False.elim h9
  case inr h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h12
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- Disjunctions on the left can always be decomposed.
        cases h13
        case inl h14 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h15 =>
          -- Conjunctions on the left can always be decomposed.
          let h16 := h15.left
          let h17 := h15.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h18 =>
        -- False on the left can always be used.
        apply False.elim h18
    case inr h19 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h20
      -- Disjunctions on the left can always be decomposed.
      cases h20
      case inl h21 =>
        -- Disjunctions on the left can always be decomposed.
        cases h21
        case inl h22 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h23 =>
          -- Conjunctions on the left can always be decomposed.
          let h24 := h23.left
          let h25 := h23.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h26 =>
        -- False on the left can always be used.
        apply False.elim h26



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257706667716830546566518550269 : ((p3 ∨ p3) → ((p4 ∨ False) → ((p5 ∨ ((p4 → (False → (p1 ∧ (True ∧ p3)))) ∧ ((((p2 ∨ p3) ∧ (p4 → p4)) → False) ∧ True))) ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5
  case inr h6 =>
    -- False on the left can always be used.
    apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321025741321673400348663854065 : (p4 ∨ (False ∨ (True ∧ (((True → p1) ∧ ((p2 ∨ ((p2 → (p1 ∨ p5)) ∨ (p2 ∧ (p4 → (False ∧ ((p5 → False) ∧ p4)))))) ∧ p3)) ∨ True)))) := by
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
theorem thm_5_vars_179195156832825889695057299439 : ((p3 ∧ ((p3 → False) → (((p5 → (p2 ∨ (p3 ∨ p4))) ∧ p5) ∧ p3))) ∨ (p5 → ((((p3 ∧ (False ∧ True)) ∨ True) → (p4 → False)) → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68716066394479001612298556187 : ((p4 → (((p4 ∧ ((((p3 → (p4 ∨ ((False → (p5 → (p2 → p3))) ∧ False))) ∨ False) ∨ p5) → p4)) → p3) ∨ ((p1 → p5) ∨ p4))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_644339123765944388358343701893 : ((((False ∨ ((False → (p2 ∨ (p5 ∧ (False → (p4 → False))))) ∨ ((True ∨ ((p3 ∨ ((p4 ∨ p1) → (p2 ∨ p3))) → p4)) ∨ p3))) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53226506583450247561252856348 : (((((p3 ∧ True) ∨ (p3 → p2)) ∨ ((p4 ∨ (p3 ∨ p1)) ∧ True)) ∨ (p1 → ((p4 ∧ p1) ∧ ((p2 ∧ (p2 ∨ p4)) ∧ (p2 ∧ p3))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_724523948322231653651323063551 : ((((False ∨ (p3 ∨ p3)) ∧ ((((p2 ∧ p3) → ((p3 ∨ (False → (False ∨ p2))) ∧ False)) ∨ ((p3 → p1) ∧ (False ∨ (p5 → p5)))) ∨ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315506396141778973343587478123 : (p3 ∨ ((p5 ∨ (p4 ∧ True)) → (((p2 ∨ ((p3 ∨ (p4 → ((p2 ∧ False) ∨ (p4 ∨ False)))) → ((False → p4) → p4))) ∨ (p2 ∧ p3)) ∨ p5))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- Implications on the right can always be decomposed.
    intro h7
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h9 =>
      -- One of the premise coincides with the conclusion.
      exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337095472657624142526787822646 : (p1 → ((((p1 ∨ ((p5 → (p2 ∨ p3)) ∨ True)) → p2) ∨ (((p1 ∧ (True ∧ p4)) ∧ (p3 ∧ p3)) → ((False → p3) → True))) ∨ (True ∧ False))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54523744639060643869270604649 : ((((p4 → False) ∧ (p4 → (p4 ∧ (p3 ∨ p5)))) ∨ (p5 → (((p2 ∨ (((False → False) → (True → p3)) ∨ p5)) ∨ p1) ∧ (True ∨ p5)))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_670750437508625720262491622336 : ((((False ∧ ((p2 ∨ (((True ∧ (((p4 ∨ ((p1 ∧ p3) ∨ False)) → (False → p1)) → p5)) → p2) ∧ p1)) ∨ p3)) ∨ ((p3 ∨ True) ∨ p5)) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_185941093692184254357930961528 : ((((p4 ∨ p4) ∧ (p5 → ((p5 ∧ False) ∧ (p3 → p3)))) ∧ p5) → ((p2 → (p4 ∨ (p5 → (((p2 ∧ p3) ∧ (p1 ∨ p3)) ∧ False)))) → p3)) := by
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
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h8 : p5 := by
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h9 := h6 h8
    -- We need to get the left conjuct of h9 based on <expert-advice>.
    let h10 := h9.left
    -- We need to get the right conjuct of h10 based on <expert-advice>.
    let h11 := h10.right
    -- False on the left can always be used.
    apply False.elim h11
  case inr h12 =>
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h13 : p5 := by
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h14 := h6 h13
    -- We need to get the left conjuct of h14 based on <expert-advice>.
    let h15 := h14.left
    -- We need to get the right conjuct of h15 based on <expert-advice>.
    let h16 := h15.right
    -- False on the left can always be used.
    apply False.elim h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54084283807661813577691830031 : ((((p5 ∧ True) ∨ (((p1 → False) ∧ (False ∧ p2)) ∨ p2)) → ((False ∨ (p5 → (p4 ∧ (p2 ∨ (False ∨ (p4 ∧ p2)))))) → (p5 ∧ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_223322726514017103952474015036 : ((True ∨ (True ∧ p5)) ∧ ((((p4 ∨ p5) ∨ p2) ∧ (True → p3)) → ((p3 → p5) ∨ (p4 → (p3 ∨ (((p5 → False) ∧ (p4 → p1)) ∨ p5)))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h7 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h8 := h3 h7
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h9 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h10
      -- One of the premise coincides with the conclusion.
      exact h9
  case inr h11 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h12
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h13 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h14 := h3 h13
    -- One of the premise coincides with the conclusion.
    exact h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_611789748359892414186499401826 : (((((p1 → ((p1 → p4) ∧ ((((((p3 → False) ∧ (p4 ∧ p3)) ∧ False) → (p3 ∨ p5)) ∧ (p2 ∨ (False ∨ p4))) ∨ False))) → p1) ∨ True) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_234658091997437939810211519790 : ((p4 → (True ∧ p4)) → (((p1 ∧ p2) ∨ ((p4 ∧ p2) ∧ (False → (p4 ∧ True)))) → ((((p4 ∨ p2) ∧ (True → (p2 → False))) ∧ True) → p5))) := by
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
  cases h6
  case inl h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
      have h12 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h7, we can now drive its conclusion.
      let h13 := h7 h12
      -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
      have h14 : p2 := by
        -- One of the premise coincides with the conclusion.
        exact h11
      -- We have shown the premise of h13, we can now drive its conclusion.
      let h15 := h13 h14
      -- False on the left can always be used.
      apply False.elim h15
    case inr h16 =>
      -- Conjunctions on the left can always be decomposed.
      let h17 := h16.left
      let h18 := h16.right
      -- Conjunctions on the left can always be decomposed.
      let h19 := h17.left
      let h20 := h17.right
      -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
      have h21 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h7, we can now drive its conclusion.
      let h22 := h7 h21
      -- We want to use the implication h22 based on <expert-advice>. So we show its premise.
      have h23 : p2 := by
        -- One of the premise coincides with the conclusion.
        exact h20
      -- We have shown the premise of h22, we can now drive its conclusion.
      let h24 := h22 h23
      -- False on the left can always be used.
      apply False.elim h24
  case inr h25 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h26 =>
      -- Conjunctions on the left can always be decomposed.
      let h27 := h26.left
      let h28 := h26.right
      -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
      have h29 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h7, we can now drive its conclusion.
      let h30 := h7 h29
      -- We want to use the implication h30 based on <expert-advice>. So we show its premise.
      have h31 : p2 := by
        -- One of the premise coincides with the conclusion.
        exact h28
      -- We have shown the premise of h30, we can now drive its conclusion.
      let h32 := h30 h31
      -- False on the left can always be used.
      apply False.elim h32
    case inr h33 =>
      -- Conjunctions on the left can always be decomposed.
      let h34 := h33.left
      let h35 := h33.right
      -- Conjunctions on the left can always be decomposed.
      let h36 := h34.left
      let h37 := h34.right
      -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
      have h38 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h7, we can now drive its conclusion.
      let h39 := h7 h38
      -- We want to use the implication h39 based on <expert-advice>. So we show its premise.
      have h40 : p2 := by
        -- One of the premise coincides with the conclusion.
        exact h37
      -- We have shown the premise of h39, we can now drive its conclusion.
      let h41 := h39 h40
      -- False on the left can always be used.
      apply False.elim h41



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_747349184404857226874440109855 : ((((p5 ∨ p4) → (p1 ∨ (((p3 ∨ (p2 ∧ ((p1 → p3) → (False → False)))) ∨ ((False ∨ p2) → (p1 → (p2 ∧ True)))) ∨ (p4 ∨ False)))) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
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
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h5 =>
      -- False on the left can always be used.
      apply False.elim h5
    case inr h6 =>
      -- One of the premise coincides with the conclusion.
      exact h6
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_777659104159998875309456594381 : (((p1 ∨ ((((p5 ∨ (False ∨ (p4 ∨ p3))) ∨ True) ∨ p3) ∧ (p4 → (((((True → True) ∧ False) ∧ True) ∧ p3) → ((p1 ∧ p4) ∨ p5))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230491529889590233161203244021 : (((True → False) ∧ p4) → ((p5 → p1) → ((p1 → ((((p3 ∧ (p1 ∨ p5)) ∧ p5) ∨ (p5 ∧ (((p1 ∨ p5) → True) ∧ p3))) ∨ p3)) ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h5 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h5
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187104663823313717196584586760 : (((False ∧ p3) ∨ ((((p1 ∨ (p1 ∨ p1)) ∨ p5) → p2) ∧ p4)) → ((((p2 ∧ (p2 → (p5 ∧ (p4 ∧ (p3 ∧ p4))))) ∧ p3) ∧ p4) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- False on the left can always be used.
    apply False.elim h3
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_10335119318680897897866315410 : (((p5 ∨ ((p4 ∧ ((p4 ∧ ((p1 ∧ ((True ∧ False) ∨ ((((p2 ∧ p1) ∨ False) → p2) → True))) → False)) → True)) → (p5 ∨ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115861176722150278658701453247 : (((p1 → ((p2 ∨ False) ∨ p4)) ∧ ((p1 ∧ (((p4 → p4) ∧ p2) ∨ (p4 ∨ (True ∧ (True ∨ False))))) → (p2 ∧ (p3 → p2)))) ∨ (p3 → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_620708369190416129523657633037 : (((((p2 ∧ p2) → (((True ∨ p5) → ((True ∨ True) ∨ ((p4 ∧ (p4 ∧ (p4 ∧ p3))) ∨ (p1 ∨ (p3 ∧ (p3 ∨ False)))))) → p1)) ∨ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_705703196855233267650866042444 : (((((p5 → (True ∨ (p5 → p4))) ∧ (p4 ∧ p1)) ∧ (((True → (p4 ∧ (p3 → ((p4 ∧ (p3 → True)) → (p1 ∨ p4))))) ∧ p2) → p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350305879761819255776469844019 : (p4 → ((p3 ∨ ((((p4 ∧ True) ∨ (p5 ∨ p4)) → (False ∧ ((p2 → (p1 ∨ p2)) → (p5 ∧ p5)))) ∨ (p4 ∧ (p1 ∨ (p3 → p3))))) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_216293344508512899470504268188 : ((p2 → ((True → False) ∨ p4)) ∨ ((p3 ∧ p3) ∨ (((True ∨ (False ∨ (p1 ∧ (((False ∨ p4) → p2) → (p1 ∨ p2))))) → p5) ∨ (False → False)))) := by
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
theorem thm_5_vars_804407844185697827848894367141 : (((p3 → (((p3 ∨ (p4 → p2)) → (((False ∨ p4) → p2) ∨ p4)) ∨ (((p2 ∨ (p4 → p3)) → (False ∧ (False ∧ p1))) ∨ (True ∧ p3)))) ∨ p2) ∧ True) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59547951657096643005315191239 : (((p3 → p1) ∨ (((p3 ∧ True) ∨ (((((p2 ∨ ((p4 ∧ True) ∧ p5)) ∧ (p1 ∨ (p4 → True))) ∨ p4) ∧ p5) ∧ (True ∨ p5))) → p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_923272874496007759827279707076 : (((((((p2 → p1) → ((p5 ∧ False) → p3)) ∧ (True ∨ False)) → p1) ∧ ((True ∧ p2) → ((p1 → p5) ∧ ((False ∨ (True → True)) → p3)))) → p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (((p2 → p1) → ((p5 ∧ False) → p3)) ∧ (True ∨ False)) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h5
    -- Implications on the right can always be decomposed.
    intro h6
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- False on the left can always be used.
    apply False.elim h8
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h9 := h2 h4
  -- One of the premise coincides with the conclusion.
  exact h9
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47223503095841814425991310787 : (((((p4 → (p5 ∧ (p1 ∨ (False ∨ p3)))) ∧ p1) ∧ (False ∨ ((True ∧ ((False ∨ (True ∧ (p1 ∧ True))) ∨ p1)) ∧ False))) ∨ (True ∨ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147972949747301952806003344471 : (((p4 → (((p1 → True) → ((((((True ∧ p4) ∨ p3) → p2) ∨ False) ∧ False) ∨ False)) ∧ p3)) ∧ (p3 ∨ p4)) ∨ (((False ∧ True) ∧ p4) → p2)) := by
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
theorem thm_5_vars_51104322471341281699829764624 : ((((p4 ∧ (p1 ∨ ((True → ((p5 ∧ ((p1 → p5) ∧ p3)) → p1)) → (False ∨ p2)))) ∧ p5) ∨ (True ∧ ((True ∨ (p4 ∧ p3)) ∧ True))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_670426513542061279758156781694 : (((((p3 ∨ (p2 → p4)) → (((p4 ∨ ((p5 ∧ False) ∧ False)) ∨ (False ∨ p2)) → (((p5 ∧ True) → False) ∨ p4))) ∨ (True ∨ (p1 ∧ p1))) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_56340130207298650489723692745 : (((((p5 ∨ p4) ∨ p5) ∨ p4) → ((False ∨ ((p5 ∧ ((p4 ∧ ((p1 ∧ True) → p3)) ∨ p1)) → (True ∧ True))) → (p2 ∨ (p1 ∨ True)))) ∨ p5) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Disjunctions on the left can always be decomposed.
        cases h6
        case inl h7 =>
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
      case inr h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_163018805303010746781539624359 : (((((p2 ∧ p4) ∨ ((p4 → (p2 → (p2 ∨ p3))) ∨ p1)) → p1) ∨ (p2 → (p2 ∨ p4))) ∧ (((p5 ∨ p4) → p4) → (p5 ∨ (p1 → p1)))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42081579926523151613909619338 : ((((p2 → p3) ∨ (p1 → ((((p3 ∧ (((p5 ∨ p4) ∨ p3) ∧ p5)) ∨ (True ∧ p5)) ∨ False) ∨ ((p1 → True) ∧ (False ∨ p1))))) ∨ p4) ∨ False) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58471713682716283456040240119 : (((p3 ∨ p5) ∧ (p2 ∨ ((((p3 → p4) ∨ ((p3 → p5) → ((True → (True → p4)) ∧ p1))) ∨ (True → ((p3 ∧ False) ∧ False))) ∧ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137838237477073985449692293850 : ((p3 ∨ ((p5 ∨ (True ∧ (p1 → ((False → (p2 → (p5 → p5))) ∨ p4)))) ∧ (False ∧ ((p4 → p2) ∨ (p5 ∨ p4))))) ∨ (True ∨ (p1 ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44703261683570018376551267567 : (((((p5 → (p3 ∧ p3)) → p5) ∧ ((p3 ∧ (((True → False) ∧ p5) → (((p2 ∨ p3) → p3) ∧ (p3 → False)))) ∧ (p4 ∨ p5))) → p3) ∨ p2) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h8 =>
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h9 =>
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340929717602775636209241570539 : (p2 → (((False ∨ (True → (False → (False ∧ False)))) → ((p3 ∨ True) → ((p4 ∨ p2) ∧ (((((p4 ∧ False) ∨ p2) → False) → True) → p5)))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111785834337535406569581789823 : ((((((p4 ∨ (p1 ∨ (((p3 ∨ p2) → p4) ∧ False))) ∧ p1) ∨ (p2 ∧ (p3 ∧ ((p1 → p5) → True)))) ∨ (p2 ∧ p4)) ∨ True) ∨ (True ∧ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150005579498515025588347220923 : ((p5 ∨ (((p5 ∨ (p4 ∧ (True ∨ (True ∧ False)))) ∨ (p3 ∨ (((True ∧ p4) → (False → True)) → False))) ∨ p2)) ∨ (True ∨ ((p3 ∧ True) ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_316984893132068663871678958443 : (p3 ∨ (p3 → (((p4 → (False → ((((((p1 ∨ p1) ∨ p2) ∨ (p3 → p1)) ∧ p2) ∧ (p2 → (True ∧ p5))) → p3))) → p4) ∨ (p4 → p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217454767663619895516048845428 : (((p5 → (False ∧ False)) ∨ p3) → (((p2 ∨ ((True → (True → (p4 → p5))) ∨ (p2 → p1))) → (p3 → p5)) ∨ (True ∨ (p4 ∧ (p1 ∨ True))))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_726345614607698901076008355489 : (((((p4 ∨ p2) ∨ p2) ∨ (((p2 → (p1 ∨ ((p1 ∨ p4) ∧ ((p4 → True) → p1)))) → (p5 → ((True ∧ (p2 → False)) ∧ p1))) ∨ True)) ∨ False) ∧ True) := by
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
theorem thm_5_vars_177740081866309752197724285235 : ((((p3 ∧ (p5 ∧ p1)) ∨ (p4 ∧ ((p5 ∨ (True → p4)) ∨ p4))) ∧ p5) ∨ (p4 → (p1 ∨ ((p2 ∨ p4) ∧ ((p2 → (p2 ∨ p4)) ∨ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_670737945875148264615613724088 : ((((True ∧ (p4 ∨ (p4 ∨ (False ∧ ((p5 ∨ (p3 → ((p2 → p5) → ((p5 → p1) ∨ False)))) ∨ (p3 → p1)))))) ∨ (p4 ∨ (p3 → True))) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_324354934089655949726920537197 : (p5 ∨ (((p2 ∨ ((False ∨ p3) ∧ p5)) ∧ True) ∨ (True ∨ ((p2 ∧ p5) ∨ (((((p4 ∧ True) ∨ ((p5 → p5) ∧ p5)) ∧ p3) ∧ True) ∧ p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233238585325764728928540188496 : ((True ∨ (True ∧ p1)) → (((p3 ∧ (False ∨ ((p1 ∨ True) ∨ True))) ∧ (p2 ∨ (p1 ∨ (False ∧ (True ∨ p4))))) ∨ (((False ∧ p1) → p1) → True))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_666298637573821892251830670984 : (((((p2 ∨ ((((p1 → p4) ∧ ((((p5 ∨ p2) ∨ p2) ∧ p1) ∧ (p2 → p5))) → p4) ∨ p1)) → (p1 ∧ p5)) ∧ ((p1 ∧ p3) ∨ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356879329791015678209016762100 : (p5 → ((p4 → ((p2 ∧ p2) ∨ p3)) ∨ ((True ∨ p3) ∧ ((((True → (p3 ∧ True)) → (p1 ∧ p2)) ∧ (True ∧ False)) ∨ (p4 ∨ (p5 ∨ p1)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258851089953211711569070459076 : ((True → p1) → (((p2 ∨ (True ∧ p2)) ∨ (p4 → p2)) ∨ (p4 → (p5 ∨ (False ∨ (((p4 → (True → False)) → ((p1 ∨ p1) → False)) ∨ p3)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h6 : p4 := by
      -- One of the premise coincides with the conclusion.
      exact h2
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h7 := h3 h6
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h8 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h9 := h7 h8
    -- False on the left can always be used.
    apply False.elim h9
  case inr h10 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h11 : p4 := by
      -- One of the premise coincides with the conclusion.
      exact h2
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h12 := h3 h11
    -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
    have h13 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h12, we can now drive its conclusion.
    let h14 := h12 h13
    -- False on the left can always be used.
    apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_176575125689039839755471532486 : ((((p4 → ((False ∧ p5) → p4)) ∨ p2) → ((p4 ∧ p1) ∨ (p5 → p5))) ∧ ((p2 → (p4 ∨ ((p3 ∧ (p3 ∨ True)) ∨ p2))) ∧ (True ∨ p4))) := by
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
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h5
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h6
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h6
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225918893598108883963726792570 : (((p2 ∧ True) ∨ p3) ∨ ((p4 ∧ (((p3 ∧ False) ∨ ((p5 ∨ ((p4 ∧ p1) ∧ (p5 ∨ p3))) → p5)) ∨ False)) ∨ (p3 ∨ (p4 ∨ (False → True))))) := by
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
theorem thm_5_vars_705538127799853564192903015544 : (((((((True ∧ p5) → True) ∨ (p3 ∧ p3)) → False) ∧ (p3 ∨ ((True ∨ (False ∧ ((False ∧ (p3 ∧ (p5 → (False ∨ True)))) → p3))) ∨ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_684359986416666074285558160254 : ((((((p1 ∧ ((True ∧ (p2 ∨ True)) → (p1 ∧ p5))) ∧ p4) ∨ (((p5 ∧ False) → p1) → p1)) ∨ (False → ((p1 → p5) → (p5 ∨ p3)))) ∨ p4) ∧ True) := by
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
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165387383273090825075013711531 : ((((p4 ∨ p2) ∧ (p4 ∧ ((((p4 → False) ∨ p3) ∧ True) → p1))) ∨ (p5 ∨ (True ∨ False))) ∨ ((p2 ∨ ((p2 → (p5 ∧ p2)) ∨ p1)) → p2)) := by
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
theorem thm_5_vars_254770359968435984178475502158 : ((p3 ∧ p4) → (((p4 ∧ ((p1 ∧ ((p3 ∨ (p1 ∨ True)) ∧ (p3 ∨ False))) ∨ (p1 ∨ (True ∧ p3)))) → (p5 ∨ p4)) ∧ (p4 ∨ (p4 ∨ p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h11 =>
        -- Conjunctions on the left can always be decomposed.
        let h12 := h1.left
        let h13 := h1.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h13
      case inr h14 =>
        -- False on the left can always be used.
        apply False.elim h14
    case inr h15 =>
      -- Disjunctions on the left can always be decomposed.
      cases h15
      case inl h16 =>
        -- Disjunctions on the left can always be decomposed.
        cases h9
        case inl h17 =>
          -- Conjunctions on the left can always be decomposed.
          let h18 := h1.left
          let h19 := h1.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h19
        case inr h20 =>
          -- False on the left can always be used.
          apply False.elim h20
      case inr h21 =>
        -- Disjunctions on the left can always be decomposed.
        cases h9
        case inl h22 =>
          -- Conjunctions on the left can always be decomposed.
          let h23 := h1.left
          let h24 := h1.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h24
        case inr h25 =>
          -- False on the left can always be used.
          apply False.elim h25
  case inr h26 =>
    -- Disjunctions on the left can always be decomposed.
    cases h26
    case inl h27 =>
      -- Conjunctions on the left can always be decomposed.
      let h28 := h1.left
      let h29 := h1.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h29
    case inr h30 =>
      -- Conjunctions on the left can always be decomposed.
      let h31 := h30.left
      let h32 := h30.right
      -- Conjunctions on the left can always be decomposed.
      let h33 := h1.left
      let h34 := h1.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h34
  -- Conjunctions on the left can always be decomposed.
  let h35 := h1.left
  let h36 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h36



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_686379991268969410474438301239 : ((((((p2 → p3) → (p5 ∧ p5)) ∧ ((((p5 ∨ ((True ∨ False) ∨ False)) → p5) → True) ∨ p5)) → (p4 ∨ (((p2 → p3) ∧ p5) ∨ True))) ∨ p2) ∧ True) := by
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
  cases h3
  case inl h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156969935708195364248884213138 : (((((False ∨ p5) ∧ (p2 ∨ ((False → (p3 ∨ False)) → p3))) ∨ (p1 ∨ (p4 → (p5 ∨ False)))) ∨ True) ∨ ((((True ∨ p1) ∧ True) → p5) ∨ True)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_348027204837749513058916958731 : (p3 → ((p4 ∧ False) ∨ (((((False → p4) → (p5 ∨ (p2 → (p4 ∨ False)))) → ((p2 ∧ False) ∨ p1)) ∧ (p5 ∧ (p5 → p1))) ∨ (p1 ∨ True)))) := by
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
theorem thm_5_vars_66179436140736479133164312175 : ((p5 ∨ ((True ∧ (p3 ∧ (((True ∨ (((p2 ∧ True) ∨ True) → ((True → p5) → p1))) → p1) ∧ p2))) ∧ (((p5 ∨ p2) → p4) ∨ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61323455114703218790017353290 : ((False ∧ (p4 → (p4 ∧ (p4 → (((True ∨ (((p4 ∨ True) ∧ p5) ∨ p3)) ∧ p5) → (True ∧ (((True ∨ True) ∨ (p5 ∧ False)) → False))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45438750720499736660544679496 : (((True ∨ (((p5 ∨ False) ∨ (p1 ∧ ((False → p5) ∨ (((p2 ∧ (True ∧ False)) ∨ p4) ∨ False)))) ∨ ((p1 → False) ∧ (p2 → p2)))) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308486689059840818082073293144 : (p2 ∨ ((((p3 ∨ (p2 ∨ ((p5 ∨ (((p5 ∨ True) ∨ ((p5 → p2) ∨ True)) → p2)) ∧ p4))) ∨ (p3 → p4)) ∨ ((p2 ∧ p5) → True)) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219411983542623590300213782024 : ((p3 ∨ (p3 → (p2 ∨ p3))) → (((False ∨ ((p2 ∨ ((p5 ∧ ((p1 ∨ (p3 ∧ p3)) → (p4 ∧ False))) ∨ True)) ∨ (p4 ∨ p4))) ∨ p3) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56253506640826338972115624231 : (((p1 → ((p2 ∧ p5) ∧ True)) ∨ (False ∧ (p3 ∨ (p5 → (p4 ∧ (False ∧ (((False ∧ p2) ∨ (p5 ∨ ((p2 → True) ∧ p5))) → False))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148989457085559456086948861522 : (((p2 ∨ (p3 ∨ p2)) ∧ (False ∨ (p2 ∨ (((False ∨ (p2 ∧ True)) ∧ (p4 ∨ p2)) ∧ ((False → False) ∧ p3))))) ∨ (((p2 → p3) ∧ p3) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_640562639589767599558594519856 : (((((True ∨ p2) ∧ (((p2 ∧ True) ∨ (p2 → p2)) → (p2 ∨ ((p2 ∧ ((p5 ∨ p4) ∨ False)) ∨ (p1 → ((p4 → p3) → True)))))) → p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_4492629247449451327291138619 : (p2 → (False ∨ (False ∨ ((((p4 ∨ False) ∧ p4) ∨ p2) ∨ ((p4 ∧ ((True ∨ (False ∧ p4)) → False)) ∧ ((False → (p4 ∧ p4)) → True)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
theorem thm_5_vars_342304054391133211776861578274 : (p2 → ((p1 → ((False ∧ p5) ∧ (((True ∧ p5) ∨ ((True ∧ p3) ∧ (p2 ∧ p5))) ∨ (False ∨ p3)))) ∨ ((((p4 ∧ False) ∨ p2) → False) → p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : ((p4 ∧ False) ∨ p2) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119350494685898883470739802547 : ((p3 → ((p4 → False) ∨ (((((True ∧ (p4 → True)) → (p5 ∨ False)) ∧ p1) → (p1 ∨ True)) → (p4 ∧ ((p2 ∨ p4) ∨ p3))))) ∨ (False → False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43347910161385420297411064843 : (((((True → ((p1 ∧ p4) ∧ (p2 ∨ ((p3 → ((p3 → ((p2 ∧ False) ∧ True)) ∨ (p5 ∧ False))) ∨ (False → p4))))) → p1) ∨ p2) → p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299423710200663065946461959370 : (False ∨ ((p5 ∧ ((p1 ∧ (p5 → (((True ∨ True) ∧ p3) ∨ ((True ∨ (p3 → (((True ∨ True) ∨ p5) ∧ False))) → p3)))) ∨ (True ∨ True))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346631557110381826441338331491 : (p3 → ((p1 ∧ ((p4 ∧ ((((((p1 ∧ ((p3 ∧ p3) ∨ p1)) → p1) → (True → p2)) → p1) → p1) ∨ False)) ∨ p3)) ∨ ((p5 ∧ p3) ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44338055376561975362704455890 : ((((((p2 ∧ (p1 ∨ p4)) ∧ ((p2 ∧ ((p3 ∧ p4) → False)) → p4)) ∧ (p5 ∧ p5)) → (False ∨ ((p5 ∨ (p2 ∨ False)) ∧ p4))) → p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_590356380414153088527475608218 : (((((((p1 ∨ p1) ∨ True) → (p1 → (((p2 ∨ (p5 ∧ p2)) ∧ (p3 → (p3 → p5))) ∧ ((p1 ∧ (p1 → p4)) → p1)))) → p5) ∧ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57611370385165775548162099857 : ((((p5 → False) ∧ True) → (p3 → ((((True → p5) ∨ (p1 ∨ (p4 ∧ (((p3 ∧ p3) ∧ (p2 ∨ p5)) ∧ (p2 ∨ False))))) ∨ p3) ∧ p3))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Conjunctions on the left can always be decomposed.
  let h5 := h1.left
  let h6 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_654639617914012119018655728227 : (((((p5 → ((p2 ∧ p4) ∨ ((False ∧ (p1 ∨ p2)) ∨ ((p1 ∨ ((True ∧ p5) ∨ p5)) ∧ (False → (p5 ∧ p2)))))) ∨ p4) ∨ (False ∨ p4)) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- False on the left can always be used.
  apply False.elim h2
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337798320813310908775191811527 : (p1 → ((((True → p2) ∧ ((True ∨ (p5 ∨ p1)) → (p1 ∧ p4))) ∧ ((True ∧ p5) → p1)) → (((p5 ∧ (p2 ∨ (False ∧ p4))) ∧ True) ∨ p4))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h7 : (True ∨ (p5 ∨ p1)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h8 := h6 h7
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- One of the premise coincides with the conclusion.
  exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66529163223196228282755631587 : ((True → ((((((p1 ∧ ((p4 ∨ (p1 → p2)) ∧ p5)) → False) → False) ∨ True) → (((p2 ∧ (p1 ∧ p1)) ∨ p1) ∧ (p5 ∧ p1))) → p1)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : ((((p1 ∧ ((p4 ∨ (p1 → p2)) ∧ p5)) → False) → False) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152446738294432033993610885180 : ((((p4 → True) → False) ∧ ((p4 → p3) → (p1 → ((True ∧ p5) ∨ (((p1 ∧ p5) ∨ (p5 ∨ False)) → p5))))) → ((True → p4) → (p5 ∧ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h5 : (p4 → True) := by
    -- Implications on the right can always be decomposed.
    intro h6
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h7 := h3 h5
  -- False on the left can always be used.
  apply False.elim h7
  -- Conjunctions on the left can always be decomposed.
  let h8 := h1.left
  let h9 := h1.right
  -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
  have h10 : (p4 → True) := by
    -- Implications on the right can always be decomposed.
    intro h11
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h8, we can now drive its conclusion.
  let h12 := h8 h10
  -- False on the left can always be used.
  apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_591836945814614645706980424523 : (((((((p2 → p5) → (p1 ∧ (p1 ∧ ((p5 → (p1 → (p2 ∧ p5))) ∧ p2)))) ∧ (p1 → (True ∨ (p4 → p5)))) ∨ (p3 → True)) ∧ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_88276359580892293093447821891 : (((True → ((p2 ∧ p3) ∨ p2)) ∧ (((p2 ∧ (((p5 ∧ True) ∨ True) ∨ p5)) → (((p5 ∧ p4) → (p4 ∧ (p4 → p5))) → p4)) → p4)) → p2) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h9 =>
    -- One of the premise coincides with the conclusion.
    exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166547933449822661387167995514 : ((p5 ∨ ((True → ((True ∧ (p1 ∨ (((False ∧ True) → False) → p5))) ∧ p2)) → (p5 ∨ False))) ∨ ((p2 ∨ ((True ∨ (p2 → p4)) ∨ p3)) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_58161220863685599341371928497 : (((p3 ∧ True) ∧ ((p1 ∨ (True ∨ p3)) → ((((p3 → p4) → p5) ∨ False) → ((((p5 ∨ True) ∧ p3) ∨ (p2 → p5)) ∧ (p2 ∧ p5))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_262120651286943311077147468991 : (True ∧ ((((p4 ∨ (p2 ∧ p5)) ∧ (p1 ∧ (((True → p1) → False) → (((False ∧ True) ∧ (p3 ∨ p4)) ∧ ((p4 ∧ p5) → False))))) ∧ p3) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_327093318692142405524603263187 : (True → (((p5 → (False → p3)) → (False ∨ ((((p1 ∨ (p4 → p3)) → ((True → False) → False)) ∧ p5) ∨ ((p3 → (p3 → p1)) → p4)))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_221463671337337574398750504924 : (((False → p5) ∨ p1) ∧ (((p1 ∨ (False ∧ (p5 ∧ (p5 → ((p5 ∧ True) → p3))))) ∨ (False ∨ (True ∨ ((p1 → p2) → True)))) ∧ (True ∧ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_93073483582193781124053677609 : ((True ∧ ((((p1 ∧ p2) ∨ (True ∨ p5)) → False) ∧ (p3 ∨ (True ∧ ((True ∧ p3) → (((p1 ∧ p5) ∨ p4) ∧ (True ∨ (p4 ∧ p1)))))))) → p2) := by
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
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h7 : ((p1 ∧ p2) ∨ (True ∨ p5)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h8 := h4 h7
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h12 : ((p1 ∧ p2) ∨ (True ∨ p5)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h13 := h4 h12
    -- False on the left can always be used.
    apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_194797413688151177886448792963 : (((p2 → ((p3 → (p1 ∨ p3)) → True)) ∨ p3) ∧ ((p1 ∨ (p4 ∨ ((True ∨ False) ∧ ((p1 ∧ (p3 ∧ (p3 ∨ p3))) → (p4 ∧ False))))) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67543549815670871549829456963 : ((p1 → (((p5 ∧ p4) ∧ p3) ∨ (p4 ∨ (((p4 ∧ p5) ∧ True) ∨ ((p3 → p4) → (((p4 ∧ True) ∨ p4) ∨ (p1 ∨ (p5 ∨ p2)))))))) ∨ False) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135501459173364379559511747523 : (((True ∨ ((True → (((False → p4) ∧ p4) → p2)) ∨ ((p1 ∧ (True → True)) ∧ (p4 → p2)))) → ((p1 ∨ True) ∧ p5)) ∨ (False → (p2 ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38521192206430515720504868474 : (((((p1 ∨ (p3 ∧ ((p4 ∧ False) → (p4 → True)))) → (False ∧ True)) → ((((p5 ∧ True) ∨ p5) ∨ (p5 ∧ (p2 → p5))) ∨ p5)) ∧ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



