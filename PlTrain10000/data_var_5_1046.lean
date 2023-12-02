variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_704539977286268350274327632226 : (((((True ∧ p3) ∨ (((p5 ∨ (p4 ∨ p1)) ∧ p5) ∧ p1)) → ((True ∨ False) ∧ ((p2 → (p4 ∨ p3)) ∧ (((p3 ∨ p4) ∧ p5) → p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_824100288454487671554073608 : ((p4 ∧ ((((p4 ∨ p1) ∨ p3) → ((p1 → (p3 ∨ (True ∧ p5))) ∨ (p3 → (False → p1)))) ∧ ((p1 ∨ (p3 ∧ p5)) ∨ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233872458265322722171871410437 : ((p4 ∨ (False ∨ True)) → ((((((p3 ∧ False) ∨ False) ∨ (p1 ∨ p2)) → p4) ∧ p2) → ((((p5 ∧ (p2 → p3)) ∨ p2) ∨ p5) → (p4 ∨ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Conjunctions on the left can always be decomposed.
      let h8 := h2.left
      let h9 := h2.right
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h10 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h10
      case inr h11 =>
        -- Disjunctions on the left can always be decomposed.
        cases h11
        case inl h12 =>
          -- False on the left can always be used.
          apply False.elim h12
        case inr h13 =>
          -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
          have h14 : (((p3 ∧ False) ∨ False) ∨ (p1 ∨ p2)) := by
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h9
          -- We have shown the premise of h8, we can now drive its conclusion.
          let h15 := h8 h14
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h15
    case inr h16 =>
      -- Conjunctions on the left can always be decomposed.
      let h17 := h2.left
      let h18 := h2.right
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h19 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h19
      case inr h20 =>
        -- Disjunctions on the left can always be decomposed.
        cases h20
        case inl h21 =>
          -- False on the left can always be used.
          apply False.elim h21
        case inr h22 =>
          -- We want to use the implication h17 based on <expert-advice>. So we show its premise.
          have h23 : (((p3 ∧ False) ∨ False) ∨ (p1 ∨ p2)) := by
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h18
          -- We have shown the premise of h17, we can now drive its conclusion.
          let h24 := h17 h23
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h24
  case inr h25 =>
    -- Conjunctions on the left can always be decomposed.
    let h26 := h2.left
    let h27 := h2.right
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h28 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h28
    case inr h29 =>
      -- Disjunctions on the left can always be decomposed.
      cases h29
      case inl h30 =>
        -- False on the left can always be used.
        apply False.elim h30
      case inr h31 =>
        -- We want to use the implication h26 based on <expert-advice>. So we show its premise.
        have h32 : (((p3 ∧ False) ∨ False) ∨ (p1 ∨ p2)) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h27
        -- We have shown the premise of h26, we can now drive its conclusion.
        let h33 := h26 h32
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h33



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345406490819307036681222711397 : (p3 → (((((p2 → (p4 ∧ True)) → ((((False ∨ (p4 ∧ False)) → p4) ∨ (p5 ∨ p3)) ∧ p5)) ∧ ((True ∧ p4) ∨ (p5 ∧ True))) → p1) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42424610235708909776442052339 : (((p5 ∧ ((((p3 ∧ (((False ∧ True) ∨ p5) → (True ∨ False))) → (p5 ∧ p5)) ∨ True) ∨ ((p2 → ((True ∧ p5) ∧ p4)) → True))) ∨ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_644162132871097901525720131688 : ((((True ∨ (p4 ∨ ((((True ∨ ((p5 ∨ p2) ∨ ((p2 ∨ False) → True))) ∧ (p1 → (p3 → False))) ∨ False) ∧ (p3 → (False ∨ False))))) → p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187451179762471366415683418561 : ((True ∨ ((((False → p2) → p4) ∧ (p3 → (p2 → p4))) → p3)) → ((False ∨ (p3 → p5)) → (((p2 ∨ False) ∧ (p2 ∧ p4)) → (True → p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h6.left
    let h9 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h10 =>
      -- False on the left can always be used.
      apply False.elim h10
    case inr h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h12 =>
        -- One of the premise coincides with the conclusion.
        exact h9
      case inr h13 =>
        -- One of the premise coincides with the conclusion.
        exact h9
  case inr h14 =>
    -- False on the left can always be used.
    apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158987486265706581833782191652 : ((p3 ∨ ((p3 ∨ (p4 → False)) ∨ ((p4 → (True ∧ p5)) → ((p3 ∧ p3) ∨ (p5 ∨ (p5 ∨ True)))))) ∨ ((p1 → (p4 → (False ∨ p2))) ∧ p3)) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_684262958347400440861856327597 : (((((False ∧ ((p4 ∧ p3) ∧ ((p2 ∨ ((False ∧ p3) ∨ p4)) → p5))) ∧ ((p2 ∨ p5) → p2)) ∨ (p1 ∧ (False ∧ ((True → p4) → p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_226605239239372574405682537723 : (((p5 → p2) ∨ p3) ∨ (False ∨ (((((p1 ∧ False) ∨ True) → ((False → (p1 → False)) ∧ (False ∧ False))) → ((p4 ∧ False) ∧ (p3 ∧ p2))) ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p1 ∧ False) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- False on the left can always be used.
  apply False.elim h5
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h6 : ((p1 ∧ False) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h7 := h1 h6
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- We need to get the left conjuct of h8 based on <expert-advice>.
  let h9 := h8.left
  -- False on the left can always be used.
  apply False.elim h9
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h10 : ((p1 ∧ False) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h11 := h1 h10
  -- We need to get the right conjuct of h11 based on <expert-advice>.
  let h12 := h11.right
  -- We need to get the left conjuct of h12 based on <expert-advice>.
  let h13 := h12.left
  -- False on the left can always be used.
  apply False.elim h13
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h14 : ((p1 ∧ False) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h15 := h1 h14
  -- We need to get the right conjuct of h15 based on <expert-advice>.
  let h16 := h15.right
  -- We need to get the left conjuct of h16 based on <expert-advice>.
  let h17 := h16.left
  -- False on the left can always be used.
  apply False.elim h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_69201605805836547234797323277 : ((p5 → (((p3 ∨ (((p4 ∧ p1) → p2) → (p3 ∨ True))) → True) → (True → (p3 ∧ ((((False ∨ (p1 ∨ p3)) ∨ p5) ∨ p4) → False))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_189613510048841818052968243151 : ((False ∨ (False → (p5 ∨ (p5 ∧ (p3 → (p3 → p3)))))) ∧ ((p2 → True) ∧ ((((p4 ∧ False) ∨ p5) ∨ p1) ∨ (p2 → ((p4 → p2) → True))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_808482539621325431297378298789 : (((p4 → (p3 ∨ (p2 → (p2 ∧ (((((p2 ∧ (((p1 → (p1 → p3)) ∨ (p4 ∧ False)) ∨ p5)) ∨ True) ∧ p5) ∨ False) ∨ (p2 ∨ False)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200341122203937030196192968177 : (((p3 ∨ p3) ∧ (False ∨ (p4 → (p3 ∨ p3)))) → (((((p3 ∨ (p4 ∨ False)) ∧ (p4 ∧ ((p2 ∧ (p3 → p4)) ∧ p4))) ∧ p1) ∨ p3) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h5 =>
      -- False on the left can always be used.
      apply False.elim h5
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h8 =>
      -- False on the left can always be used.
      apply False.elim h8
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_261508110429675761916100759892 : ((p5 → p3) → (((((p3 ∧ (p3 → p1)) ∨ (False ∧ p4)) ∨ ((((True → p2) → ((p2 ∧ p4) → p2)) ∧ True) ∧ p1)) ∨ p1) ∨ (False → p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58096900353343932589914639073 : (((p1 ∧ p2) ∧ (((((False → (False ∧ p5)) ∧ ((p4 → p1) ∧ (True ∧ ((p1 ∨ (p5 → p5)) ∨ True)))) ∧ (True → p5)) ∨ False) → p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45168873236717575055257455797 : (((True ∧ ((((p1 ∨ p3) ∨ p3) → p1) ∧ ((p3 ∧ ((p3 → (p2 → ((((p5 ∧ p5) ∨ p4) → True) → p4))) ∨ p5)) → True))) → p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_196864789948210528050582777319 : (((p3 ∨ (True ∧ (True ∨ (p2 ∧ p5)))) ∧ p3) ∨ (((p2 ∨ True) → (p5 ∨ (p2 → (((p4 ∧ True) ∨ (p5 → (p3 → p1))) ∨ True)))) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134675614842133800050202730101 : (((((((p5 ∨ p1) ∧ p5) ∨ (p5 ∨ p4)) ∧ False) → (((p5 → p2) → (p2 → p2)) → ((p4 ∨ p1) ∨ p5))) → p1) ∨ (p5 ∨ (p2 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134147980548699626463443219898 : ((((p3 → ((((True → p5) ∨ p4) ∨ (p5 → ((False ∧ (True → p5)) ∨ p5))) ∨ True)) ∧ ((p2 ∨ p1) ∧ p3)) ∨ True) ∨ ((False ∨ True) → p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48054563311543281960325834654 : ((((p5 ∧ (False → (False ∨ (p4 ∨ (p2 ∨ p2))))) ∧ (((p2 ∧ False) → (p4 ∨ False)) ∧ (p2 ∧ (True → (True ∨ p4))))) → (p4 ∧ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_756663462411360985221893263132 : (((p1 ∧ ((((((p3 ∨ p2) → (p2 ∨ p2)) → (False ∨ p3)) → True) → (p4 ∧ p1)) ∨ ((p3 ∧ (p1 ∧ p4)) ∧ (p2 → (False → p2))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166138085970330340108440580913 : ((True ∧ (p2 ∧ (((p2 ∧ ((p5 ∨ p2) ∨ ((p1 ∧ False) → True))) ∨ p4) ∨ (p5 → p5)))) ∨ ((False ∧ True) ∨ (((p5 ∨ p5) ∧ p2) → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186812331846443311781198136412 : (((p3 ∨ ((p5 ∧ p5) → p2)) ∧ ((p4 → (p2 ∨ False)) ∨ p1)) → ((p2 ∧ True) ∨ ((p5 ∨ p1) ∨ (((False ∨ (p3 ∨ p1)) ∨ True) ∨ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h5 =>
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
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h6
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h8 =>
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
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177970968981916524223789186982 : ((((p5 → p2) → (((p2 → (p4 → p1)) ∧ True) → (False ∧ False))) ∨ p4) ∨ (((True → (True ∨ p3)) ∨ (True ∨ (p3 → p3))) ∨ (False ∨ p4))) := by
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
theorem thm_5_vars_42682743312677614392038203571 : (((p5 ∨ ((((p4 → (False ∨ p1)) ∧ ((p1 ∧ p1) → ((p5 → (p3 ∧ (p2 ∧ (p2 ∨ True)))) → (p2 ∧ p2)))) ∧ p3) ∧ p5)) ∨ True) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_822439426963991007150949547242 : ((((((((p2 → p1) ∨ p5) ∨ True) ∧ (p1 → (p3 ∧ False))) ∨ (p3 ∧ ((((False ∧ p4) → p5) ∧ ((p4 ∧ True) ∨ p1)) → p4))) ∧ p1) → p3) ∧ True) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
        have h9 : p1 := by
          -- One of the premise coincides with the conclusion.
          exact h3
        -- We have shown the premise of h6, we can now drive its conclusion.
        let h10 := h6 h9
        -- We need to get the left conjuct of h10 based on <expert-advice>.
        let h11 := h10.left
        -- One of the premise coincides with the conclusion.
        exact h11
      case inr h12 =>
        -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
        have h13 : p1 := by
          -- One of the premise coincides with the conclusion.
          exact h3
        -- We have shown the premise of h6, we can now drive its conclusion.
        let h14 := h6 h13
        -- We need to get the left conjuct of h14 based on <expert-advice>.
        let h15 := h14.left
        -- One of the premise coincides with the conclusion.
        exact h15
    case inr h16 =>
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h17 : p1 := by
        -- One of the premise coincides with the conclusion.
        exact h3
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h18 := h6 h17
      -- We need to get the left conjuct of h18 based on <expert-advice>.
      let h19 := h18.left
      -- One of the premise coincides with the conclusion.
      exact h19
  case inr h20 =>
    -- Conjunctions on the left can always be decomposed.
    let h21 := h20.left
    let h22 := h20.right
    -- One of the premise coincides with the conclusion.
    exact h21
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193960005607402622124094139913 : ((p2 ∨ (p2 ∨ ((((True ∧ p2) → p4) ∧ True) ∨ True))) → (p3 ∨ (p2 → (((((True ∧ p2) ∧ p3) ∨ p4) ∨ (p4 → p1)) ∨ (False → p1))))) := by
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
        -- Conjunctions on the left can always be decomposed.
        let h11 := h10.left
        let h12 := h10.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h13
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h14
        -- False on the left can always be used.
        apply False.elim h14
      case inr h15 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h16
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h17
        -- False on the left can always be used.
        apply False.elim h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_139976655617323511802435470881 : (((True → (((True → (((p1 ∧ p3) → ((p1 ∧ True) → (p5 ∧ p1))) ∨ p3)) ∧ (False ∧ p3)) ∧ p3)) ∧ (p3 ∨ True)) → ((p3 ∧ True) ∨ p1)) := by
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
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h4
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h6 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h7 := h2 h6
    -- We need to get the left conjuct of h7 based on <expert-advice>.
    let h8 := h7.left
    -- We need to get the right conjuct of h8 based on <expert-advice>.
    let h9 := h8.right
    -- We need to get the left conjuct of h9 based on <expert-advice>.
    let h10 := h9.left
    -- False on the left can always be used.
    apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_209326112360784571596597612711 : ((False → ((True ∨ (p3 → p2)) ∨ p1)) → ((((p2 → (p2 ∧ False)) ∧ True) ∧ ((((p2 → (p2 ∨ (p2 → p2))) ∧ True) ∧ p3) → p4)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314478774001028150215857528544 : (p3 ∨ (((p1 ∧ False) → ((p1 ∨ (p5 → p4)) ∨ (((p4 ∨ p1) → p3) ∨ (((p4 ∧ p5) → p5) ∧ p1)))) → (p4 → ((p4 ∨ True) ∨ p2)))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160722050096357353258962027749 : (((p3 ∨ (p5 → ((p5 → (True → p3)) ∧ p2))) ∨ ((p2 ∨ True) ∧ (p4 → ((p2 → p3) → p4)))) → (((p5 → (p3 ∧ p3)) ∨ p4) ∨ True)) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_183861941126325126860738629814 : ((((p2 → (p1 ∨ (p5 → p2))) ∧ ((True ∧ True) ∨ True)) ∧ False) ∨ (((p3 → (p1 ∨ ((p2 ∧ p2) ∧ (p2 → p4)))) ∨ p4) ∨ (p1 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258765764782252621357757211571 : ((True → False) → ((((True ∨ True) ∨ p1) → (p1 ∧ (p3 ∧ (p4 ∨ ((((p2 ∨ p5) ∨ ((p1 ∧ (p5 ∧ p2)) ∧ p1)) ∨ p1) ∨ True))))) ∨ p1)) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248004350675104625285730972754 : ((p1 ∨ p4) ∨ (p2 → ((((True ∨ p2) ∨ ((p3 → (p1 ∨ p2)) ∧ p1)) → (((p2 ∧ (p2 → p5)) → ((p2 → p1) ∧ False)) ∧ p3)) ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_201407448286989810536296817522 : (((((p5 ∧ p1) ∨ p2) ∨ True) ∧ True) ∧ ((p4 ∨ (((False → True) ∨ p3) → False)) ∨ (True ∨ (((True ∨ (False ∨ p5)) ∧ (False ∨ p5)) → p1)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53290091367086984217630840371 : (((False ∨ ((((False ∧ (p1 ∧ p1)) ∨ p4) ∨ (True → False)) ∧ p3)) ∨ (False ∨ ((False ∨ p5) → (p1 → ((False ∨ (p4 → p5)) ∨ p1))))) ∨ p3) := by
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
  cases h1
  case inl h3 =>
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184802399214536210944916988622 : (((False ∨ (p5 ∨ (p1 ∧ p4))) ∨ ((p2 → p3) → (p5 ∨ p5))) ∨ (((p4 ∧ (False ∧ p2)) ∧ (((p1 → p4) ∧ (True → p1)) → p1)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60746746149329986158186173874 : ((True ∧ ((True → (p1 ∨ p2)) ∨ ((((((True → (p2 ∨ p2)) ∧ (p2 ∨ p3)) ∨ (p4 ∧ ((p3 ∧ p1) ∧ p5))) → False) ∧ p1) ∨ True))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_207287617566802519456690041158 : ((((p1 ∧ (True → p5)) → p2) ∨ p4) → (((((p3 → True) → p5) ∧ (p2 → (((True ∧ False) → p4) ∧ p1))) → (p2 ∨ p5)) ∨ (True ∨ p5))) := by
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
theorem thm_5_vars_349459883778752832970720038386 : (p3 → (p5 → ((p3 → (p4 ∨ (((p4 ∧ ((p4 ∧ (p2 → p3)) ∨ (((True → p2) ∧ (p4 ∨ (p2 → p1))) ∨ p1))) ∨ True) ∧ p5))) ∨ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_349294850734281039691084228300 : (p3 → (p2 → ((((True → True) ∧ ((((p3 ∨ p2) ∨ (p2 → True)) ∧ p3) → False)) ∨ p1) ∨ (p2 ∨ ((p5 ∧ (p3 ∨ (p4 → p3))) ∨ p3))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217302878820680880809800761543 : (((p5 ∧ (p4 ∧ p4)) ∨ p4) → ((False ∨ ((((False → (p2 ∨ p5)) → (False → (p2 ∨ (p4 ∨ p1)))) ∧ p3) ∨ p2)) ∨ (p2 ∨ (True → True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51813447921749613527071142289 : (((True → ((((True → (p3 → p5)) → p1) → ((p4 ∨ p4) → (False → p2))) → p2)) ∧ (((((False → False) ∧ p2) ∧ p2) ∧ p1) ∨ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328637799149680548172785339745 : (True → (((p3 → (((p3 ∨ (((p1 ∨ True) ∨ p3) ∨ p4)) ∨ p2) ∧ p5)) ∨ p2) → ((p3 ∧ (p3 → (p3 ∧ ((p2 ∧ p3) ∧ p1)))) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119512314287713106427965975797 : ((p5 → (((p4 → p1) ∧ ((p3 ∧ (((p4 ∨ True) → p1) ∨ (((p1 ∧ (p2 ∧ True)) ∧ (p2 → p2)) → p3))) ∨ p2)) ∧ True)) ∨ (p4 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192217088688283874689432016459 : ((((p4 ∧ (p3 ∧ (p4 ∨ (False → p4)))) → True) ∧ p1) → (((True ∧ (True → p1)) ∧ ((p1 → (p2 ∨ ((p4 ∨ False) → p3))) ∧ p2)) ∨ p1)) := by
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
theorem thm_5_vars_114649154073887757653980438228 : ((((((((False ∨ p4) ∨ (p5 ∧ p1)) ∧ False) → p4) → p1) ∨ ((False ∨ p5) ∧ False)) ∨ (False ∨ ((p1 ∧ (True ∨ True)) → p4))) ∨ (True ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_656417442990551488585631371730 : ((((((p4 ∨ p5) → (False → (True ∨ ((p5 → True) ∨ p3)))) ∧ (((p4 ∨ p4) ∨ ((p1 ∧ (False → True)) ∧ p2)) ∨ p2)) ∨ (p3 → p3)) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44175611102014876444396234869 : ((((p1 ∧ (p5 → (((p5 ∨ p5) → ((((p3 → p1) ∨ p1) → True) → p1)) ∧ (p3 ∨ (False ∨ p4))))) → (p3 ∧ (p1 → p2))) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49661399535197871645952590177 : (((((p5 → True) ∨ p5) ∨ (((((p3 ∧ p5) → p2) → (p5 ∨ ((False ∧ p1) ∧ (p4 ∨ False)))) → p3) ∧ p2)) → ((True ∨ p3) → p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44522790679175454247026210660 : ((((p5 ∧ (True ∨ ((p5 ∧ p4) → (p3 → (p5 → p1))))) ∨ (p5 ∨ ((((p5 ∧ p3) ∨ True) → (True ∨ (p2 → p5))) ∧ p3))) → p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197667463291939848913551247514 : ((((p2 ∧ True) → (p3 ∨ False)) → (p4 ∨ p4)) ∨ (True ∨ (((p1 → (((p2 ∨ p2) ∧ p2) ∧ False)) ∨ (p4 ∨ ((p5 → True) ∨ p4))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148048867514476454413620386673 : (((p4 ∧ ((p1 ∨ (p1 → (p3 ∨ ((p5 ∧ True) ∨ p2)))) ∨ (True ∧ ((p4 ∨ False) → False)))) ∨ (p2 → p2)) ∨ (p3 → ((True ∧ p2) ∧ p4))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136151332186545511882670072904 : ((((p1 → p3) ∧ ((True ∧ p4) → (p4 → True))) → ((((((p3 ∨ p2) ∨ p4) ∨ False) ∨ p2) ∨ p1) → (p1 ∧ p1))) ∨ ((p2 ∨ False) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340716451208272261643967364341 : (p2 → ((((p4 ∨ p1) → ((False → ((p1 ∧ ((p2 ∨ p4) ∨ p1)) ∧ ((((True → p2) ∧ False) ∨ False) ∨ (p4 → p1)))) → p1)) ∧ p2) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341740941440090707092231944961 : (p2 → (((True → p4) → ((p3 ∨ (((True ∨ p2) ∧ p1) ∨ p5)) → (p5 ∨ (p5 ∨ ((p1 ∨ ((p4 ∧ p2) ∧ p5)) ∨ p4))))) ∨ (p5 → p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205529069249139591564805704221 : (((False ∨ p3) ∧ (p2 ∧ (True → p1))) ∨ ((p1 ∨ (((p3 ∧ (p1 ∧ p3)) → False) ∨ (True ∨ p1))) ∨ (p3 ∨ (False ∨ (p1 ∨ (p4 → True)))))) := by
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
theorem thm_5_vars_158193363607321458814428903075 : ((((False ∧ p1) ∧ p3) ∧ ((p3 ∨ (((False ∨ p1) ∨ (((p5 ∨ p5) ∨ p4) ∨ p2)) ∨ p4)) ∨ False)) ∨ (True ∨ ((p1 ∧ (False ∨ p5)) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50796518826578938092357724816 : (((False → ((p3 → ((((False ∧ (p2 → (True ∧ False))) ∨ p5) ∧ p1) ∧ ((p5 → p1) → p5))) ∧ p5)) → (p2 ∧ ((p4 → p4) → p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111960693836135491174907911101 : ((((((p5 → p1) ∧ ((p3 ∧ p2) → p4)) → False) → ((p2 ∨ p2) → ((((p2 → p1) → False) → True) → (p3 ∧ p3)))) ∨ False) ∨ (True ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37369442960458462085028354530 : (((((p3 ∨ (((p5 ∧ ((p2 → (True ∨ (p1 → p4))) ∧ p2)) → (p4 → (p1 → (p3 ∨ (p5 → p3))))) ∧ p5)) ∨ True) ∨ p5) ∧ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_145024532501807352229468306003 : ((((p5 ∧ (p4 ∨ p2)) ∨ ((False → p1) ∧ ((p1 ∨ p4) ∧ p4))) ∨ ((p3 → ((True ∧ p5) ∨ False)) → True)) ∧ (p3 → (p3 ∨ (False ∨ False)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64939128257155088977763547723 : ((p2 ∨ (((p1 ∧ ((p5 → p2) ∧ p3)) ∨ ((p4 ∧ p3) ∨ (True → p3))) ∨ ((False → ((False ∨ ((p3 ∨ False) ∨ p3)) ∨ p5)) ∨ p3))) ∨ p2) := by
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
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178047544816737015748752835439 : (((((p1 → True) ∨ (p4 ∨ ((False ∨ p1) → (p1 ∨ p4)))) ∧ True) → False) ∨ ((p3 ∧ (p5 → ((False → (p5 → (True → p5))) → p4))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_465091597495032175563763470239 : ((((p3 ∧ ((p2 ∨ (((p3 ∨ p2) → p3) → p5)) ∨ ((p5 → p1) ∧ (True → p2)))) → ((False → p4) → (True → ((p4 ∨ True) ∧ p3)))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h12 := h1.left
  let h13 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h13
  case inl h14 =>
    -- Disjunctions on the left can always be decomposed.
    cases h14
    case inl h15 =>
      -- One of the premise coincides with the conclusion.
      exact h12
    case inr h16 =>
      -- One of the premise coincides with the conclusion.
      exact h12
  case inr h17 =>
    -- Conjunctions on the left can always be decomposed.
    let h18 := h17.left
    let h19 := h17.right
    -- One of the premise coincides with the conclusion.
    exact h12
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_343402376721829600047096235588 : (p2 → ((p3 ∧ p5) ∨ ((((p3 → False) ∨ (p1 ∨ ((p2 ∧ p4) ∨ ((p4 → p3) ∧ ((p5 ∧ p3) ∨ ((p1 → True) → p4)))))) ∧ True) ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_689011584820658983531994391045 : (((((((p3 ∨ ((((p5 ∨ p2) ∧ p4) ∧ p4) ∧ p4)) ∨ True) ∧ (p2 ∨ True)) ∨ p2) ∨ (((p3 ∨ False) ∨ p4) ∧ (p4 ∧ (False ∨ p3)))) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134088802789292442638898073898 : (((((p5 → p4) ∧ ((p3 → (((p3 ∧ p5) → p2) → False)) ∨ (p1 ∨ (p5 ∧ (p1 → (p2 ∧ p1)))))) → p3) ∨ p5) ∨ ((True ∨ True) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_743437972719089508180289913482 : ((((p5 → p3) ∨ ((False ∨ ((p1 ∧ (p2 → p3)) ∨ ((False ∨ p1) → (False ∧ p5)))) ∨ (p2 ∧ (p5 ∨ (p3 → ((True → True) → p3)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158002420163027252725752497553 : (((p4 ∨ ((((True ∨ p5) ∨ p2) → p5) ∨ p4)) → (((p1 ∧ (True ∧ False)) ∧ p5) ∨ (p1 ∨ p2))) ∨ (p2 → ((True ∨ (p5 ∨ p3)) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_683278565014419421416936805217 : ((((p2 ∨ (((True → p3) → (p5 ∨ (((p3 ∧ (p1 ∧ False)) ∨ p3) → (False ∧ p5)))) ∧ p5)) ∧ (p1 ∨ (p5 ∧ (False ∨ (p4 ∧ p1))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248998875347717869036937903699 : ((p4 ∨ False) ∨ ((False ∨ (((((((p1 → True) ∨ p1) → p2) ∨ (True ∨ p1)) ∧ (False → p2)) ∨ p3) ∧ (False → (False ∨ True)))) ∨ (False ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115621065992054600114971855938 : (((p3 → (((True ∨ p4) ∨ p1) ∨ p1)) ∧ ((p5 ∨ p3) ∨ (True ∧ ((p1 ∧ (False ∨ p3)) ∨ (((p2 ∧ p3) ∨ False) ∧ p3))))) ∨ (p5 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191112404737572572244026066422 : (((p5 ∧ (p5 ∨ p3)) ∧ (p4 ∧ ((True ∧ p3) → p1))) ∨ (True ∧ ((((p4 ∨ p4) ∨ (True ∨ p5)) ∧ False) ∨ ((p3 ∧ False) ∨ (p1 ∨ True))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_140476612991163278308640527822 : (((((((p4 ∨ (p3 ∨ p4)) → (False → False)) → (False ∧ p5)) ∧ (p5 ∨ p5)) ∧ p4) ∧ (((True ∧ p5) ∧ True) ∨ p3)) → (p5 ∧ (p1 ∧ False))) := by
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
  let h6 := h4.left
  let h7 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- Conjunctions on the left can always be decomposed.
      let h12 := h10.left
      let h13 := h10.right
      -- One of the premise coincides with the conclusion.
      exact h13
    case inr h14 =>
      -- One of the premise coincides with the conclusion.
      exact h8
  case inr h15 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h16 =>
      -- Conjunctions on the left can always be decomposed.
      let h17 := h16.left
      let h18 := h16.right
      -- Conjunctions on the left can always be decomposed.
      let h19 := h17.left
      let h20 := h17.right
      -- One of the premise coincides with the conclusion.
      exact h20
    case inr h21 =>
      -- One of the premise coincides with the conclusion.
      exact h15
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h22 := h1.left
  let h23 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h24 := h22.left
  let h25 := h22.right
  -- Conjunctions on the left can always be decomposed.
  let h26 := h24.left
  let h27 := h24.right
  -- Disjunctions on the left can always be decomposed.
  cases h27
  case inl h28 =>
    -- Disjunctions on the left can always be decomposed.
    cases h23
    case inl h29 =>
      -- Conjunctions on the left can always be decomposed.
      let h30 := h29.left
      let h31 := h29.right
      -- Conjunctions on the left can always be decomposed.
      let h32 := h30.left
      let h33 := h30.right
      -- We want to use the implication h26 based on <expert-advice>. So we show its premise.
      have h34 : ((p4 ∨ (p3 ∨ p4)) → (False → False)) := by
        -- Implications on the right can always be decomposed.
        intro h35
        -- Implications on the right can always be decomposed.
        intro h36
        -- False on the left can always be used.
        apply False.elim h36
      -- We have shown the premise of h26, we can now drive its conclusion.
      let h37 := h26 h34
      -- We need to get the left conjuct of h37 based on <expert-advice>.
      let h38 := h37.left
      -- False on the left can always be used.
      apply False.elim h38
    case inr h39 =>
      -- We want to use the implication h26 based on <expert-advice>. So we show its premise.
      have h40 : ((p4 ∨ (p3 ∨ p4)) → (False → False)) := by
        -- Implications on the right can always be decomposed.
        intro h41
        -- Implications on the right can always be decomposed.
        intro h42
        -- False on the left can always be used.
        apply False.elim h42
      -- We have shown the premise of h26, we can now drive its conclusion.
      let h43 := h26 h40
      -- We need to get the left conjuct of h43 based on <expert-advice>.
      let h44 := h43.left
      -- False on the left can always be used.
      apply False.elim h44
  case inr h45 =>
    -- Disjunctions on the left can always be decomposed.
    cases h23
    case inl h46 =>
      -- Conjunctions on the left can always be decomposed.
      let h47 := h46.left
      let h48 := h46.right
      -- Conjunctions on the left can always be decomposed.
      let h49 := h47.left
      let h50 := h47.right
      -- We want to use the implication h26 based on <expert-advice>. So we show its premise.
      have h51 : ((p4 ∨ (p3 ∨ p4)) → (False → False)) := by
        -- Implications on the right can always be decomposed.
        intro h52
        -- Implications on the right can always be decomposed.
        intro h53
        -- False on the left can always be used.
        apply False.elim h53
      -- We have shown the premise of h26, we can now drive its conclusion.
      let h54 := h26 h51
      -- We need to get the left conjuct of h54 based on <expert-advice>.
      let h55 := h54.left
      -- False on the left can always be used.
      apply False.elim h55
    case inr h56 =>
      -- We want to use the implication h26 based on <expert-advice>. So we show its premise.
      have h57 : ((p4 ∨ (p3 ∨ p4)) → (False → False)) := by
        -- Implications on the right can always be decomposed.
        intro h58
        -- Implications on the right can always be decomposed.
        intro h59
        -- False on the left can always be used.
        apply False.elim h59
      -- We have shown the premise of h26, we can now drive its conclusion.
      let h60 := h26 h57
      -- We need to get the left conjuct of h60 based on <expert-advice>.
      let h61 := h60.left
      -- False on the left can always be used.
      apply False.elim h61
  -- Conjunctions on the left can always be decomposed.
  let h62 := h1.left
  let h63 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h64 := h62.left
  let h65 := h62.right
  -- Conjunctions on the left can always be decomposed.
  let h66 := h64.left
  let h67 := h64.right
  -- Disjunctions on the left can always be decomposed.
  cases h67
  case inl h68 =>
    -- Disjunctions on the left can always be decomposed.
    cases h63
    case inl h69 =>
      -- Conjunctions on the left can always be decomposed.
      let h70 := h69.left
      let h71 := h69.right
      -- Conjunctions on the left can always be decomposed.
      let h72 := h70.left
      let h73 := h70.right
      -- We want to use the implication h66 based on <expert-advice>. So we show its premise.
      have h74 : ((p4 ∨ (p3 ∨ p4)) → (False → False)) := by
        -- Implications on the right can always be decomposed.
        intro h75
        -- Implications on the right can always be decomposed.
        intro h76
        -- False on the left can always be used.
        apply False.elim h76
      -- We have shown the premise of h66, we can now drive its conclusion.
      let h77 := h66 h74
      -- We need to get the left conjuct of h77 based on <expert-advice>.
      let h78 := h77.left
      -- False on the left can always be used.
      apply False.elim h78
    case inr h79 =>
      -- We want to use the implication h66 based on <expert-advice>. So we show its premise.
      have h80 : ((p4 ∨ (p3 ∨ p4)) → (False → False)) := by
        -- Implications on the right can always be decomposed.
        intro h81
        -- Implications on the right can always be decomposed.
        intro h82
        -- False on the left can always be used.
        apply False.elim h82
      -- We have shown the premise of h66, we can now drive its conclusion.
      let h83 := h66 h80
      -- We need to get the left conjuct of h83 based on <expert-advice>.
      let h84 := h83.left
      -- False on the left can always be used.
      apply False.elim h84
  case inr h85 =>
    -- Disjunctions on the left can always be decomposed.
    cases h63
    case inl h86 =>
      -- Conjunctions on the left can always be decomposed.
      let h87 := h86.left
      let h88 := h86.right
      -- Conjunctions on the left can always be decomposed.
      let h89 := h87.left
      let h90 := h87.right
      -- We want to use the implication h66 based on <expert-advice>. So we show its premise.
      have h91 : ((p4 ∨ (p3 ∨ p4)) → (False → False)) := by
        -- Implications on the right can always be decomposed.
        intro h92
        -- Implications on the right can always be decomposed.
        intro h93
        -- False on the left can always be used.
        apply False.elim h93
      -- We have shown the premise of h66, we can now drive its conclusion.
      let h94 := h66 h91
      -- We need to get the left conjuct of h94 based on <expert-advice>.
      let h95 := h94.left
      -- False on the left can always be used.
      apply False.elim h95
    case inr h96 =>
      -- We want to use the implication h66 based on <expert-advice>. So we show its premise.
      have h97 : ((p4 ∨ (p3 ∨ p4)) → (False → False)) := by
        -- Implications on the right can always be decomposed.
        intro h98
        -- Implications on the right can always be decomposed.
        intro h99
        -- False on the left can always be used.
        apply False.elim h99
      -- We have shown the premise of h66, we can now drive its conclusion.
      let h100 := h66 h97
      -- We need to get the left conjuct of h100 based on <expert-advice>.
      let h101 := h100.left
      -- False on the left can always be used.
      apply False.elim h101



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42947635890332069315283007395 : (((p4 → (False ∧ (((p3 → ((p1 ∨ ((((p2 ∧ (p4 → p4)) → p4) ∨ (p2 ∨ p5)) → (p2 → True))) ∧ True)) → False) ∨ False))) ∨ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134334486746663430446920811634 : (((p3 ∧ (p1 ∧ (((p3 ∨ (True → True)) ∧ (p2 ∨ (((((False ∨ p4) ∧ p5) → True) → p3) → p2))) ∨ False))) ∨ False) ∨ ((False ∨ p5) → p5)) := by
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
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219233441142858451672317205845 : ((p1 ∨ ((p1 ∨ p1) ∨ False)) → (((((p2 ∧ False) ∧ p3) → (p2 ∧ (False ∨ True))) → p5) ∨ (p1 ∨ ((((False → p5) ∨ p5) ∧ p4) ∧ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
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
        exact h5
      case inr h6 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h6
    case inr h7 =>
      -- False on the left can always be used.
      apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263254111017086988385692565978 : (True ∧ ((((p3 ∧ True) → True) ∧ (p5 ∨ (p3 → (((p5 ∧ True) ∧ p2) → ((p4 ∨ ((p5 → True) ∧ (p4 ∨ False))) ∧ p1))))) → (p1 ∨ True))) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191232662207583301591979276794 : (((p1 → (True ∧ p1)) → (((p4 ∧ p4) ∨ p5) → p5)) ∨ (False ∨ (True ∨ ((p5 ∧ (p1 ∧ ((False ∨ p2) ∧ (p1 ∧ (p1 ∨ p2))))) ∧ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_153051953656660189634028303918 : ((p3 ∧ ((((((True → p4) → p1) → p3) ∧ ((p1 ∧ p2) ∨ p3)) ∧ (False ∨ ((p4 ∧ p2) ∧ p5))) ∧ p3)) → (True ∧ (p1 ∨ (True → True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
  let h8 := h6.left
  let h9 := h6.right
  -- Disjunctions on the left can always be decomposed.
  cases h9
  case inl h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h13 =>
      -- False on the left can always be used.
      apply False.elim h13
    case inr h14 =>
      -- Conjunctions on the left can always be decomposed.
      let h15 := h14.left
      let h16 := h14.right
      -- Conjunctions on the left can always be decomposed.
      let h17 := h15.left
      let h18 := h15.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h19
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h20 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h21 =>
      -- False on the left can always be used.
      apply False.elim h21
    case inr h22 =>
      -- Conjunctions on the left can always be decomposed.
      let h23 := h22.left
      let h24 := h22.right
      -- Conjunctions on the left can always be decomposed.
      let h25 := h23.left
      let h26 := h23.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h27
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_659224939667840800501312724449 : ((((p4 → (((p3 → ((False ∨ p2) ∧ False)) ∧ ((((p2 → p5) ∨ True) → (p3 → p5)) ∧ p1)) → ((p3 ∧ p5) ∨ True))) ∨ (p5 → False)) ∨ p2) ∧ True) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_679405361090549322552149035580 : ((((p5 → ((True → ((False ∧ (((((p1 ∧ True) ∨ False) ∧ p1) ∨ p1) ∧ p1)) ∧ (True ∨ p2))) ∧ False)) ∨ ((True ∨ (p5 → p1)) → True)) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_149942346894221031758606408959 : ((p3 ∨ (p4 ∧ ((p2 → p1) ∨ ((p5 ∨ False) ∧ ((p1 ∨ ((p1 ∧ p4) → ((p3 → p5) ∧ False))) ∨ p2))))) ∨ (p2 → ((p5 ∧ True) ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159645736285506498813742086137 : ((((p5 ∧ (p1 ∧ ((False ∨ (p4 → p4)) → (False → ((p5 → (p1 ∨ False)) ∧ p4))))) ∨ p2) ∨ p2) → (p3 ∨ (p2 → ((False ∨ p4) ∨ True)))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h11 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h12
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37132188559097330951140384461 : (((((((True → True) ∨ (((((True → ((False → p3) ∧ (p2 → True))) → True) ∧ p5) → True) ∨ False)) → p5) ∨ (p3 ∨ p5)) ∧ False) ∧ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150002068176843180823472335163 : ((p5 ∨ ((False ∧ ((p2 ∨ (True ∧ p1)) → ((p3 ∧ ((p1 ∨ (p2 → p1)) → (p1 → p4))) ∨ False))) ∧ p2)) ∨ ((p4 → (True ∨ p5)) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260527024259555311475678288548 : ((p3 → p1) → (((p3 ∧ p3) ∧ ((True ∨ ((p5 ∧ (((p1 → True) → p1) → True)) ∨ (p5 ∨ False))) → ((True ∨ p3) → (p2 ∨ p4)))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59772474346761367932678096593 : (((p2 ∧ True) → ((p5 ∨ (p2 ∧ (p2 ∧ (True ∧ ((False ∨ (True → (((True ∨ p5) ∨ p3) ∧ p5))) ∨ ((p4 ∨ False) ∨ p4)))))) ∨ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110818119240433520540331739325 : ((((((p1 ∨ True) → (p5 → p1)) → (((((p1 ∨ (p5 ∧ p5)) → True) ∧ p5) → ((p3 → p5) ∨ p5)) → p3)) ∨ p4) ∧ p1) ∨ (True ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137712255418287900768206623205 : ((p1 ∨ (((p1 ∨ ((p1 → p3) → p4)) ∨ True) → (p1 ∨ ((((False ∧ ((p5 ∨ False) → p1)) ∧ p1) ∧ p5) ∧ p5)))) ∨ (p1 ∨ (p5 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46868076346821532133772815199 : ((((p4 ∨ (((p5 ∨ (p5 ∧ p5)) ∧ (False → (True ∨ (p2 ∨ p1)))) ∨ (p5 → (p5 → (p3 → (p2 ∨ p5)))))) ∧ p3) ∨ (False → p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337061877527326350708900064769 : (p1 → (((((p4 → (p2 ∨ (p3 ∧ p4))) ∨ True) → (p2 → ((False → False) → ((p1 ∧ (p5 → (p4 → p1))) ∨ p4)))) → p4) ∨ (p1 ∨ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_686852599574347373041027815823 : ((((p5 ∧ ((False → ((p2 ∧ p1) ∧ p5)) ∨ ((False ∧ p2) ∨ ((True ∨ (p3 ∧ p2)) ∨ True)))) → (((p3 → False) → (p2 ∧ p2)) ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_613004633878452990356516991398 : ((((((((((p5 → ((p5 ∧ p3) ∨ True)) ∨ p1) ∨ p5) ∨ False) ∧ (((p1 ∧ p2) ∨ p5) ∧ (True ∧ p2))) ∧ True) → (p4 ∧ False)) ∨ True) ∨ False) ∧ True) := by
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
theorem thm_5_vars_879349756181119042403220276682 : ((((p3 ∨ ((((p2 ∧ p2) → p1) → (((((p2 ∧ p4) ∧ p3) → False) ∨ (p4 → p4)) → p3)) ∨ (False ∧ (p4 ∧ False)))) ∧ (p1 ∨ p1)) → p3) ∧ True) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h5 =>
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h6 =>
      -- One of the premise coincides with the conclusion.
      exact h4
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h9 =>
        -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
        have h10 : ((p2 ∧ p2) → p1) := by
          -- Implications on the right can always be decomposed.
          intro h11
          -- Conjunctions on the left can always be decomposed.
          let h12 := h11.left
          let h13 := h11.right
          -- One of the premise coincides with the conclusion.
          exact h9
        -- We have shown the premise of h8, we can now drive its conclusion.
        let h14 := h8 h10
        -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
        have h15 : ((((p2 ∧ p4) ∧ p3) → False) ∨ (p4 → p4)) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h16
          -- One of the premise coincides with the conclusion.
          exact h16
        -- We have shown the premise of h14, we can now drive its conclusion.
        let h17 := h14 h15
        -- One of the premise coincides with the conclusion.
        exact h17
      case inr h18 =>
        -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
        have h19 : ((p2 ∧ p2) → p1) := by
          -- Implications on the right can always be decomposed.
          intro h20
          -- Conjunctions on the left can always be decomposed.
          let h21 := h20.left
          let h22 := h20.right
          -- One of the premise coincides with the conclusion.
          exact h18
        -- We have shown the premise of h8, we can now drive its conclusion.
        let h23 := h8 h19
        -- We want to use the implication h23 based on <expert-advice>. So we show its premise.
        have h24 : ((((p2 ∧ p4) ∧ p3) → False) ∨ (p4 → p4)) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h25
          -- One of the premise coincides with the conclusion.
          exact h25
        -- We have shown the premise of h23, we can now drive its conclusion.
        let h26 := h23 h24
        -- One of the premise coincides with the conclusion.
        exact h26
    case inr h27 =>
      -- Conjunctions on the left can always be decomposed.
      let h28 := h27.left
      let h29 := h27.right
      -- False on the left can always be used.
      apply False.elim h28
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_103128787954156923562967089835 : ((((p2 ∧ p4) ∧ (((p4 ∧ (True ∧ p2)) ∧ ((p3 ∨ (((True → (p3 ∨ (p2 → p1))) → p2) ∨ p4)) ∧ p1)) ∧ p5)) ∨ True) ∧ (True ∨ p2)) := by
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
theorem thm_5_vars_114356913995308516833222803785 : (((((((p1 → p3) → (p4 → (((p4 ∨ True) ∧ (p4 ∧ False)) ∧ p1))) ∨ p2) ∨ False) ∧ False) ∨ (((True ∧ False) → p4) ∨ p3)) ∨ (p4 ∧ False)) := by
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
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_141892275442711626246076204174 : (((p3 → False) ∨ ((False → (((((p1 ∨ True) ∨ p3) ∨ p1) ∧ p4) → True)) → (True ∧ ((p5 ∧ p4) ∧ (p1 ∨ p1))))) → (p3 → (p4 ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h4 : p3 := by
      -- One of the premise coincides with the conclusion.
      exact h2
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h5 := h3 h4
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h7 : (False → (((((p1 ∨ True) ∨ p3) ∨ p1) ∧ p4) → True)) := by
      -- Implications on the right can always be decomposed.
      intro h8
      -- Implications on the right can always be decomposed.
      intro h9
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h10 := h6 h7
    -- We need to get the right conjuct of h10 based on <expert-advice>.
    let h11 := h10.right
    -- We need to get the left conjuct of h11 based on <expert-advice>.
    let h12 := h11.left
    -- We need to get the right conjuct of h12 based on <expert-advice>.
    let h13 := h12.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h13



