variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51709289416928093155411876138 : ((((p2 ∧ ((p4 ∧ p1) ∨ ((p1 ∧ True) ∧ p1))) ∧ (((p4 ∧ p2) ∧ False) ∧ True)) ∧ (False ∨ ((False → (p5 → p4)) ∧ (False ∧ p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48700408727763521642344674131 : ((((p2 ∨ (((False → False) ∧ p2) → p5)) ∧ (((False ∨ (False ∨ (p4 → p1))) → p4) ∧ ((p3 ∧ p4) → p4))) ∧ ((p1 → p4) → p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1973062780477025475508737648 : ((p4 ∧ (((p3 ∧ p5) → ((True ∧ ((p5 → p5) ∧ p2)) ∧ p1)) ∨ (((p4 ∨ p1) → p3) ∨ p4))) ∨ ((p5 ∨ False) → (p2 → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- False on the left can always be used.
    apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_670101616908670609449047208381 : (((((True ∧ (True → ((True ∨ p5) ∧ p3))) ∧ ((p4 ∨ (((p1 ∧ p1) ∨ False) ∨ ((False ∨ p2) → p5))) ∧ p3)) ∨ (p2 → (p2 ∨ p4))) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_612143489193065935512353204538 : ((((((((p4 ∧ p5) → ((p2 → False) ∨ (p4 ∨ p3))) → (p4 → p3)) ∧ (((p5 ∧ True) → p3) ∨ (True → p2))) ∧ (False ∧ True)) ∨ True) ∨ False) ∧ True) := by
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
theorem thm_5_vars_115262144428549747060854641924 : ((((p2 ∨ p5) ∨ ((p1 ∨ ((False ∨ p1) → p5)) ∧ False)) ∨ (((p4 → p1) ∨ p3) → ((p2 ∧ False) → ((p2 → False) ∧ False)))) ∨ (True → p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- False on the left can always be used.
  apply False.elim h5
  -- Conjunctions on the left can always be decomposed.
  let h6 := h2.left
  let h7 := h2.right
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_800392752707392610462732929096 : (((p2 → ((p1 ∧ ((p1 ∧ (((p2 ∧ (p2 → ((True → p1) ∨ p4))) ∨ (((False ∨ p2) ∧ (p5 ∨ p2)) ∧ p5)) ∧ p5)) ∧ p2)) ∨ True)) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_247868140168130385849892566607 : ((p1 ∨ p2) ∨ ((True ∨ p5) → ((((False ∨ p4) ∨ p2) → ((p3 → (p3 → p4)) → (p5 ∧ (p5 ∧ p5)))) ∨ (p4 → (True ∨ (p5 → False)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166757701699853897776049770960 : ((p4 → (p1 ∨ (False ∧ ((p3 → ((p5 → (p4 ∨ p5)) → (p5 → (p4 ∨ p3)))) → False)))) ∨ (((True ∧ ((p3 → p2) → p3)) ∨ True) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_153120832971484584818761436169 : ((p4 ∧ (((((p1 → False) ∧ p5) → p3) ∧ p4) ∧ (((p1 → p3) ∨ (((True ∨ p5) ∨ p5) ∨ False)) → False))) → ((p3 ∨ True) → (p3 ∧ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h1.left
    let h5 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h6.left
    let h9 := h6.right
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h1.left
    let h12 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h13 := h12.left
    let h14 := h12.right
    -- Conjunctions on the left can always be decomposed.
    let h15 := h13.left
    let h16 := h13.right
    -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
    have h17 : ((p1 → p3) ∨ (((True ∨ p5) ∨ p5) ∨ False)) := by
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
    -- We have shown the premise of h14, we can now drive its conclusion.
    let h18 := h14 h17
    -- False on the left can always be used.
    apply False.elim h18
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h19 =>
    -- Conjunctions on the left can always be decomposed.
    let h20 := h1.left
    let h21 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h22 := h21.left
    let h23 := h21.right
    -- Conjunctions on the left can always be decomposed.
    let h24 := h22.left
    let h25 := h22.right
    -- We want to use the implication h23 based on <expert-advice>. So we show its premise.
    have h26 : ((p1 → p3) ∨ (((True ∨ p5) ∨ p5) ∨ False)) := by
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
    -- We have shown the premise of h23, we can now drive its conclusion.
    let h27 := h23 h26
    -- False on the left can always be used.
    apply False.elim h27
  case inr h28 =>
    -- Conjunctions on the left can always be decomposed.
    let h29 := h1.left
    let h30 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h31 := h30.left
    let h32 := h30.right
    -- Conjunctions on the left can always be decomposed.
    let h33 := h31.left
    let h34 := h31.right
    -- We want to use the implication h32 based on <expert-advice>. So we show its premise.
    have h35 : ((p1 → p3) ∨ (((True ∨ p5) ∨ p5) ∨ False)) := by
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
    -- We have shown the premise of h32, we can now drive its conclusion.
    let h36 := h32 h35
    -- False on the left can always be used.
    apply False.elim h36



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_962421152082253405428074563347 : ((((True → False) ∧ (p2 ∧ ((((p5 → True) ∨ False) ∧ (p4 ∧ (p3 ∧ p1))) ∧ (((p5 → ((p2 ∧ p2) ∨ (False ∨ True))) ∨ p3) ∧ p3)))) → False) ∧ True) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h9.left
    let h12 := h9.right
    -- Conjunctions on the left can always be decomposed.
    let h13 := h12.left
    let h14 := h12.right
    -- Conjunctions on the left can always be decomposed.
    let h15 := h7.left
    let h16 := h7.right
    -- Disjunctions on the left can always be decomposed.
    cases h15
    case inl h17 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h18 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h19 := h2 h18
      -- False on the left can always be used.
      apply False.elim h19
    case inr h20 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h21 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h22 := h2 h21
      -- False on the left can always be used.
      apply False.elim h22
  case inr h23 =>
    -- False on the left can always be used.
    apply False.elim h23
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_559724094999949222465924488526 : (((p4 ∨ (((((p3 → p4) ∧ (p3 ∧ (p4 ∧ ((p3 ∧ p3) ∨ (p3 → False))))) ∧ (False ∨ p5)) ∧ p1) ∨ (False → ((p5 ∧ p3) ∧ p1)))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112976458166993152034980740179 : (((p1 ∧ (False → (((False → p1) ∨ p3) ∨ ((((p5 ∨ (p1 ∧ (False ∨ p2))) → p2) ∧ p2) → (p4 ∨ (p3 ∧ p1)))))) → p5) ∨ (False → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158009982345398354288273317607 : (((((p3 ∧ (p1 ∨ p4)) ∧ p2) ∨ p3) ∧ ((False ∧ p3) ∨ ((((p5 ∧ p3) → p3) ∧ False) ∧ p4))) ∨ (p3 ∨ ((True ∨ p1) ∨ (True → p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185852534521240949065311998169 : (((((False → p5) → ((p4 ∧ (p1 → False)) ∨ p3)) ∨ p5) ∧ p5) → ((p3 ∧ ((p3 → p3) → (p2 ∧ (p2 ∨ p3)))) → ((p5 ∨ p3) → p2))) := by
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
    let h5 := h2.left
    let h6 := h2.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h1.left
    let h8 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h9 =>
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h10 : (p3 → p3) := by
        -- Implications on the right can always be decomposed.
        intro h11
        -- One of the premise coincides with the conclusion.
        exact h11
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h12 := h6 h10
      -- We need to get the left conjuct of h12 based on <expert-advice>.
      let h13 := h12.left
      -- One of the premise coincides with the conclusion.
      exact h13
    case inr h14 =>
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h15 : (p3 → p3) := by
        -- Implications on the right can always be decomposed.
        intro h16
        -- One of the premise coincides with the conclusion.
        exact h16
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h17 := h6 h15
      -- We need to get the left conjuct of h17 based on <expert-advice>.
      let h18 := h17.left
      -- One of the premise coincides with the conclusion.
      exact h18
  case inr h19 =>
    -- Conjunctions on the left can always be decomposed.
    let h20 := h2.left
    let h21 := h2.right
    -- Conjunctions on the left can always be decomposed.
    let h22 := h1.left
    let h23 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h22
    case inl h24 =>
      -- We want to use the implication h21 based on <expert-advice>. So we show its premise.
      have h25 : (p3 → p3) := by
        -- Implications on the right can always be decomposed.
        intro h26
        -- One of the premise coincides with the conclusion.
        exact h26
      -- We have shown the premise of h21, we can now drive its conclusion.
      let h27 := h21 h25
      -- We need to get the left conjuct of h27 based on <expert-advice>.
      let h28 := h27.left
      -- One of the premise coincides with the conclusion.
      exact h28
    case inr h29 =>
      -- We want to use the implication h21 based on <expert-advice>. So we show its premise.
      have h30 : (p3 → p3) := by
        -- Implications on the right can always be decomposed.
        intro h31
        -- One of the premise coincides with the conclusion.
        exact h31
      -- We have shown the premise of h21, we can now drive its conclusion.
      let h32 := h21 h30
      -- We need to get the left conjuct of h32 based on <expert-advice>.
      let h33 := h32.left
      -- One of the premise coincides with the conclusion.
      exact h33



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187476574120912607354085397193 : ((False ∨ (((((p2 → (p1 → p5)) → True) ∨ True) ∧ p1) ∨ p4)) → (p1 → ((((p5 ∧ True) ∧ p2) ∨ p4) → (False ∨ (True ∨ (p2 → p1)))))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h9 =>
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
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h15 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h16 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h17 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h18 =>
      -- False on the left can always be used.
      apply False.elim h18
    case inr h19 =>
      -- Disjunctions on the left can always be decomposed.
      cases h19
      case inl h20 =>
        -- Conjunctions on the left can always be decomposed.
        let h21 := h20.left
        let h22 := h20.right
        -- Disjunctions on the left can always be decomposed.
        cases h21
        case inl h23 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h24 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h25 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_759796240629274509523476641538 : (((p2 ∧ ((p3 ∧ ((p4 ∧ (p1 ∨ (False ∨ (p3 ∨ p3)))) → False)) → (((False ∧ ((False ∧ True) ∧ (p3 ∨ p3))) ∧ (p4 ∨ p3)) ∨ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_36319944798817514699166973251 : ((p4 → ((((p5 ∨ (p1 ∧ p2)) ∨ p4) ∧ ((((((True ∨ p2) ∧ (p2 → False)) ∧ (True ∧ p2)) → p1) ∨ p4) ∧ True)) ∧ (p2 → True))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68204401225569310190850300688 : ((p3 → ((p1 ∨ ((p1 → ((((False ∧ False) → p3) → (p1 ∨ p3)) ∧ ((p1 ∧ (True ∧ (True ∧ (p4 ∧ False)))) ∨ p5))) ∧ p1)) ∨ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_247540151690204606190440147091 : ((False ∨ p4) ∨ ((((p2 ∨ True) ∧ (False ∨ (((False ∨ ((p5 ∧ p3) ∨ (p5 → p1))) ∨ False) ∨ ((False ∨ False) ∨ p2)))) ∧ p5) ∨ (p2 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_603892605095516382962529677016 : ((((p4 ∨ (p1 → ((((p5 ∨ (p3 → False)) ∧ (((p5 ∧ False) ∨ p5) ∨ ((p1 → p4) → ((p2 ∨ p4) → p3)))) ∧ p1) ∧ True))) ∧ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_703397770308025279004565781538 : ((((p2 ∨ (((p5 ∧ (p3 ∨ (True → False))) ∧ p1) ∨ True)) ∨ ((p1 ∧ (p1 ∨ p2)) ∧ ((False ∨ p2) → ((p2 ∨ p4) ∨ (False → True))))) ∨ False) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322242263639295452037472242812 : (p5 ∨ ((((p3 ∧ (p5 ∨ ((((p1 ∧ p5) ∧ (p1 ∨ ((((True ∧ p2) ∧ p2) ∧ (p4 → False)) → p4))) → p3) ∨ False))) ∨ True) ∨ p4) ∨ p1)) := by
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
theorem thm_5_vars_118680639525214430064762986838 : ((p5 ∨ (((((((p1 → ((p3 ∧ p1) → True)) ∨ p1) → (p3 → (p3 ∨ False))) ∧ (p3 ∧ (p1 → p4))) ∨ p1) → p4) ∧ p2)) ∨ (p2 → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51317300106386979985284780340 : (((p5 ∨ (((((p3 ∧ True) → (((p4 ∨ p5) ∨ (p3 ∨ p5)) → False)) ∨ p4) → p1) ∧ p3)) ∨ ((p2 ∨ p1) → (p2 → (p4 ∧ p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_680803935485563344080065573161 : (((((p4 → (p5 ∧ p4)) ∧ ((p2 → (p2 ∨ (False → p1))) → ((((p5 ∧ p3) → p5) ∨ p1) ∨ p4))) → (True → (p5 ∨ (p4 ∧ True)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_209129905877308310627515734035 : ((p3 ∨ (((p2 ∧ True) ∨ p1) ∧ p5)) → ((p3 ∧ (True → ((p3 ∧ (p3 → p1)) ∧ p5))) → ((False ∨ (p2 ∨ p5)) ∧ (p3 ∨ (p4 → True))))) := by
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
  cases h1
  case inl h5 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h6 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h7 := h4 h6
    -- We need to get the right conjuct of h7 based on <expert-advice>.
    let h8 := h7.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h12.left
      let h14 := h12.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h13
    case inr h15 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h11
  -- Conjunctions on the left can always be decomposed.
  let h16 := h2.left
  let h17 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h18 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h18
  case inr h19 =>
    -- Conjunctions on the left can always be decomposed.
    let h20 := h19.left
    let h21 := h19.right
    -- Disjunctions on the left can always be decomposed.
    cases h20
    case inl h22 =>
      -- Conjunctions on the left can always be decomposed.
      let h23 := h22.left
      let h24 := h22.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h16
    case inr h25 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53754368755828191964130354779 : (((((p1 ∨ (p3 ∨ p1)) ∧ (p1 ∨ (True ∧ p5))) ∧ p1) ∨ (False ∧ (((((p1 ∧ p5) → p2) → p3) ∨ ((p3 → p4) ∨ p2)) ∧ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172241093020705355351630759902 : (((((p5 → p2) ∨ (p4 ∨ False)) → (p2 ∨ p3)) ∧ (False → ((True → p1) → p2))) ∨ (False → ((False ∧ ((p3 → p1) ∨ False)) → (p3 ∧ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h3
  -- Conjunctions on the left can always be decomposed.
  let h5 := h2.left
  let h6 := h2.right
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119462194138355223493109136491 : ((p4 → ((p3 ∨ (True ∧ p3)) → ((((False ∨ ((True → (False ∧ p1)) ∨ (p3 → p2))) → (False ∨ False)) ∧ (p1 ∧ p3)) ∧ False))) ∨ (p4 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244711459342699389184047489005 : ((p1 ∧ True) ∨ (True ∧ (((p3 ∧ p1) → (p4 → (((p3 ∧ (p1 ∨ False)) ∨ (p3 → ((True ∧ True) ∧ (p3 → p5)))) ∧ p3))) → (p5 ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115230863529310490175389652303 : (((((((p2 ∨ (p5 → p3)) → False) → True) → p3) ∨ True) ∨ ((((p5 ∨ False) ∨ (p3 → p3)) ∧ (p5 ∧ p2)) ∧ (p5 ∧ True))) ∨ (p1 → False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46046630374586270650126315298 : ((((p2 → ((((((p4 ∧ p1) → p5) ∨ (p4 ∨ True)) → (p3 ∨ True)) → p1) ∨ ((p3 ∧ p2) ∧ (p5 ∨ p5)))) ∧ p3) ∧ (p2 → p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135137942188837554219541550670 : (((False ∨ ((((p2 ∨ p2) ∨ p1) ∨ ((p3 ∨ True) ∧ (p5 → p1))) ∨ (((p3 ∨ True) ∧ p5) ∧ p5))) ∨ (p5 ∨ p4)) ∨ ((False ∧ p4) → p1)) := by
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
theorem thm_5_vars_200856515483301427350668725415 : ((True ∨ (p1 ∧ (((p3 → p1) ∨ False) ∨ p1))) → (((((p1 ∧ ((p5 ∨ (p2 ∨ False)) ∧ p2)) ∨ (p5 ∧ p1)) ∨ (p4 → p3)) ∨ True) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h4
      case inr h8 =>
        -- False on the left can always be used.
        apply False.elim h8
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231151772981312034589628242475 : (((p2 ∨ True) ∨ False) → (((p4 ∨ p4) ∨ p2) → ((((p2 ∧ p2) ∧ p4) → False) → (p3 ∨ (True ∨ (True ∧ (((p5 → False) ∨ True) → p3))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h6 =>
        -- Disjunctions on the left can always be decomposed.
        cases h6
        case inl h7 =>
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
      case inr h9 =>
        -- False on the left can always be used.
        apply False.elim h9
    case inr h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h11 =>
        -- Disjunctions on the left can always be decomposed.
        cases h11
        case inl h12 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h13 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h14 =>
        -- False on the left can always be used.
        apply False.elim h14
  case inr h15 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h16 =>
      -- Disjunctions on the left can always be decomposed.
      cases h16
      case inl h17 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h18 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h19 =>
      -- False on the left can always be used.
      apply False.elim h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_344122503452339295421313025179 : (p2 → (False ∨ ((p3 → ((False ∨ (((False ∨ True) → (False → (True → p3))) ∧ (p1 ∧ p1))) ∧ (False ∧ p3))) ∨ (False ∨ (p1 → (True → p1)))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63368671217507503005639411854 : ((p5 ∧ (p4 ∧ (((p5 ∨ ((p3 ∨ p5) ∧ p3)) → (p1 → False)) ∧ ((True ∧ (((True ∧ p2) ∨ (False ∧ True)) ∧ p3)) ∨ (True ∨ True))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_744196649477930659218701608591 : ((((p1 ∧ p1) → (p1 ∧ ((((p2 ∨ (False ∨ (p3 ∧ True))) ∨ False) ∨ (p1 ∧ p5)) ∨ ((p3 ∨ p1) ∨ (((p4 → p5) → p4) → p5))))) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40526483168872943943189099598 : ((((False ∨ ((p5 ∨ (((True ∨ (p3 ∧ (False ∧ p5))) ∨ (p4 → ((p1 ∨ True) ∨ p1))) ∧ p1)) → ((p5 ∧ p4) ∨ True))) ∨ False) ∨ p1) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h8 =>
        -- Conjunctions on the left can always be decomposed.
        let h9 := h8.left
        let h10 := h8.right
        -- Conjunctions on the left can always be decomposed.
        let h11 := h10.left
        let h12 := h10.right
        -- False on the left can always be used.
        apply False.elim h11
    case inr h13 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114421949071058675703603414979 : ((((p3 → p2) → (((((p1 ∧ True) → ((p4 → p1) → (p2 → False))) → False) ∧ p3) ∧ True)) ∨ (p2 ∧ ((p5 → p2) ∨ False))) ∨ (p3 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_665725851392891662750207907160 : (((((p1 → (((((p1 ∨ p1) → p5) ∨ ((p5 ∧ p3) ∨ p4)) → p4) ∧ ((p2 ∨ p1) ∧ (p1 → p2)))) ∨ p1) ∧ (False ∧ (p1 → p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118812457686006746888757859552 : ((True → ((((((p1 ∨ p5) ∨ ((p3 ∨ p2) → p2)) ∨ (p3 ∨ p2)) → p1) ∧ ((p1 → p1) ∨ ((p5 ∨ False) → p2))) ∨ p1)) ∨ (True ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_154238835273559935139809082069 : ((((p1 ∧ ((p5 ∨ p4) ∨ (p1 ∨ p1))) ∧ ((p2 ∧ p3) ∨ (((True → True) ∧ True) ∨ p3))) ∨ True) ∧ ((True ∨ (p2 → (False → p3))) ∨ p1)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_113787988656541565160513960577 : ((((True ∨ True) ∧ (((p5 → p5) → p4) ∧ ((p3 ∨ p1) ∨ ((False ∧ p1) ∨ ((True → False) ∧ (p5 ∨ p2)))))) → (p3 ∧ p4)) ∨ (p3 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_139810664187670521258988919655 : (((p5 ∨ ((p4 ∧ (p4 ∧ ((True ∨ False) → ((p1 → p4) ∧ (p5 → (p5 ∧ (p4 ∨ p1))))))) → (p2 ∧ p4))) → p3) → ((p2 ∧ p4) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55742311231295027745045318902 : ((((p1 ∧ (p2 → False)) → True) ∧ ((False → (False ∨ p4)) → (((p2 ∨ ((p1 ∨ p4) ∧ p3)) ∧ ((p4 ∧ p2) ∨ p1)) ∨ (True ∨ p5)))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60751627782617631269386628260 : ((True ∧ ((p4 ∧ (True ∨ p3)) → ((((p5 ∧ p1) ∨ ((((p3 ∨ p1) ∨ p3) → p3) ∧ (p1 ∧ (p2 ∧ p3)))) ∧ p3) ∧ (p1 ∧ p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308629404882733709539320865904 : (p2 ∨ (((p3 ∨ p4) → (((p4 ∨ p1) → p1) → ((p4 ∧ ((p2 ∧ True) ∨ (p2 ∨ (p1 ∨ (p3 ∨ (p4 ∧ p3)))))) ∧ (p2 ∧ False)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_106629007863336054297120449460 : ((((p2 ∨ (p3 → (p5 ∨ True))) ∧ True) ∧ (p1 → (p1 ∧ (((((p2 → False) ∨ p5) → p3) ∨ (False ∧ p3)) ∨ (p3 → p3))))) ∧ (p5 → True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro
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
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299158088148541223365768449826 : (False ∨ (((p2 → ((False ∧ p3) ∨ ((p5 ∨ (p1 → True)) ∧ ((p2 ∧ p2) → ((((p1 ∨ p4) → p2) ∧ (p4 ∧ p1)) ∧ p4))))) ∨ True) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351898694617977147681067565174 : (p4 → (((((p2 → p3) → (p1 ∧ (p5 ∧ p2))) ∨ p1) ∨ p4) ∨ ((((p5 ∧ (p3 ∨ False)) ∧ p1) ∧ (p1 → ((p2 → True) ∧ p1))) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117213396160063983389230631045 : ((True ∧ ((p2 ∨ (False ∧ (True → p4))) → (True ∧ ((p5 ∨ (p4 ∧ p4)) ∨ (p3 ∧ ((p3 ∨ ((False → False) → True)) → False)))))) ∨ (p2 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53098828359332049670804383536 : (((p4 ∨ ((p2 ∨ (False ∨ p4)) ∨ (p4 → (p1 ∨ (p5 ∧ False))))) ∧ ((((True → (((p1 → p4) → False) ∧ p5)) ∨ p3) → p4) ∧ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_34980446438956317270399912981 : ((p1 → (((p4 ∧ (p4 ∧ (((True → p5) ∨ p1) ∧ True))) ∨ ((True → p5) → (((p1 ∧ False) ∨ (p4 ∧ p3)) ∨ (p4 → p3)))) ∨ True)) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53672125030597816314837787870 : ((((True ∨ p1) → (((False ∧ p3) ∨ True) → (p5 ∨ True))) ∧ ((p1 → False) ∨ ((((p3 ∨ p5) ∨ (p5 → (p4 ∨ p5))) ∨ p2) ∨ p3))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- False on the left can always be used.
    apply False.elim h4
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h9
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57695253559858192699513376781 : ((((True ∧ p5) → p5) → (p3 ∧ (((False ∨ (p5 ∨ p2)) ∨ ((p2 ∨ (p3 → p4)) ∨ (p3 → (p1 ∨ p5)))) ∧ (True ∨ (False ∧ False))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_923713167478340432212279049230 : (((((p5 ∨ (p4 → False)) ∧ ((p1 → (p3 → p4)) ∨ (False ∧ p5))) ∧ (True ∧ ((p1 ∧ p2) ∧ (p3 ∧ ((p2 ∨ p4) ∨ (p4 → p5)))))) → p4) ∧ True) := by
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
  cases h4
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h3.left
      let h9 := h3.right
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- Conjunctions on the left can always be decomposed.
      let h12 := h10.left
      let h13 := h10.right
      -- Conjunctions on the left can always be decomposed.
      let h14 := h11.left
      let h15 := h11.right
      -- Disjunctions on the left can always be decomposed.
      cases h15
      case inl h16 =>
        -- Disjunctions on the left can always be decomposed.
        cases h16
        case inl h17 =>
          -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
          have h18 : p1 := by
            -- One of the premise coincides with the conclusion.
            exact h12
          -- We have shown the premise of h7, we can now drive its conclusion.
          let h19 := h7 h18
          -- We want to use the implication h19 based on <expert-advice>. So we show its premise.
          have h20 : p3 := by
            -- One of the premise coincides with the conclusion.
            exact h14
          -- We have shown the premise of h19, we can now drive its conclusion.
          let h21 := h19 h20
          -- One of the premise coincides with the conclusion.
          exact h21
        case inr h22 =>
          -- One of the premise coincides with the conclusion.
          exact h22
      case inr h23 =>
        -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
        have h24 : p1 := by
          -- One of the premise coincides with the conclusion.
          exact h12
        -- We have shown the premise of h7, we can now drive its conclusion.
        let h25 := h7 h24
        -- We want to use the implication h25 based on <expert-advice>. So we show its premise.
        have h26 : p3 := by
          -- One of the premise coincides with the conclusion.
          exact h14
        -- We have shown the premise of h25, we can now drive its conclusion.
        let h27 := h25 h26
        -- One of the premise coincides with the conclusion.
        exact h27
    case inr h28 =>
      -- Conjunctions on the left can always be decomposed.
      let h29 := h28.left
      let h30 := h28.right
      -- False on the left can always be used.
      apply False.elim h29
  case inr h31 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h32 =>
      -- Conjunctions on the left can always be decomposed.
      let h33 := h3.left
      let h34 := h3.right
      -- Conjunctions on the left can always be decomposed.
      let h35 := h34.left
      let h36 := h34.right
      -- Conjunctions on the left can always be decomposed.
      let h37 := h35.left
      let h38 := h35.right
      -- Conjunctions on the left can always be decomposed.
      let h39 := h36.left
      let h40 := h36.right
      -- Disjunctions on the left can always be decomposed.
      cases h40
      case inl h41 =>
        -- Disjunctions on the left can always be decomposed.
        cases h41
        case inl h42 =>
          -- We want to use the implication h32 based on <expert-advice>. So we show its premise.
          have h43 : p1 := by
            -- One of the premise coincides with the conclusion.
            exact h37
          -- We have shown the premise of h32, we can now drive its conclusion.
          let h44 := h32 h43
          -- We want to use the implication h44 based on <expert-advice>. So we show its premise.
          have h45 : p3 := by
            -- One of the premise coincides with the conclusion.
            exact h39
          -- We have shown the premise of h44, we can now drive its conclusion.
          let h46 := h44 h45
          -- One of the premise coincides with the conclusion.
          exact h46
        case inr h47 =>
          -- One of the premise coincides with the conclusion.
          exact h47
      case inr h48 =>
        -- We want to use the implication h32 based on <expert-advice>. So we show its premise.
        have h49 : p1 := by
          -- One of the premise coincides with the conclusion.
          exact h37
        -- We have shown the premise of h32, we can now drive its conclusion.
        let h50 := h32 h49
        -- We want to use the implication h50 based on <expert-advice>. So we show its premise.
        have h51 : p3 := by
          -- One of the premise coincides with the conclusion.
          exact h39
        -- We have shown the premise of h50, we can now drive its conclusion.
        let h52 := h50 h51
        -- One of the premise coincides with the conclusion.
        exact h52
    case inr h53 =>
      -- Conjunctions on the left can always be decomposed.
      let h54 := h53.left
      let h55 := h53.right
      -- False on the left can always be used.
      apply False.elim h54
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_641746005295455576587406435555 : (((((p3 ∨ p2) → ((p3 ∧ False) → (((p2 → p5) → False) ∧ (p5 ∧ ((p4 ∧ ((((False ∧ True) ∧ False) → p4) → p3)) → p4))))) → p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157046695123385430171727388504 : (((p1 ∧ ((((p4 ∨ (p2 → p3)) ∨ (p5 → (p5 ∧ (p3 ∧ p4)))) ∨ (p3 ∨ p2)) ∨ False)) ∨ True) ∨ ((p2 ∨ (p1 → p4)) ∨ (p5 ∨ p5))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180809921496284627392910034947 : ((((True ∧ False) → p5) ∧ (p2 ∨ (((p5 → p1) ∨ (p4 ∧ False)) ∧ p4))) → (((p1 ∨ p2) ∧ (p4 → ((p1 ∧ True) → True))) ∨ (p3 → p3))) := by
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
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- One of the premise coincides with the conclusion.
      exact h10
    case inr h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- False on the left can always be used.
      apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159424335931252916592688592679 : ((((((p2 ∧ (p3 ∨ (p2 ∧ (True ∨ (p1 ∧ p2))))) → True) ∨ (False ∧ False)) ∨ (p5 ∧ p5)) ∧ p5) → ((False ∨ p2) ∨ ((p2 ∨ False) ∨ True))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- False on the left can always be used.
      apply False.elim h7
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_554391559546167236672524693 : (((True ∧ ((p2 ∧ (((False → ((p2 ∧ (p4 ∨ ((p4 ∨ p1) → p3))) ∧ p5)) ∧ (True → p4)) → (p1 ∧ False))) ∧ True)) ∨ True) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_201206711722041742912237135189 : ((p2 → (((p3 ∧ False) ∧ (p5 → p1)) ∧ True)) → ((p4 ∧ p4) → (((p3 ∧ ((((p2 → p1) ∨ p2) → p1) ∨ True)) ∨ (p3 ∨ p1)) ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171801447361112220321610243282 : (((((p1 ∧ p4) → (((True ∧ False) ∧ p3) ∧ p3)) ∨ (p2 → (True ∨ False))) → p4) ∨ (p2 ∨ (((((p2 → True) ∨ p4) ∨ True) → p4) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_26889558825627106375520685288 : (((p2 ∨ p4) ∨ ((((p2 ∨ ((p4 ∨ True) ∨ (p3 ∨ p1))) ∨ True) → (True → (p2 ∨ (False → False)))) ∨ ((False ∧ True) → (p4 ∧ p5)))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  apply False.elim h2
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- False on the left can always be used.
  apply False.elim h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147659622124125788567916629912 : (((((((p3 ∧ (False ∨ p3)) ∨ True) ∧ (((p1 ∨ p5) → (False ∨ False)) ∨ p1)) → p2) ∨ (True ∨ p2)) → p4) ∨ ((True ∨ (p2 → p4)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324260077469418256540338882367 : (p5 ∨ ((((p5 ∨ (p1 ∨ p3)) ∧ p3) ∧ (False ∨ False)) ∨ (((True ∧ (True → True)) → True) ∨ (((p1 ∧ True) ∨ p1) ∨ (p3 → (p1 → p1)))))) := by
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
theorem thm_5_vars_113918482076855141706301567538 : (((((((p5 ∧ p2) → (True ∧ (p2 ∨ False))) ∧ ((p2 → p2) ∧ p5)) ∨ True) ∧ (p1 → (p4 ∧ False))) ∧ ((p2 ∨ p3) ∧ False)) ∨ (p4 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_92725995104534518149591732127 : (((p3 → True) → (((p5 → (True → (False ∨ (p3 → p5)))) ∧ (True ∧ p3)) ∧ (p2 ∧ ((p4 → (p4 ∧ False)) ∨ ((p4 ∧ p4) ∧ p3))))) → p3) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p3 → True) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186430366697684641863192447882 : (((p1 → (((p4 ∨ p4) → (p3 → (p5 → p5))) ∨ p3)) → True) → ((p1 → ((p3 → p3) → (p4 ∧ (p4 ∨ (p2 ∧ p1))))) ∨ (False → p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44551254681617955205931057243 : (((((((p4 ∨ p2) → (p4 → p2)) ∨ p2) ∨ p2) ∧ (((p2 ∧ p2) ∨ (True ∨ (p2 ∧ (p1 ∨ ((p2 ∧ p1) ∧ p1))))) ∨ p2)) → p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310946536283508122006400509783 : (p2 ∨ ((p1 ∨ True) ∧ (((p4 → (p3 ∧ ((((True → p3) → False) ∨ (p4 → p4)) → False))) ∨ True) ∨ (p3 ∧ ((p3 ∧ (p4 → p2)) ∨ True))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_686891839491444919284095406844 : ((((False ∨ ((((p1 ∨ (p3 ∨ (p4 ∨ ((p3 ∧ p3) ∨ p4)))) ∨ (p4 ∧ p2)) ∧ p1) ∨ p2)) → (((p1 → p2) ∧ True) ∨ (True ∨ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_124039953004717286262605065099 : ((((((p5 ∧ p3) → True) ∧ (p1 ∧ (p2 ∧ (True ∧ p3)))) → True) → (p4 ∧ ((((p2 ∨ (p3 ∧ p5)) → False) ∨ p1) ∧ p3))) → (False ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((((p5 ∧ p3) → True) ∧ (p1 ∧ (p2 ∧ (True ∧ p3)))) → True) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_326906916949404972051256227535 : (True → (((((p4 → (((p1 ∨ True) ∨ ((p3 ∧ True) ∨ (p4 → (p3 ∨ (False → p2))))) ∨ p3)) ∨ ((p4 → p4) ∧ p2)) → p4) → False) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_612762197040644864271572477453 : (((((((p3 ∨ p2) ∨ p5) ∧ (((((False ∧ p3) → p2) ∧ False) → p4) → ((p1 ∧ (p1 ∧ p4)) ∧ (False ∧ False)))) ∨ (p1 ∨ True)) ∨ False) ∨ p2) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246498132758015196230337915326 : ((p5 ∧ p1) ∨ ((((False ∨ (p1 → False)) ∨ False) → (p1 ∨ ((((((p2 ∨ True) ∨ p2) ∨ p4) → p5) ∨ p3) ∨ (p2 ∨ (True ∨ True))))) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_33802563819022649215159148288 : ((p5 ∨ (((((p3 → (True ∧ (((p2 ∨ (False ∧ False)) ∧ ((p5 ∧ p4) → p4)) ∨ p2))) ∨ p3) → p1) ∧ True) ∨ ((False → False) → True))) ∧ True) := by
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
theorem thm_5_vars_593086087625209590111625852920 : (((((((p4 ∨ (((p3 ∨ p3) ∧ p5) ∧ ((p3 → ((p3 ∨ p1) ∧ p4)) → p4))) → p4) ∧ (True → True)) ∨ (p4 ∧ (p2 → p2))) ∧ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_686305791078443414066406651818 : (((((((p3 → p3) → (p3 ∨ p1)) ∨ p1) ∧ (p5 → (p4 ∨ ((p2 ∧ (p1 → False)) ∧ False)))) → ((p5 → ((p2 → p3) ∨ p5)) ∨ False)) ∨ p2) ∧ True) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h7
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156715398401551972468850406903 : ((((p3 ∧ (p3 ∨ ((p1 ∨ p2) → (p3 ∧ p2)))) ∧ ((p2 ∧ p2) → (p2 ∨ (p4 → p5)))) ∧ p5) ∨ (((True ∨ p4) ∧ p2) → (p3 ∨ True))) := by
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
theorem thm_5_vars_165544545101476882396879606186 : ((((p3 → (p5 → ((p5 ∨ p1) → False))) → p1) ∧ (((p3 ∧ p1) ∨ (True → p3)) → p1)) ∨ ((p4 → ((p4 ∧ p1) → p1)) ∧ (True ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h4
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_610536643344858036349272498356 : ((((((((False ∨ p4) ∧ ((p5 ∧ False) ∨ (False → (p4 ∨ p2)))) ∨ (((p1 ∨ p1) ∧ p5) ∨ (p5 → p2))) ∧ (p5 → p3)) → False) ∨ True) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_256715062605644326336037482854 : ((p1 ∨ p1) → ((p4 ∨ (((p3 → (p3 → (p5 → p2))) ∨ ((True → (p5 ∧ p5)) → (p1 ∨ p5))) → (p3 ∧ True))) ∨ ((p3 → p3) ∨ False))) := by
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
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_864741250264589796999750591980 : ((((((p1 ∧ True) → (p2 ∧ (p3 ∧ (True ∧ False)))) → ((False ∨ (((((False ∨ p1) ∨ (p1 → p5)) → False) ∨ p2) ∨ True)) ∨ p4)) → False) → p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p1 ∧ True) → (p2 ∧ (p3 ∧ (True ∧ False)))) → ((False ∨ (((((False ∨ p1) ∨ (p1 → p5)) → False) ∨ p2) ∨ True)) ∨ p4)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- False on the left can always be used.
  apply False.elim h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_254860652701965934415742035448 : ((p3 ∧ p5) → (p1 ∨ ((((p1 ∨ p4) ∨ ((p4 ∨ (False → p4)) ∧ p4)) → (p2 ∧ True)) → ((p5 → ((True ∧ p5) ∧ (True → p2))) ∨ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42893133567188437961969518308 : (((p3 → (((p3 ∧ p2) ∨ ((((p2 ∧ p2) → ((p4 → True) → p2)) → (((False ∨ p2) ∨ p3) ∧ p4)) → True)) → (False ∨ False))) ∨ True) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337071481459195147945961538769 : (p1 → ((((p3 → (((p2 → p5) ∧ False) → (p2 → (p2 ∧ p3)))) → (p3 ∧ ((p3 ∧ (p3 ∨ p5)) → p4))) ∨ (p5 ∨ True)) ∨ (p5 ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214819151938986521210334040780 : (((p3 ∨ p5) ∨ (p1 ∨ p1)) ∨ ((p3 → (p1 ∨ (p4 → (((p5 ∨ p1) → p2) ∨ ((p5 → p2) → (p4 → (p3 ∧ p4))))))) ∨ (p1 ∨ p5))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319169763756526260193071916607 : (p4 ∨ ((((p4 → ((p2 ∨ False) ∨ (p5 ∧ (p2 ∧ p5)))) → False) ∧ ((p3 ∨ True) ∨ (p5 → p3))) ∨ ((False ∨ (p2 ∧ (p3 ∨ p4))) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158793207722851156137619614748 : ((p5 ∧ ((p5 ∨ ((p5 ∧ (p4 ∨ True)) → ((p4 ∨ (p2 ∨ p3)) → p4))) ∨ ((False ∨ p1) ∨ False))) ∨ ((True ∧ (p4 ∨ True)) ∧ (p3 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304698982851962186696930000552 : (p1 ∨ ((((p2 ∧ ((p2 ∨ (((p2 ∧ p2) → p1) ∧ (p4 → (p3 ∨ p3)))) → (p5 ∨ p4))) → ((p2 ∧ p2) ∨ True)) → False) ∨ (p5 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_775717491180287570282597545988 : (((False ∨ (p3 ∨ ((((p5 ∨ p4) ∨ p5) ∨ (((p5 ∧ (True ∧ p5)) ∨ p2) ∧ (p3 ∨ (((p3 → p4) → (p5 ∨ p4)) ∨ p3)))) ∨ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_875974891304213481219663832524 : ((((((((True ∨ (((p5 ∨ p3) → p3) → False)) ∨ p5) ∧ ((p3 ∧ p4) ∨ (p5 ∨ p4))) ∨ (False ∨ p5)) ∧ (p5 → False)) ∧ (p5 → p3)) → p4) ∧ True) := by
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
  cases h4
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Disjunctions on the left can always be decomposed.
        cases h8
        case inl h11 =>
          -- Conjunctions on the left can always be decomposed.
          let h12 := h11.left
          let h13 := h11.right
          -- One of the premise coincides with the conclusion.
          exact h13
        case inr h14 =>
          -- Disjunctions on the left can always be decomposed.
          cases h14
          case inl h15 =>
            -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
            have h16 : p5 := by
              -- One of the premise coincides with the conclusion.
              exact h15
            -- We have shown the premise of h5, we can now drive its conclusion.
            let h17 := h5 h16
            -- False on the left can always be used.
            apply False.elim h17
          case inr h18 =>
            -- One of the premise coincides with the conclusion.
            exact h18
      case inr h19 =>
        -- Disjunctions on the left can always be decomposed.
        cases h8
        case inl h20 =>
          -- Conjunctions on the left can always be decomposed.
          let h21 := h20.left
          let h22 := h20.right
          -- One of the premise coincides with the conclusion.
          exact h22
        case inr h23 =>
          -- Disjunctions on the left can always be decomposed.
          cases h23
          case inl h24 =>
            -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
            have h25 : p5 := by
              -- One of the premise coincides with the conclusion.
              exact h24
            -- We have shown the premise of h5, we can now drive its conclusion.
            let h26 := h5 h25
            -- False on the left can always be used.
            apply False.elim h26
          case inr h27 =>
            -- One of the premise coincides with the conclusion.
            exact h27
    case inr h28 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h29 =>
        -- Conjunctions on the left can always be decomposed.
        let h30 := h29.left
        let h31 := h29.right
        -- One of the premise coincides with the conclusion.
        exact h31
      case inr h32 =>
        -- Disjunctions on the left can always be decomposed.
        cases h32
        case inl h33 =>
          -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
          have h34 : p5 := by
            -- One of the premise coincides with the conclusion.
            exact h33
          -- We have shown the premise of h5, we can now drive its conclusion.
          let h35 := h5 h34
          -- False on the left can always be used.
          apply False.elim h35
        case inr h36 =>
          -- One of the premise coincides with the conclusion.
          exact h36
  case inr h37 =>
    -- Disjunctions on the left can always be decomposed.
    cases h37
    case inl h38 =>
      -- False on the left can always be used.
      apply False.elim h38
    case inr h39 =>
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h40 : p5 := by
        -- One of the premise coincides with the conclusion.
        exact h39
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h41 := h5 h40
      -- False on the left can always be used.
      apply False.elim h41
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_353674949364673977918091344940 : (p4 → (p5 ∨ (((p3 → ((((p5 → ((p1 ∧ True) ∨ p4)) ∧ p5) ∧ p2) → p3)) ∧ p2) ∨ (p4 ∧ (p5 ∨ (p5 ∨ ((p1 ∨ p3) ∨ p4))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_732195584719289755444098320756 : ((((True ∧ p4) ∧ (p2 ∨ ((p2 ∧ True) ∨ (p5 ∨ ((True ∧ ((True → p2) → p4)) ∧ ((p5 → (p5 ∨ ((p1 ∨ p3) ∨ True))) ∨ True)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149954706153030330959595452474 : ((p4 ∨ (((True → (True ∨ p5)) ∧ (p2 → (((((p5 → False) ∨ p3) ∧ p2) ∨ p1) → (False ∨ p4)))) ∧ p5)) ∨ ((p5 ∨ True) → (p5 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_650780096717516140894288202489 : (((((p1 → ((p5 → (p3 → p1)) ∧ (p5 → p5))) ∧ ((False → False) → (((p1 → p5) ∨ ((p5 ∧ p1) ∧ p5)) ∨ p3))) ∧ (p1 → p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315281927948198374674512113757 : (p3 ∨ ((((p1 ∧ False) → p3) ∨ p4) → (((((p3 → ((p5 ∨ p4) → True)) → p3) ∨ p1) ∨ (p1 ∨ (True ∧ (p5 → p2)))) ∨ (False → False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- False on the left can always be used.
    apply False.elim h5



